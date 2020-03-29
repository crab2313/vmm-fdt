use nom::bytes::complete::{tag, take, take_while};
use nom::combinator::{map_res, verify};
use nom::multi::{count, many0};
use nom::number::complete::{be_u32, be_u64};
use nom::sequence::{terminated, tuple};
use nom::IResult;

use std::collections::HashMap;

use crate::{DeviceTree, Error, FdtToken, NodeHandle, ReserveEntry, Result, Value, Values};

#[derive(Default, Debug)]
struct FdtHeader {
    totalsize: u32,
    off_dt_struct: u32,
    off_dt_strings: u32,
    off_mem_rsvmap: u32,
    // TODO: check version
    boot_cpuid_phys: u32,
    size_dt_strings: u32,
    size_dt_struct: u32,
}

fn magic(i: &[u8]) -> IResult<&[u8], &[u8]> {
    tag(u32::to_be_bytes(0xd00dfeed))(i)
}

fn header(i: &[u8]) -> IResult<&[u8], FdtHeader> {
    let mut header = FdtHeader::default();
    let (i, _) = magic(i)?;
    let (i, fields) = count(be_u32, 9)(i)?;

    header.totalsize = fields[0];
    header.off_dt_struct = fields[1];
    header.off_dt_strings = fields[2];
    header.off_mem_rsvmap = fields[3];
    header.boot_cpuid_phys = fields[6];
    header.size_dt_strings = fields[7];
    header.size_dt_struct = fields[8];

    Ok((i, header))
}

fn reserve_block(i: &[u8]) -> IResult<&[u8], Vec<ReserveEntry>> {
    let to_entry = |(address, size)| -> Result<ReserveEntry> { Ok(ReserveEntry { address, size }) };
    let entry = map_res(tuple((be_u64, be_u64)), to_entry);

    many0(verify(entry, |e| !(e.address == 0 && e.size == 0)))(i)
}

fn null_terminated(i: &[u8]) -> IResult<&[u8], &[u8]> {
    terminated(take_while(|b| b != 0), tag([0]))(i)
}

fn strings_block(i: &[u8]) -> IResult<&[u8], HashMap<u32, &[u8]>> {
    let (re, strs) = many0(null_terminated)(i)?;
    let strings: Vec<(usize, &[u8])> = strs
        .into_iter()
        .map(|s| (s.as_ptr() as usize - i.as_ptr() as usize, s))
        .collect();

    let mut table = HashMap::new();
    for (offset, string) in strings {
        table.insert(offset as u32, string);
    }
    Ok((re, table))
}

macro_rules! token {
    ($i:ident, $x:expr) => {
        fn $i(i: &[u8]) -> IResult<&[u8], &[u8]> {
            tag(u32::to_be_bytes($x as u32))(i)
        }
    };
}

token!(begin_node, FdtToken::BeginNode);
token!(end_node, FdtToken::EndNode);
token!(nop, FdtToken::Nop);
token!(prop, FdtToken::Prop);
token!(end, FdtToken::End);

#[derive(Debug)]
struct Property<'a> {
    off: u32,
    value: &'a [u8],
}

#[derive(Debug)]
struct Node<'a> {
    name: &'a [u8],
    props: Vec<Property<'a>>,
    childs: Vec<Node<'a>>,
}

fn align_to<'a>(i: &'a [u8], start: &'a [u8], align: usize) -> &'a [u8] {
    let off = i.as_ptr() as usize - start.as_ptr() as usize;
    let to_aligned = (!off + 1) & (align - 1);
    i.split_at(to_aligned).1
}

fn property(start: &[u8]) -> IResult<&[u8], Property> {
    // NOTE: we are assuming the offset from the start of dtb header to `start` is
    // aligned to 4 bytes
    let (i, (_, _, len, off)) = tuple((many0(nop), prop, be_u32, be_u32))(start)?;
    let (i, value) = take(len)(i)?;
    let i = align_to(i, start, 4);

    Ok((i, Property { off, value }))
}

fn node(start: &[u8]) -> IResult<&[u8], Node> {
    // NOTE: we are assuming the offset from the start of dtb header to `start` is
    // aligned to 4 bytes
    let (i, (_, _, name)) = tuple((many0(nop), begin_node, null_terminated))(start)?;
    let i = align_to(i, start, 4);

    let (i, (props, childs, _, _)) =
        tuple((many0(property), many0(node), many0(nop), end_node))(i)?;

    Ok((
        i,
        Node {
            name,
            props,
            childs,
        },
    ))
}

fn build_tree(
    node: Node,
    parent: Option<NodeHandle>,
    tree: &mut DeviceTree,
    strings: &HashMap<u32, &[u8]>,
) -> Result<()> {
    let tree_node: NodeHandle = match parent {
        Some(p) => tree.alloc_node(
            p,
            std::str::from_utf8(node.name).map_err(|_| Error::InvalidNodeName)?,
        )?,
        None => tree.root(), // It's the root.
    };

    for prop in node.props {
        let values = Values(vec![Value::Bytes(prop.value.to_vec())]);
        tree.set_property(
            tree_node,
            std::str::from_utf8(strings.get(&prop.off).ok_or(Error::InvalidStringTable)?)
                .map_err(|_| Error::InvalidPropertyName)?,
            values,
        )?;
    }

    for child in node.childs {
        build_tree(child, Some(tree_node), tree, strings)?;
    }

    Ok(())
}

fn structure_block(start: &[u8]) -> IResult<&[u8], Node> {
    let (i, nodes) = node(start)?;
    let i = align_to(i, start, 4);
    let (i, _) = end(i)?;
    Ok((i, nodes))
}

fn parse(dtb: &[u8]) -> IResult<&[u8], (FdtHeader, Vec<ReserveEntry>, HashMap<u32, &[u8]>, Node)> {
    let (_, header) = header(dtb)?;

    // calculate the start and end of memory reservation block
    let reserve_start = header.off_mem_rsvmap as usize;
    let reserve_end = header.off_dt_struct as usize;
    let (_, reserved) = reserve_block(&dtb[reserve_start..reserve_end])?;

    // parse strings block
    let strings_start = header.off_dt_strings as usize;
    let strings_end = (header.off_dt_strings + header.size_dt_strings) as usize;
    let (_, strings) = strings_block(&dtb[strings_start..strings_end])?;

    // parse the structure block
    let struct_start = header.off_dt_struct as usize;
    let struct_end = (header.off_dt_struct + header.size_dt_struct) as usize;
    let (i, nodes) = structure_block(&dtb[struct_start..struct_end])?;

    Ok((i, (header, reserved, strings, nodes)))
}

pub(crate) fn parse_dtb(dtb: &[u8]) -> Result<DeviceTree> {
    let (_, parsed) = parse(dtb).map_err(|_| Error::InvalidDtbFormat)?;
    let (header, reserved, strings, nodes) = parsed;

    // Then build the DeviceTree
    let mut tree = DeviceTree::new();
    tree.set_boot_cpuid(header.boot_cpuid_phys);
    tree.reserved = reserved;
    build_tree(nodes, None, &mut tree, &strings)?;

    Ok(tree)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn magic_parse() {
        assert!(magic(&[0xd0, 0x0d, 0xfe, 0xed]).is_ok());
    }

    #[test]
    fn dtb_parse() {
        let dtb = &include_bytes!("test.dtb")[..];
        parse(dtb).unwrap();
    }
}
