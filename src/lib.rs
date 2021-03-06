#![deny(missing_docs)]

//! A simple flattened device tree (FDT) generator. See the `examples` directory
//! in this crate for a full list of examples.

use generational_arena::{Arena, Index};

use std::convert::{TryFrom, TryInto};
use std::io::prelude::*;
use std::io::SeekFrom;

mod parser;

/// Core error type used in this crate.
#[derive(Debug)]
pub enum Error {
    /// The node is not exist in the device tree.
    NoSuchNode,
    /// The property is not exist in the device tree node.
    NoSuchProperty,
    /// The identification is used by another node already.
    IdentConflict,
    /// The value of the specified property is invalid.
    InvalidProperty,
    /// The size of `Values` do not meet the requirement.
    SizeMismatch,
    /// There is a `Cell::Ref` exist in the `Values`.
    RefExist,
    /// `#address-cells` property of a node is invalid.
    InvalidAddressCells,
    /// The DTB being parsed contains invalid property name.
    InvalidPropertyName,
    /// The DTB being parsed contains invalid string table reference.
    InvalidStringTable,
    /// The DTB being parsed contains invalid node name.
    InvalidNodeName,
    /// Invalid DTB format.
    InvalidDtbFormat,
    /// A wrapper of std::io::Error.
    IoError(std::io::Error),
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Error {
        Error::IoError(error)
    }
}

/// Result type wrapper for this crate.
pub type Result<T> = std::result::Result<T, Error>;

// Token type defined by specification
#[repr(u32)]
enum FdtToken {
    BeginNode = 0x0000_0001,
    EndNode = 0x0000_0002,
    Prop = 0x0000_0003,
    Nop = 0x0000_0004,
    End = 0x0000_0009,
}

/// A single 32-bit cell in a property's value.
#[derive(Debug, Clone, PartialEq)]
pub enum Cell {
    /// A reference to an ident. See [set_ident][1]. It will be replaced with
    /// the referenced node's `phandle` which is also a 32-bit integer cell when
    /// we generate the devicetree blobs.
    ///
    /// [1]: struct.DeviceTree.html#method.set_ident
    Ref(String),
    /// A single 32-bit cell.
    Cell(u32),
}

/// A single unit of a property's value. Can be a bytestring, a string or
/// an array of 32-bit integer cells.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A list of 32-bit cells.
    Cells(Vec<Cell>),
    /// A array of raw bytes.
    Bytes(Vec<u8>),
}

/// The value of a node's property.
///
/// [Values][5] is just a newtype wrapper of Vec<[Value][1]> with several helpers.
/// In fact, [Values][5] is a container which can hold a mix of cells, byte_string
/// and strings. See [cells!][2], [strings!][3], [byte_string!][4] and [values!][5]
/// for reference.
///
/// # Examples
///
/// ```
/// use vmm_fdt::{Values, values, cells, strings, byte_string};
///
/// let cells = cells![0x1, 0x3, 0x4];
/// assert_eq!(cells.len(), 12);
/// assert_eq!(cells.first_u32().unwrap(), 0x1);
/// assert_eq!(cells.first_u64().unwrap(), 0x1_0000_0003);
///
/// let bytes = cells.to_bytes().unwrap();
/// assert_eq!(bytes[3], 0x1);
///
/// let ref_cells = cells![0x1, 0x3, 0x4, "ref"];
/// assert!(ref_cells.first_u32().is_err());
///
/// let v64 = vec![0x1_1000_0000u64, 0x30_1000_0000u64];
/// let values: Values = v64.into();
/// let bytes = values.to_bytes().unwrap();
/// assert_eq!(bytes[3], 0x1);
/// assert_eq!(bytes[11], 0x30);
/// ```
///
/// [1]: enum.Value.html
/// [2]: macro.cells.html
/// [3]: macro.strings.html
/// [4]: macro.byte_string.html
/// [5]: macro.values.html
/// [6]: struct.Values.html
#[derive(Debug, Clone, PartialEq)]
pub struct Values(pub Vec<Value>);

impl Values {
    /// Return the length in bytes.
    pub fn len(&self) -> usize {
        self.0.iter().fold(0, |s, v| {
            s + match v {
                Value::Cells(c) => c.len() * 4,
                Value::Bytes(b) => b.len(),
            }
        })
    }

    /// Combine the first 4 bytes to a big-endian u32
    pub fn first_u32(&self) -> Result<u32> {
        let bytes = self.to_bytes()?;
        if bytes.len() < 4 {
            return Err(Error::SizeMismatch);
        }
        Ok(u32::from_be_bytes(bytes[0..4].try_into().unwrap()))
    }

    /// Combine the first 8 bytes as a big-endian u64
    pub fn first_u64(&self) -> Result<u64> {
        let bytes = self.to_bytes()?;
        if bytes.len() < 8 {
            return Err(Error::SizeMismatch);
        }
        Ok(u64::from_be_bytes(bytes[0..8].try_into().unwrap()))
    }

    /// Convert the `Values` to a byte array. The method will return Error::RefExist
    /// when there is a Cell::Ref inside the `Values`.
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut bytes = vec![];
        for v in &self.0 {
            match v {
                Value::Cells(cs) => {
                    for c in cs {
                        match c {
                            Cell::Ref(_) => return Err(Error::RefExist),
                            Cell::Cell(c) => bytes.extend(&c.to_be_bytes()),
                        }
                    }
                }
                Value::Bytes(bs) => {
                    bytes.extend(bs);
                }
            }
        }
        Ok(bytes)
    }
}

impl From<Vec<u64>> for Values {
    fn from(vec: Vec<u64>) -> Values {
        let mut cells = vec![];

        for v in vec {
            cells.push(Cell::Cell((v >> 32) as u32));
            cells.push(Cell::Cell(v as u32));
        }

        Values(vec![Value::Cells(cells)])
    }
}

impl TryFrom<&Values> for u32 {
    type Error = Error;

    fn try_from(v: &Values) -> Result<u32> {
        if v.len() != 4 {
            return Err(Error::SizeMismatch);
        }
        v.first_u32()
    }
}

impl From<u32> for Cell {
    fn from(cell: u32) -> Cell {
        Cell::Cell(cell)
    }
}

impl From<&str> for Cell {
    fn from(str: &str) -> Cell {
        Cell::Ref(String::from(str))
    }
}

impl From<&str> for Value {
    fn from(str: &str) -> Value {
        Value::Bytes(Vec::from(str.as_bytes()))
    }
}

/// A helper to combine several values for a property.
///
/// # Examples
///
/// ```
/// use vmm_fdt::{values, cells, strings, byte_string};
///
/// let a = values![cells![0x1, "hello"]];
/// let b = values![byte_string![1, 2, 3, 4]];
/// let c = values![strings!["hello"]];
/// let d = values![cells![0x1, 0x4], strings!["hello"]];
/// ```
#[macro_export]
macro_rules! values {
    [ $( $x:expr ),* ] => {
        {
            use $crate::{Value, Values};
            let mut temp_vec: Vec<Value> = vec![];
            $(
                temp_vec.append(&mut $x.0);
            )*
            Values(temp_vec)
        }
    };
}

/// A helper to construct byte string.
///
/// # Examples
///
/// ```
/// use vmm_fdt::{Value, byte_string};
///
/// let bytes = byte_string![0x22, 0x5, 0x6];
///
/// match &bytes.0[0] {
///     Value::Bytes(b) => {
///         assert_eq!(b.len(), 3);
///         assert_eq!(b[2], 0x6);
///     },
///     Value::Cells(_) => panic!("wrong format"),
/// }
/// ```
#[macro_export]
macro_rules! byte_string {
    [ $( $x:expr ),* ] => {
        {
            use $crate::{Value, Values};
            let mut temp_vec: Vec<u8> = Vec::new();
            $(
                temp_vec.push($x);
            )*
            Values(vec![Value::Bytes(temp_vec)])
        }
    };
}

/// A helper to construct a list of 32-bit cells.
///
/// # Examples
/// ```
/// use vmm_fdt::{cells, Cell, Value};
///
/// let cells = cells![0x2, "gic"];
/// assert_eq!(cells.0, [Value::Cells(vec![Cell::Cell(0x2), Cell::Ref("gic".to_string())])]);
/// ```
#[macro_export]
macro_rules! cells {
    [ $( $x:expr ),* ] => {
        {
            use $crate::{Value, Cell, Values};
            let mut temp_vec: Vec<Cell> = Vec::new();
            $(
                temp_vec.push($x.into());
            )*
            Values(vec![Value::Cells(temp_vec)])
        }
    };
}

/// A helper to convert a list of strings to raw byte string.
///
/// # Examples
///
/// ```
/// use vmm_fdt::{strings, Value};
///
/// let bytes = strings!["ab", "c"];
///
/// match &bytes.0[0] {
///     Value::Bytes(b) => {
///         assert_eq!(b[0], 0x61);
///         assert_eq!(b[2], 0x0);
///         assert_eq!(b[3], 0x63);
///         assert_eq!(b[4], 0x0);
///     },
///     Value::Cells(_) => panic!("wrong formats"),
/// }
/// ```
#[macro_export]
macro_rules! strings {
    [ $( $x:expr ),* ] => {
        {
            use $crate::{Value, Values};
            let mut temp_vec: Vec<u8> = Vec::new();
            $(
                temp_vec.extend($x.as_bytes());
                temp_vec.push(0);
            )*
            Values(vec![Value::Bytes(temp_vec)])
        }
    };
}

type Phandle = u32;
use std::collections::HashMap;

/// A in-memory device tree.
#[derive(Debug)]
pub struct DeviceTree {
    // the index of the root node
    root: Index,
    arena: Arena<Node>,

    ident_map: HashMap<String, Phandle>,
    next_phandle: Phandle,

    str_map: HashMap<String, u32>,
    next_strid: u32,

    // memory reservation block
    reserved: Vec<ReserveEntry>,
    boot_cpuid: u32,
}

#[derive(Debug)]
struct ReserveEntry {
    address: u64,
    size: u64,
}

#[derive(Debug)]
struct Property {
    name: u32,
    values: Values,
}

#[derive(Debug)]
struct Node {
    name: String,
    ident: Option<String>,
    properties: Vec<Property>,
    subnodes: Vec<Index>,

    parent: Option<Index>,
    adderss_cells: u32,
    size_cells: u32,
}

impl Node {
    fn new(name: &str) -> Node {
        Node {
            name: String::from(name),
            ident: None,
            properties: vec![],
            subnodes: vec![],
            parent: None,
            adderss_cells: 2,
            size_cells: 1,
        }
    }

    fn set_ident(&mut self, ident: &str) {
        self.ident = Some(String::from(ident));
    }

    fn set_phandle(&mut self, name: u32, phandle: Phandle) {
        self.set_property(name, cells![phandle]);
    }

    fn set_property(&mut self, name: u32, values: Values) {
        // handle property overwrite
        for p in self.properties.iter_mut() {
            if p.name == name {
                p.values = values;
                return;
            }
        }
        self.properties.push(Property { name, values })
    }

    fn get_property(&self, name: u32) -> Result<Values> {
        for p in self.properties.iter() {
            if p.name == name {
                return Ok(p.values.clone());
            }
        }
        Err(Error::NoSuchProperty)
    }

    fn set_address_cells(&mut self, cells: u32) {
        self.adderss_cells = cells;
    }

    fn address_cells(&self) -> u32 {
        self.adderss_cells
    }

    fn set_size_cells(&mut self, cells: u32) {
        self.size_cells = cells;
    }
}

/// A handle used to identify a node in a [DeviceTree][1].
///
/// The general idea behind this type is to simplify reference management of
/// [DeviceTree][1]. A [NodeHandle](struct.NodeHandle.html) is just an integer
/// ID and it is only meaningful with its associated [DeviceTree][1].
///
/// [1]: struct.DeviceTree.html
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NodeHandle(Index);

impl From<&Index> for NodeHandle {
    fn from(index: &Index) -> NodeHandle {
        NodeHandle(*index)
    }
}

impl DeviceTree {
    /// Create a new device tree.
    pub fn new() -> DeviceTree {
        let mut arena = Arena::new();
        // the name of root node should not be used
        let root = arena.insert(Node::new(""));
        DeviceTree {
            root,
            arena,
            ident_map: HashMap::new(),
            next_phandle: 1,
            str_map: HashMap::new(),
            next_strid: 0,
            reserved: vec![],
            boot_cpuid: 0,
        }
    }

    /// Parse a device tree blob into [DeviceTree](struct.DeviceTree.html).
    pub fn parse(dtb: &[u8]) -> Result<DeviceTree> {
        parser::parse_dtb(dtb)
    }

    /// Add an entry in memory reservation block.
    pub fn reserve_memory(&mut self, address: u64, size: u64) {
        // TODO validate the reservation block
        self.reserved.push(ReserveEntry { address, size });
    }

    /// Set the `boot_cpuid_phys` field in the device tree header.
    pub fn set_boot_cpuid(&mut self, cpuid: u32) {
        self.boot_cpuid = cpuid;
    }

    /// Get the `boot_cpuid_phys` field in the device tree header.
    pub fn boot_cpuid(&self) -> u32 {
        self.boot_cpuid
    }

    /// Allocate a new tree node and returns its `NodeHandle`.
    pub fn alloc_node(&mut self, parent: NodeHandle, name: &str) -> Result<NodeHandle> {
        if !self.node_exist(parent) {
            return Err(Error::NoSuchNode);
        }

        let mut node = Node::new(name);
        node.parent = Some(parent.0);
        let index = self.arena.insert(node);
        let pn = self.get_mut(parent)?;

        pn.subnodes.push(index);
        Ok(NodeHandle(index))
    }

    fn alloc_phandle(&mut self, ident: &str) -> Phandle {
        if let Some(phandle) = self.ident_map.get(ident) {
            return *phandle;
        }
        let phandle = self.next_phandle;
        self.next_phandle += 1;
        self.ident_map.insert(String::from(ident), phandle);
        phandle
    }

    fn get_phandle(&self, ident: &str) -> Option<Phandle> {
        match self.ident_map.get(ident) {
            None => None,
            Some(&p) => Some(p),
        }
    }

    fn alloc_strid(&mut self, str: &str) -> u32 {
        if let Some(id) = self.get_strid(str) {
            return id;
        }
        let strid = self.next_strid;
        self.next_strid += 1;
        self.str_map.insert(String::from(str), strid);
        strid
    }

    fn get_strid(&self, str: &str) -> Option<u32> {
        match self.str_map.get(str) {
            None => None,
            Some(&id) => Some(id),
        }
    }

    /// Set a device tree node's identification. An identification is a string
    /// which is used to globally reference a node in the device tree. **Be noted**
    /// that this method will set the `phandle` property of the node.
    pub fn set_ident(&mut self, node: NodeHandle, ident: &str) -> Result<()> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }

        if self.get_phandle(ident).is_some() {
            return Err(Error::IdentConflict);
        }

        let strid = self.alloc_strid("phandle");
        let phandle = self.alloc_phandle(ident);
        let node = self.get_mut(node)?;
        node.set_ident(ident);
        node.set_phandle(strid, phandle);
        Ok(())
    }

    /// Return the NodeHandle of the root node in the device tree.
    pub fn root(&self) -> NodeHandle {
        NodeHandle(self.root)
    }

    /// Test wether a NodeHandle is valid, i.e., whether the node is exist
    /// in the device tree.
    pub fn node_exist(&self, node: NodeHandle) -> bool {
        self.arena.contains(node.0)
    }

    fn get(&self, node: NodeHandle) -> Result<&Node> {
        self.arena.get(node.0).ok_or(Error::NoSuchNode)
    }

    fn get_mut(&mut self, node: NodeHandle) -> Result<&mut Node> {
        self.arena.get_mut(node.0).ok_or(Error::NoSuchNode)
    }

    /// Insert a propery to the device tree node.
    pub fn set_property(&mut self, node: NodeHandle, p: &str, v: Values) -> Result<()> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }
        // do not allocate a new string id if there is not such a node
        let strid = self.alloc_strid(p);
        let node = self.get_mut(node)?;

        if p == "#address-cells" || p == "#size-cells" {
            let size = u32::try_from(&v)?;
            if p == "#address-cells" {
                node.set_address_cells(size);
            } else {
                node.set_size_cells(size);
            }
        }

        node.set_property(strid, v);
        Ok(())
    }

    /// Return a node's name. The name will be extended as `name@address` when
    /// `reg` is exist as a property of the node.
    pub fn node_name(&self, node: NodeHandle) -> Result<String> {
        let handle = node;
        let node = self.get(node)?;
        let reg = self.get_property(handle, "reg");

        if let (Ok(reg), Some(parent)) = (reg, node.parent) {
            let size = self.get(NodeHandle(parent))?.address_cells();
            let addr = match size {
                1 => reg.first_u32()? as u64,
                2 => reg.first_u64()?,
                _ => return Err(Error::InvalidAddressCells),
            };
            return Ok(format!("{}@{:x}", node.name, addr));
        }

        Ok(node.name.clone())
    }

    /// Returns the value of a node's property.
    pub fn get_property(&self, node: NodeHandle, p: &str) -> Result<Values> {
        let node = self.get(node)?;
        let strid = self.get_strid(p).ok_or(Error::NoSuchProperty)?;
        node.get_property(strid)
    }

    /// Generate a DTB blob.
    pub fn to_dtb<T: Seek + Write>(&self, buffer: &mut T) -> Result<()> {
        let mut str_offset: HashMap<u32, u32> = HashMap::new();
        let mut offset = 0;

        // construct the string table first
        for (str, id) in &self.str_map {
            str_offset.insert(*id, offset);
            offset += str.len() as u32 + 1;
        }

        // do not left free space after the header
        buffer.seek(SeekFrom::Start(40))?;

        // memory reservation block generation
        align_to(buffer, 8)?;
        let off_mem_rsvmap = buffer.seek(SeekFrom::Current(0))? as u32;
        for r in &self.reserved {
            buffer.write(&r.address.to_be_bytes())?;
            buffer.write(&r.size.to_be_bytes())?;
        }
        // mark the end of memory reservation block
        buffer.write(&0u64.to_be_bytes())?;
        buffer.write(&0u64.to_be_bytes())?;

        // structure block generation
        align_to(buffer, 4)?;
        let off_dt_struct = buffer.seek(SeekFrom::Current(0))? as u32;
        self.write_node(self.root(), buffer, &str_offset)?;
        align_to(buffer, 4)?;
        buffer.write(&u32::to_be_bytes(FdtToken::End as u32))?;
        let size_dt_struct = buffer.seek(SeekFrom::Current(0))? as u32 - off_dt_struct;

        // strings block generation
        // strings block does not has alignment requirement
        let mut size_dt_strings = 0;
        let pos = buffer.seek(SeekFrom::Current(0))?;
        let off_dt_strings = pos as u32;
        for (s, id) in &self.str_map {
            let offset = *str_offset.get(id).unwrap();
            let end = offset + s.len() as u32 + 1;
            if end > size_dt_strings {
                size_dt_strings = end;
            }

            buffer.seek(SeekFrom::Start(pos + offset as u64))?;
            buffer.write(s.as_bytes())?;
            buffer.write(&[0x0])?; // null terminator
        }

        // fill the device tree header
        //
        // struct fdt_header {
        //      uint32_t magic;
        //      uint32_t totalsize;
        //      uint32_t off_dt_struct;
        //      uint32_t off_dt_strings;
        //      uint32_t off_mem_rsvmap;
        //      uint32_t version;
        //      uint32_t last_comp_version;
        //      uint32_t boot_cpuid_phys;
        //      uint32_t size_dt_strings;
        //      uint32_t size_dt_struct;
        // };

        buffer.seek(SeekFrom::Start(0))?;

        buffer.write(&u32::to_be_bytes(0xd00dfeed))?; // magic
        buffer.write(&u32::to_be_bytes(off_dt_strings + size_dt_strings))?; // totalsize
        buffer.write(&u32::to_be_bytes(off_dt_struct))?; // off_dt_struct
        buffer.write(&u32::to_be_bytes(off_dt_strings))?; // off_dt_strings
        buffer.write(&u32::to_be_bytes(off_mem_rsvmap))?; // off_mem_rsvmap
        buffer.write(&u32::to_be_bytes(17))?; // version
        buffer.write(&u32::to_be_bytes(16))?; // last_comp_version
        buffer.write(&u32::to_be_bytes(self.boot_cpuid))?; // boot_cpuid_phys
        buffer.write(&u32::to_be_bytes(size_dt_strings))?; // size_dt_strings
        buffer.write(&u32::to_be_bytes(size_dt_struct))?; // size_dt_struct;

        Ok(())
    }

    fn write_node<T: Seek + Write>(
        &self,
        node: NodeHandle,
        buffer: &mut T,
        str_offset: &HashMap<u32, u32>,
    ) -> Result<()> {
        assert_eq!(buffer.seek(SeekFrom::Current(0))? & 0x3, 0);
        let name = self.node_name(node)?;
        let node = self.get(node)?;

        buffer.write(&u32::to_be_bytes(FdtToken::BeginNode as u32))?;
        buffer.write(name.as_bytes())?;
        buffer.write(&[0x0])?; // null terminator of the string
        align_to(buffer, 4)?;

        // write the properties
        for prop in &node.properties {
            buffer.write(&u32::to_be_bytes(FdtToken::Prop as u32))?;
            buffer.write(&u32::to_be_bytes(prop.values.len() as u32))?;
            buffer.write(&u32::to_be_bytes(*str_offset.get(&prop.name).unwrap()))?;

            for v in &prop.values.0 {
                match v {
                    Value::Cells(v) => {
                        for cell in v {
                            buffer.write(&u32::to_be_bytes(match cell {
                                Cell::Cell(c) => *c,
                                Cell::Ref(r) => self.get_phandle(r).unwrap(),
                            }))?;
                        }
                    }
                    Value::Bytes(v) => {
                        buffer.write(v.as_ref())?;
                    }
                };
            }

            align_to(buffer, 4)?;
        }

        // write child node
        for child in &node.subnodes {
            self.write_node(child.into(), buffer, str_offset)?;
        }

        buffer.write(&u32::to_be_bytes(FdtToken::EndNode as u32))?;
        Ok(())
    }
}

// make the `buffer`'s current pointer align to the `align`.
fn align_to<T: Seek>(buffer: &mut T, align: u64) -> Result<()> {
    let off = (!buffer.seek(SeekFrom::Current(0))? + 1) & (align - 1);
    buffer.seek(SeekFrom::Current(off as i64))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::*;
    use std::io::Cursor;

    #[test]
    fn tree_op() {
        let mut tree = DeviceTree::new();
        let root = tree.root();
        let node = tree.alloc_node(root, "cpus").unwrap();
        tree.set_ident(node, "controller").unwrap();
        tree.set_property(node, "#address-cells", cells![0x2])
            .unwrap();

        assert!(tree.get_property(node, "no-exist").is_err());
        assert_eq!(
            tree.get_property(node, "#address-cells").unwrap(),
            cells![0x2]
        );

        tree.set_property(node, "#address-cells", cells![0x1])
            .unwrap();
        assert_eq!(
            tree.get_property(node, "#address-cells").unwrap(),
            cells![0x1]
        );

        assert!(tree.set_ident(node, "controller").is_err());

        tree.set_boot_cpuid(0x101);
        assert_eq!(tree.boot_cpuid(), 0x101);
    }

    #[test]
    fn auto_naming() {
        let mut tree = DeviceTree::new();
        let root = tree.root();
        let node = tree.alloc_node(root, "test").unwrap();
        tree.set_property(root, "#address-cells", cells![0x2])
            .unwrap();

        tree.set_property(node, "reg", cells![0x2, 0x1000_0000])
            .unwrap();
        assert_eq!(tree.node_name(node).unwrap(), "test@210000000");

        tree.set_property(node, "reg", cells![0x2]).unwrap();
        assert!(tree.node_name(node).is_err());
    }

    #[test]
    fn generate() {
        let mut tree = DeviceTree::new();
        tree.reserve_memory(0x0, 0x100000);

        let node = tree.alloc_node(tree.root(), "interrupt").unwrap();
        tree.set_ident(node, "gic").unwrap();
        tree.set_property(node, "reg", cells![0x0, 0x4000_0000])
            .unwrap();

        let mut buffer = Cursor::new(vec![0; 0x200000]);
        tree.to_dtb(&mut buffer).unwrap();
    }

    #[test]
    fn helper() {
        let mut buffer = Cursor::new(vec![0; 0x100]);
        buffer.write(&[0xff]).unwrap();
        align_to(&mut buffer, 4).unwrap();
        assert_eq!(buffer.position(), 4);

        buffer.write(&u32::to_be_bytes(0x123456)).unwrap();
        align_to(&mut buffer, 4).unwrap();
        assert_eq!(buffer.position(), 8);
    }
}
