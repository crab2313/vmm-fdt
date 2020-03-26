#![deny(missing_docs)]

//! A simple flatten device tree (FDT) generator.

use byteorder::{BigEndian, WriteBytesExt};
use generational_arena::{Arena, Index};

use std::io::prelude::*;
use std::io::SeekFrom;

/// Core error type used in this crate.
#[derive(Debug)]
pub enum Error {
    /// The node is not exist in the device tree.
    NoSuchNode,
    /// The property is not exist in the device tree node.
    NoSuchProperty,
    /// A wrapper of std::io::Error
    IoError(std::io::Error),
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Error {
        Error::IoError(error)
    }
}

/// Result type wrapper for this crate.
pub type Result<T> = std::result::Result<T, Error>;

/// Representation of a single cell in a property.
#[derive(Debug, Clone, PartialEq)]
pub enum Cell {
    /// A reference to an identification.
    Ref(String),
    /// A single 32-bit cell.
    Cell(u32),
}

type Phandle = u32;
use std::collections::HashMap;

/// A representation of device tree.
#[derive(Debug)]
pub struct DeviceTree {
    // the index of the root node
    root: Index,
    arena: Arena<Node>,

    ident_map: HashMap<String, Phandle>,
    next_phandle: Phandle,

    str_map: HashMap<String, u32>,
    next_strid: u32,
}

#[derive(Debug)]
struct Property {
    name: u32,
    value: Vec<Cell>,
}

#[derive(Debug)]
struct Node {
    name: String,
    ident: Option<String>,
    properties: Vec<Property>,
    subnodes: Vec<Index>,
}

impl Node {
    fn new(name: &str) -> Node {
        Node {
            name: String::from(name),
            ident: None,
            properties: vec![],
            subnodes: vec![],
        }
    }

    fn set_ident(&mut self, ident: &str) {
        self.ident = Some(String::from(ident));
    }

    fn set_phandle(&mut self, name: u32, phandle: Phandle) {
        self.set_property(name, vec![Cell::Cell(phandle)]);
    }

    fn set_property(&mut self, name: u32, value: Vec<Cell>) {
        self.properties.push(Property { name, value })
    }

    fn get_property(&self, name: u32) -> Result<Vec<Cell>> {
        for p in self.properties.iter() {
            if p.name == name {
                return Ok(p.value.clone());
            }
        }
        Err(Error::NoSuchProperty)
    }
}

/// A handle used to reference a node in the device tree.
#[derive(Debug, Clone, Copy)]
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
        let root = arena.insert(Node::new("root"));
        DeviceTree {
            root,
            arena,
            ident_map: HashMap::new(),
            next_phandle: 0,
            str_map: HashMap::new(),
            next_strid: 0,
        }
    }

    /// Allocate a new tree node and returns its `NodeHandle`.
    pub fn alloc_node(&mut self, parent: NodeHandle, name: &str) -> Result<NodeHandle> {
        let arena = &mut self.arena;

        if !arena.contains(parent.0) {
            return Err(Error::NoSuchNode);
        }

        let index = arena.insert(Node::new(name));
        let pn = arena.get_mut(parent.0).ok_or(Error::NoSuchNode)?;

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
        let strid = self.alloc_strid("phandle");
        let phandle = self.alloc_phandle(ident);
        let node = self.arena.get_mut(node.0).ok_or(Error::NoSuchNode)?;
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

    /// Insert a propery to the device tree node.
    pub fn set_property(&mut self, node: NodeHandle, p: &str, v: Vec<Cell>) -> Result<()> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }
        let strid = self.alloc_strid(p);
        let node = self.arena.get_mut(node.0).ok_or(Error::NoSuchNode)?;
        node.set_property(strid, v);
        Ok(())
    }

    /// Returns the value of a node's property.
    pub fn get_property(&self, node: NodeHandle, p: &str) -> Result<Vec<Cell>> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }
        let strid = self.get_strid(p).ok_or(Error::NoSuchProperty)?;
        let node = self.arena.get(node.0).ok_or(Error::NoSuchNode)?;
        node.get_property(strid)
    }

    /// Generate a DTB blob
    pub fn to_dtb<T: Seek + Write>(&self, buffer: &mut T) -> Result<()> {
        let mut str_offset: HashMap<u32, u32> = HashMap::new();
        let mut offset = 0;

        // construct the string table first
        for (str, id) in &self.str_map {
            str_offset.insert(*id, offset);
            offset += str.len() as u32 + 1;
        }

        // Write headers last
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

        // do not left free space after the header
        buffer.seek(SeekFrom::Start(40))?;

        // TODO reserved block
        self.write_node(self.root(), buffer, &str_offset)?;

        align_to(buffer, 4)?;
        buffer.write_u32::<BigEndian>(FDT_END)?;
        Ok(())
    }

    fn write_node<T: Seek + Write>(
        &self,
        node: NodeHandle,
        buffer: &mut T,
        str_offset: &HashMap<u32, u32>,
    ) -> Result<()> {
        assert_eq!(buffer.seek(SeekFrom::Current(0))? & 0x3, 0);
        let node = self.arena.get(node.0).ok_or(Error::NoSuchNode)?;

        buffer.write_u32::<BigEndian>(FDT_BEGIN_NODE)?;
        buffer.write(node.name.as_bytes())?;
        buffer.write_u8(0x0).unwrap(); // null terminator of the string
        align_to(buffer, 4)?;

        // write the properties
        for prop in &node.properties {
            buffer.write_u32::<BigEndian>(FDT_PROP)?;
            buffer.write_u32::<BigEndian>(prop.value.len() as u32 * 4)?;
            buffer.write_u32::<BigEndian>(*str_offset.get(&prop.name).unwrap())?;
            for v in &prop.value {
                let cell = match v {
                    Cell::Cell(c) => *c,
                    Cell::Ref(r) => self.get_phandle(r).unwrap(),
                };

                buffer.write_u32::<BigEndian>(cell)?;
            }
            align_to(buffer, 4)?;
        }

        // write child node
        for child in &node.subnodes {
            self.write_node(child.into(), buffer, str_offset)?;
        }

        buffer.write_u32::<BigEndian>(FDT_END_NODE).unwrap();
        Ok(())
    }
}

fn align_to<T: Seek>(buffer: &mut T, align: u64) -> Result<()> {
    let off = (!buffer.seek(SeekFrom::Current(0))? + 1) & (align - 1);
    buffer.seek(SeekFrom::Current(off as i64))?;
    Ok(())
}

/// Token type defined by specification
const FDT_BEGIN_NODE: u32 = 0x0000_0001;
const FDT_END_NODE: u32 = 0x0000_0002;
const FDT_PROP: u32 = 0x0000_0003;
#[allow(dead_code)] // It should be used by the parser
const FDT_NOP: u32 = 0x0000_0004;
const FDT_END: u32 = 0x0000_0009;

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
        tree.set_property(node, "#address-cell", vec![Cell::Cell(0x2)])
            .unwrap();

        assert!(tree.get_property(node, "no-exist").is_err());
        assert_eq!(
            tree.get_property(node, "#address-cell").unwrap(),
            vec![Cell::Cell(0x2)]
        );
    }

    #[test]
    fn generate() {
        let mut tree = DeviceTree::new();
        let node = tree.alloc_node(tree.root(), "interrupt").unwrap();
        tree.set_ident(node, "gic").unwrap();

        let mut buffer = Cursor::new(vec![0; 0x200000]);
        tree.to_dtb(&mut buffer).unwrap();
    }

    #[test]
    fn helper() {
        let mut buffer = Cursor::new(vec![0; 0x100]);
        buffer.write_u8(0xff).unwrap();
        align_to(&mut buffer, 4).unwrap();
        assert_eq!(buffer.position(), 4);

        buffer.write_u32::<BigEndian>(0x123456).unwrap();
        align_to(&mut buffer, 4).unwrap();
        assert_eq!(buffer.position(), 8);
    }
}
