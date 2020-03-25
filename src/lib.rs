#![deny(missing_docs)]

//! A simple flatten device tree (FDT) generator.

use generational_arena::{Arena, Index};

/// Token type defined by specification
#[allow(dead_code)]
#[repr(u32)]
enum Token {
    BeginNode = 0x1,
    EndNode = 0x2,
    Prop = 0x3,
    Nop = 0x4,
    End = 0x9,
}

/// Core error type used in this crate.
#[derive(Debug)]
pub enum Error {
    /// The node is not exist in the device tree.
    NoSuchNode,
    /// The property is not exist in the device tree node.
    NoSuchProperty,
}

/// Result type wrapper for this crate.
pub type Result<T> = std::result::Result<T, Error>;

/// Representation of a single cell in a property.
#[derive(Debug, Clone, PartialEq)]
pub enum PropertyValue {
    /// A reference to an identification.
    Reference(String),
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
    value: Vec<PropertyValue>,
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
        self.set_property(name, vec![PropertyValue::Cell(phandle)]);
    }

    fn set_property(&mut self, name: u32, value: Vec<PropertyValue>) {
        self.properties.push(Property { name, value })
    }

    fn get_property(&self, name: u32) -> Result<Vec<PropertyValue>> {
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
    pub fn set_property(&mut self, node: NodeHandle, p: &str, v: Vec<PropertyValue>) -> Result<()> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }
        let strid = self.alloc_strid(p);
        let node = self.arena.get_mut(node.0).ok_or(Error::NoSuchNode)?;
        node.set_property(strid, v);
        Ok(())
    }

    /// Returns the value of a node's property.
    pub fn get_property(&self, node: NodeHandle, p: &str) -> Result<Vec<PropertyValue>> {
        if !self.node_exist(node) {
            return Err(Error::NoSuchNode);
        }
        let strid = self.get_strid(p).ok_or(Error::NoSuchProperty)?;
        let node = self.arena.get(node.0).ok_or(Error::NoSuchNode)?;
        node.get_property(strid)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn tree_op() {
        let mut tree = DeviceTree::new();
        let root = tree.root();
        let node = tree.alloc_node(root, "cpus").unwrap();
        tree.set_ident(node, "controller").unwrap();
        tree.set_property(node, "#address-cell", vec![PropertyValue::Cell(0x2)])
            .unwrap();

        assert!(tree.get_property(node, "no-exist").is_err());
        assert_eq!(
            tree.get_property(node, "#address-cell").unwrap(),
            vec![PropertyValue::Cell(0x2)]
        );
    }
}
