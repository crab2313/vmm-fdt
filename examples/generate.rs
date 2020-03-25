use vmm_fdt::{DeviceTree, PropertyValue, Result};

fn generate() -> Result<()> {
    let mut fdt = DeviceTree::new();
    let root = fdt.root();
    let node = fdt.alloc_node(root, "interrupt")?;
    fdt.set_ident(node, "gic")?;
    fdt.set_property(
        node,
        "interrupt-parent",
        vec![PropertyValue::Reference("gic".to_string())],
    )?;

    Ok(())
}

fn main() {
    match generate() {
        Err(e) => println!("failed to generate fdt! {:?}", e),
        Ok(()) => (),
    };
}
