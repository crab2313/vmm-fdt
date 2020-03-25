use vmm_fdt::{DeviceTree, Cell, Result};

fn generate() -> Result<()> {
    let mut fdt = DeviceTree::new();
    let root = fdt.root();
    let node = fdt.alloc_node(root, "interrupt")?;
    fdt.set_ident(node, "gic")?;
    fdt.set_property(
        node,
        "interrupt-parent",
        vec![Cell::Ref("gic".to_string())],
    )?;

    Ok(())
}

fn main() {
    match generate() {
        Err(e) => println!("failed to generate fdt! {:?}", e),
        Ok(()) => (),
    };
}
