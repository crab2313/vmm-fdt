use std::fs::File;
use vmm_fdt::{Cell, DeviceTree, Result};

fn generate() -> Result<()> {
    let mut fdt = DeviceTree::new();
    let root = fdt.root();
    let node = fdt.alloc_node(root, "interrupt")?;
    fdt.set_ident(node, "gic")?;
    fdt.set_property(root, "interrupt-parent", vec![Cell::Ref("gic".to_string())])?;
    fdt.reserve_memory(0x0, 0x100000);

    let mut file = File::create("output.dtb")?;
    fdt.to_dtb(&mut file)
}

fn main() {
    match generate() {
        Err(e) => println!("failed to generate fdt! {:?}", e),
        Ok(()) => (),
    };
}
