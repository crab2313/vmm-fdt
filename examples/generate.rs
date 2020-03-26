use std::fs::File;
use vmm_fdt::{cells, strings, DeviceTree, Result};

fn generate() -> Result<()> {
    let mut fdt = DeviceTree::new();

    let root = fdt.root();
    fdt.set_property(root, "interrupt-parent", cells!["gic"])?;
    fdt.set_property(root, "compatible", strings!["linux,cloud-hypervisor"])?;
    fdt.set_property(root, "#address-cells", cells![0x2])?;
    fdt.set_property(root, "#size-cells", cells![0x2])?;

    let chosen = fdt.alloc_node(root, "chosen")?;
    fdt.set_property(
        chosen,
        "bootargs",
        strings!["console=hvc0 nokaslr root=/dev/vda"],
    )?;

    let memory = fdt.alloc_node(root, "memory")?;
    fdt.set_property(memory, "device_type", strings!["memory"])?;
    fdt.set_property(memory, "reg", cells![0x0, 0x4000_0000, 0x0, 0x2000_0000])?;

    let cpus = fdt.alloc_node(root, "cpus")?;
    fdt.set_property(cpus, "#address-cells", cells![0x1])?;
    fdt.set_property(cpus, "#size-cells", cells![0x0])?;

    let cpu0 = fdt.alloc_node(cpus, "cpu")?;
    fdt.set_property(cpu0, "compatible", strings!["arm,cortex-a53", "arm,armv8"])?;
    fdt.set_property(cpu0, "reg", cells![0x0])?;

    let interrupt = fdt.alloc_node(root, "interrupt-controller")?;
    fdt.set_ident(interrupt, "gic")?;
    fdt.set_property(interrupt, "compatible", strings!["arm,gic-400"])?;
    fdt.set_property(interrupt, "interrupt-controller", cells![])?;
    fdt.set_property(interrupt, "#interrupt-cells", cells![0x3])?;
    fdt.set_property(interrupt, "#address-cells", cells![0x0])?;
    fdt.set_property(
        interrupt,
        "reg",
        cells![0x0, 0x3000_0000, 0x0, 0x1000, 0x0, 0x3001_0000, 0x0, 0x1000],
    )?;

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
