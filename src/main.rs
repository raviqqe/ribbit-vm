mod instruction;
mod object;
mod primitive;
mod rib;
mod vm;

use vm::Vm;

const INPUT: &[u8] = b");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y";

fn main() {
    Vm::new(INPUT).run();
}
