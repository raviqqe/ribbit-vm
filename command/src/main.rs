use std::process::exit;
use vm::{Error, Vm};

const INPUT: &[u8] = b");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y";

fn main() {
    if let Err(error) = Vm::new(INPUT).run() {
        exit(match error {
            Error::IllegalInstruction | Error::IllegalPrimitive => 6,
        })
    }
}
