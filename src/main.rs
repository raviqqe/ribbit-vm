mod instruction;
mod object;
mod primitive;
mod rib;

use instruction::Instruction;
use object::Object;
use primitive::Primitive;
use rib::Rib;
use std::{
    convert::TryInto,
    io::{stdin, Read},
    ops::{Add, Div, Mul, Sub},
    process,
};

const MAX_OBJECT_COUNT: usize = 1 << 14;
const SPACE_SIZE: usize = MAX_OBJECT_COUNT * rib::FIELD_COUNT;
const HEAP_SIZE: usize = SPACE_SIZE * 2;
const HEAP_BOTTOM: usize = 0;
const HEAP_MIDDLE: usize = HEAP_SIZE / 2;
#[allow(dead_code)]
const HEAP_TOP: usize = HEAP_SIZE;

const NUMBER_0: Object = Object::Number(0);
const PAIR_TAG: Object = Object::Number(0);
const CLOSURE_TAG: Object = Object::Number(1);
const SYMBOL_TAG: Object = Object::Number(2);
const STRING_TAG: Object = Object::Number(3);
const SINGLETON_TAG: Object = Object::Number(5);

#[repr(i32)]
enum ExitCode {
    IllegalInstruction = 6,
}

fn exit(code: Option<ExitCode>) -> ! {
    process::exit(code.map(|code| code as i32).unwrap_or(0))
}

struct Vm<'a> {
    // Roots
    stack: Object,
    program_counter: Object,
    r#false: Object,

    position: usize,
    input: &'a [u8],

    heap: [Object; HEAP_SIZE],
    symbol_table: Object,

    allocation_index: usize,
    allocation_limit: usize,
    #[allow(dead_code)]
    scan: usize,
}

fn list_tail(vm: &mut Vm, list: usize, index: Object) -> usize {
    if index.to_raw() == 0 {
        list
    } else {
        let rib = vm.get_rib(Object::Number(list as u64));
        let cdr = rib.cdr().to_raw();
        list_tail(vm, cdr as usize, Object::Number(&index.to_raw() - 1))
    }
}

fn symbol_ref(vm: &mut Vm, n: Object) -> usize {
    let sym_table_idx = vm.symbol_table.to_raw() as usize;
    list_tail(vm, sym_table_idx, n)
}

fn get_operand(vm: &mut Vm, object: Object) -> Object {
    let rib = if !object.is_rib() {
        Object::Rib(list_tail(vm, vm.stack.to_raw() as usize, object) as u64)
    } else {
        object
    };

    vm.get_rib(rib).car()
}

fn get_procedure(vm: &mut Vm) -> Object {
    let cdr = vm.get_cdr(vm.program_counter);
    get_operand(vm, cdr)
}

fn code(vm: &mut Vm) -> Object {
    let procedure = get_procedure(vm);
    vm.get_car(procedure)
}

fn get_continuation(vm: &mut Vm) -> Object {
    let mut stack = vm.stack;

    while vm.get_tag(stack).to_raw() != 0 {
        stack = vm.get_cdr(stack);
    }

    stack
}

fn get_car_index(index: Object) -> usize {
    // TODO Check this conversion
    index.to_raw().try_into().unwrap()
}

fn get_cdr_index(index: Object) -> usize {
    // TODO Check this conversion
    (&index.to_raw() + 1).try_into().unwrap()
}

fn get_tag_index(index: Object) -> usize {
    // TODO Check this conversion
    (&index.to_raw() + 2).try_into().unwrap()
}

fn set_global(vm: &mut Vm, object: Object) {
    let index = Object::Number(get_car_index(vm.symbol_table) as u64);
    vm.heap[get_car_index(index)] = object;
    vm.symbol_table = vm.get_cdr(vm.symbol_table);
}

fn setup_stack(vm: &mut Vm) {
    vm.push(NUMBER_0, PAIR_TAG);
    vm.push(NUMBER_0, PAIR_TAG);

    let first = vm.get_cdr(vm.stack);
    vm.heap[get_cdr_index(vm.stack)] = NUMBER_0;
    vm.heap[get_tag_index(vm.stack)] = first;

    vm.heap[get_car_index(first)] = Object::Number(Instruction::Halt as u64);
    vm.heap[get_cdr_index(first)] = NUMBER_0;
    vm.heap[get_tag_index(first)] = PAIR_TAG;
}

fn create_symbol(vm: &mut Vm, name: Object) -> Object {
    let len = vm.get_list_length(name);
    let list = allocate_rib(vm, name, len, STRING_TAG);
    let symbol = allocate_rib(vm, vm.r#false, list, SYMBOL_TAG);
    allocate_rib(vm, symbol, vm.symbol_table, PAIR_TAG)
}

fn allocate_rib(vm: &mut Vm, car: Object, cdr: Object, tag: Object) -> Object {
    vm.push(car, cdr);
    let stack = vm.get_cdr(vm.stack);
    let allocated = vm.stack;

    vm.heap[get_cdr_index(allocated)] = vm.heap[get_tag_index(allocated)];
    vm.heap[get_tag_index(allocated)] = tag;

    vm.stack = stack;

    Object::Rib(allocated.to_raw())
}

fn allocate_rib2(vm: &mut Vm, car: Object, cdr: Object, tag: Object) -> Object {
    vm.push(car, tag);
    let stack = vm.get_cdr(vm.stack);
    let allocated = vm.stack;

    vm.heap[get_cdr_index(allocated)] = cdr;

    vm.stack = stack;

    Object::Rib(allocated.to_raw())
}

impl<'a> Vm<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        let mut vm = Self {
            stack: NUMBER_0,
            program_counter: NUMBER_0,
            r#false: NUMBER_0,

            position: 0,
            input,
            heap: [NUMBER_0; HEAP_SIZE],
            symbol_table: NUMBER_0,

            allocation_index: HEAP_BOTTOM,
            allocation_limit: HEAP_MIDDLE,
            scan: 0,
        };

        vm.initialize();

        vm
    }

    fn initialize(&mut self) {
        let init_0 = allocate_rib(self, NUMBER_0, NUMBER_0, SINGLETON_TAG);
        self.r#false = allocate_rib(self, init_0, init_0, SINGLETON_TAG);

        self.decode_symbol_table();
        self.decode_codes();

        let symbol_table = self.symbol_table;
        let rib = allocate_rib(self, NUMBER_0, symbol_table, CLOSURE_TAG);
        let r#false = self.r#false;
        let r#true = self.get_true();
        let nil = self.get_nil();

        set_global(self, rib);
        set_global(self, r#false);
        set_global(self, r#true);
        set_global(self, nil);

        setup_stack(self);
    }

    pub fn run(&mut self) {
        loop {
            let instruction = self.get_car(self.program_counter);
            println!("{}", instruction.to_raw() as i64);
            self.advance_program_counter();
            let instruction = self.get_car(self.program_counter);
            println!("{}", instruction.to_raw() as i64);

            match instruction.to_raw() {
                Instruction::HALT => exit(None),
                Instruction::APPLY => {
                    let jump = self.get_tag(self.program_counter) == NUMBER_0;

                    if !code(self).is_rib() {
                        let code_obj = code(self);

                        self.operate_primitive(
                            Primitive::try_from(code_obj.to_raw()).expect("valid primitive"),
                        );

                        if jump {
                            self.program_counter = get_continuation(self);
                            self.heap[get_cdr_index(self.stack)] =
                                self.get_car(self.program_counter);
                        }

                        self.advance_program_counter();
                    } else {
                        let code_object = code(self);
                        let argument_count = self.get_car(code_object);
                        self.heap[get_car_index(self.program_counter)] = code(self);

                        let procedure = get_procedure(self);
                        let mut s2 = allocate_rib(self, NUMBER_0, procedure, PAIR_TAG);

                        for _ in 0..argument_count.to_raw() {
                            let pop_obj = self.pop();
                            s2 = allocate_rib(self, pop_obj, s2, PAIR_TAG);
                        }

                        let c2 =
                            Object::Number(
                                list_tail(self, s2.to_raw() as usize, argument_count) as u64
                            );

                        if jump {
                            let k = get_continuation(self);
                            self.heap[get_car_index(c2)] = self.get_car(k);
                            self.heap[get_tag_index(c2)] = self.get_tag(k);
                        } else {
                            self.heap[get_car_index(c2)] = self.stack;
                            self.heap[get_tag_index(c2)] = self.get_tag(self.program_counter);
                        }

                        self.stack = s2;

                        let new_pc = self.get_car(self.program_counter);
                        self.heap[get_car_index(self.program_counter)] = instruction;
                        self.program_counter = self.get_tag(new_pc);
                    }
                }
                Instruction::SET => {
                    let x = self.pop();

                    let rib = if !self.get_cdr(self.program_counter).is_rib() {
                        let cdr_obj = self.get_cdr(self.program_counter);
                        let stack = self.stack.to_raw() as usize;
                        Object::Rib(list_tail(self, stack, cdr_obj) as u64)
                    } else {
                        self.get_cdr(self.program_counter)
                    };

                    self.heap[get_car_index(rib)] = x;

                    self.advance_program_counter();
                }
                Instruction::GET => {
                    let proc_obj = get_procedure(self);
                    self.push(proc_obj, PAIR_TAG);
                    self.advance_program_counter();
                }
                Instruction::CONSTANT => {
                    let object = self.get_cdr(self.program_counter);
                    self.push(object, PAIR_TAG);
                    self.advance_program_counter();
                }
                Instruction::IF => {
                    self.program_counter = if self.pop().to_raw() != self.r#false.to_raw() {
                        self.get_cdr(self.program_counter)
                    } else {
                        self.get_tag(self.program_counter)
                    };
                }
                _ => exit(Some(ExitCode::IllegalInstruction)),
            }
        }
    }

    fn advance_program_counter(&mut self) {
        self.program_counter = self.get_tag(self.program_counter);
    }

    fn pop(&mut self) -> Object {
        let value = self.get_car(self.stack);
        self.stack = self.get_cdr(self.stack);
        value
    }

    fn push(&mut self, car: Object, tag: Object) {
        self.heap[self.allocation_index] = car;
        self.allocation_index += 1;

        self.heap[self.allocation_index] = self.stack;
        self.allocation_index += 1;

        self.heap[self.allocation_index] = tag;
        self.allocation_index += 1;

        self.stack = Object::Rib((self.allocation_index - rib::FIELD_COUNT) as u64);

        if self.allocation_index == self.allocation_limit {
            self.collect_garbages();
        }
    }

    fn get_tos_index(&self) -> usize {
        get_car_index(self.stack)
    }

    fn get_rib(&self, index: Object) -> Rib<'_> {
        let index = index.to_raw() as usize;

        Rib::new(
            self.heap[index..index + rib::FIELD_COUNT]
                .try_into()
                .unwrap(),
        )
    }

    fn get_car(&self, index: Object) -> Object {
        self.get_rib(index).car()
    }

    fn get_cdr(&self, index: Object) -> Object {
        self.get_rib(index).cdr()
    }

    fn get_tag(&self, index: Object) -> Object {
        self.get_rib(index).tag()
    }

    fn get_true(&self) -> Object {
        self.get_car(self.r#false)
    }

    fn get_nil(&self) -> Object {
        self.get_cdr(self.r#false)
    }

    fn get_boolean(&mut self, value: bool) -> Object {
        if value {
            self.get_true()
        } else {
            self.r#false
        }
    }

    fn get_list_length(&mut self, mut list: Object) -> Object {
        let mut len = 0;

        while list.is_rib() && self.get_tag(list).to_raw() == 0 {
            len += 1;
            list = self.get_cdr(list)
        }

        Object::Number(len)
    }

    fn operate_primitive(&mut self, primitive: Primitive) {
        match primitive {
            Primitive::Rib => {
                let rib = allocate_rib(self, NUMBER_0, NUMBER_0, NUMBER_0);
                self.heap[get_car_index(rib)] = self.pop();
                self.heap[get_cdr_index(rib)] = self.pop();
                self.heap[get_tag_index(rib)] = self.pop();
                self.push(rib, PAIR_TAG);
            }
            Primitive::Id => {
                let x = self.pop();
                self.push(x, PAIR_TAG);
            }
            Primitive::Pop => {
                self.pop();
                // TODO Check what is the meaning of true?
            }
            Primitive::Skip => {
                let x = self.pop();
                self.pop();
                self.push(x, PAIR_TAG);
            }
            Primitive::Close => {
                let x = self.get_car(Object::Number(self.get_tos_index() as u64));
                let y = self.get_cdr(self.stack);

                self.heap[self.get_tos_index()] = allocate_rib(self, x, y, CLOSURE_TAG);
            }
            Primitive::IsRib => {
                let x = self.pop();
                let condition = self.get_boolean(x.is_rib());
                self.push(condition, PAIR_TAG);
            }
            Primitive::Field0 => {
                let x = self.pop();
                let car = self.get_car(x);
                self.push(car, PAIR_TAG);
            }
            Primitive::Field1 => {
                let x = self.pop();
                let cdr = self.get_cdr(x);
                self.push(cdr, PAIR_TAG);
            }
            Primitive::Field2 => {
                let x = self.pop();
                let tag = self.get_tag(x);
                self.push(tag, PAIR_TAG)
            }
            Primitive::SetField0 => {
                let x = self.pop();
                let y = self.pop();
                self.heap[get_car_index(x)] = y;
                self.push(y, PAIR_TAG);
            }
            Primitive::SetField1 => {
                let x = self.pop();
                let y = self.pop();
                self.heap[get_cdr_index(x)] = y;
                self.push(y, PAIR_TAG);
            }
            Primitive::SetField2 => {
                let x = self.pop();
                let y = self.pop();
                self.heap[get_tag_index(x)] = y;
                self.push(y, PAIR_TAG);
            }
            Primitive::Equal => {
                self.operate_comparison(|x, y| x == y);
            }
            Primitive::LessThan => {
                self.operate_comparison(|x, y| x < y);
            }
            Primitive::Add => {
                self.operate_binary(Add::add);
            }
            Primitive::Subtract => {
                self.operate_binary(Sub::sub);
            }
            Primitive::Multiply => {
                self.operate_binary(Mul::mul);
            }
            Primitive::Divide => {
                self.operate_binary(Div::div);
            }
            Primitive::GetC => {
                let mut buffer = vec![0u8; 1];

                // TODO Handle errors.
                stdin().read_exact(&mut buffer).unwrap();

                self.push(Object::Number(buffer[0] as u64), PAIR_TAG);
            }
            Primitive::PutC => {
                let x = self.pop();

                print!("{}", x.to_raw() as u8 as char);
            }
        }
    }

    fn operate_binary(&mut self, operate: fn(u64, u64) -> u64) {
        let x = self.pop().to_raw();
        let y = self.pop().to_raw();

        self.push(Object::Number(operate(x, y)), PAIR_TAG);
    }

    fn operate_comparison(&mut self, operate: fn(u64, u64) -> bool) {
        let x = self.pop().to_raw();
        let y = self.pop().to_raw();

        let condition = self.get_boolean(operate(x, y));

        self.push(condition, PAIR_TAG);
    }

    // Garbage collection

    #[allow(dead_code)]
    fn collect_garbages(&mut self) {
        let to_space = if self.allocation_limit == HEAP_MIDDLE {
            HEAP_MIDDLE
        } else {
            HEAP_BOTTOM
        };

        self.allocation_limit = to_space + SPACE_SIZE;
        self.allocation_index = to_space;

        todo!()
    }

    // Decoding

    fn decode_symbol_table(&mut self) {
        let mut count = self.get_input_int(0);

        while count > 0 {
            count -= 1;
            let nil = self.get_nil();
            self.symbol_table = create_symbol(self, nil);
        }

        let mut name = self.get_nil();

        loop {
            let c = self.get_input_byte();

            if c == 44 {
                self.symbol_table = create_symbol(self, name);
                name = self.get_nil();
                continue;
            }

            if c == 59 {
                break;
            }

            name = allocate_rib(self, Object::Number(c as u64), name, PAIR_TAG);
        }

        self.symbol_table = create_symbol(self, name);
    }

    fn decode_codes(&mut self) {
        let weights = [20, 30, 0, 10, 11, 4];

        #[allow(unused_assignments)]
        let mut n = Object::Number(0);
        #[allow(unused_assignments)]
        let mut d = 0;
        #[allow(unused_assignments)]
        let mut op: i64 = -1;

        loop {
            let x = self.get_input_code();
            n = Object::Number(x as u64);
            op = -1;

            while n.to_raw() > {
                op += 1;
                d = weights[op as usize];
                d + 2
            } {
                n = Object::Number(&n.to_raw() - (d + 3));
            }

            if x > 90 {
                op = Instruction::If as i64;
                n = self.pop();
            } else {
                if op == 0 {
                    self.push(NUMBER_0, NUMBER_0);
                }

                if n.to_raw() >= d {
                    n = if n.to_raw() == d {
                        Object::Number(self.get_input_int(0) as u64)
                    } else {
                        let int = self.get_input_int((n.to_raw() - d - 1) as i64);
                        Object::Rib(symbol_ref(self, Object::Number(int as u64)) as u64)
                    }
                } else {
                    n = if op < 3 {
                        Object::Rib(symbol_ref(self, n) as u64)
                    } else {
                        n
                    }
                }

                if op > 4 {
                    let obj = self.pop();
                    let rib2 = allocate_rib2(self, n, NUMBER_0, obj);
                    let nil = self.get_nil();
                    n = allocate_rib(self, rib2, nil, CLOSURE_TAG);

                    if &self.stack.to_raw() == &NUMBER_0.to_raw() {
                        break;
                    }
                } else if op > 0 {
                    op -= 1;
                } else {
                    op = 0;
                }
            }

            let c = allocate_rib(self, Object::Number(op as u64), n, Object::Number(0));
            self.heap[get_cdr_index(c)] = self.heap[self.get_tos_index()];
            self.heap[self.get_tos_index()] = c;
        }

        let car = self.get_car(n);
        let tag = self.get_tag(car);

        self.program_counter = self.get_tag(tag);
    }

    fn get_input_byte(&mut self) -> u8 {
        let byte = self.input[self.position];
        self.position += 1;
        byte
    }

    fn get_input_code(&mut self) -> i64 {
        let x = i64::from(self.get_input_byte()) - 35;

        if x < 0 {
            57
        } else {
            x
        }
    }

    fn get_input_int(&mut self, number: i64) -> i64 {
        let x = self.get_input_code();
        let n = number * 46;

        if x < 46 {
            n + x
        } else {
            self.get_input_int(n + x - 46)
        }
    }
}

// @@(replace ");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y" (encode 92)
const INPUT: &[u8] = b");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y";
// )@@

fn main() {
    Vm::new(INPUT).run();
}
