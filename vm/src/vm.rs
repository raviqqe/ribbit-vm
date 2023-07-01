use crate::{
    error::Error,
    instruction::Instruction,
    object::Object,
    primitive::Primitive,
    rib::{self, Rib},
};
use std::{
    convert::TryInto,
    io::{stdin, Read},
    ops::{Add, Div, Mul, Sub},
};

const MAX_OBJECT_COUNT: usize = 1 << 14;
const SPACE_SIZE: usize = MAX_OBJECT_COUNT * rib::FIELD_COUNT;
const HEAP_SIZE: usize = SPACE_SIZE * 2;
const HEAP_BOTTOM: usize = 0;
const HEAP_MIDDLE: usize = HEAP_SIZE / 2;
#[allow(dead_code)]
const HEAP_TOP: usize = HEAP_SIZE;

const ZERO: Object = Object::Number(0);

const PAIR_TAG: Object = ZERO;
const CLOSURE_TAG: Object = Object::Number(1);
const SYMBOL_TAG: Object = Object::Number(2);
const STRING_TAG: Object = Object::Number(3);
const SINGLETON_TAG: Object = Object::Number(5);

fn get_rib_index(index: Object, field: usize) -> usize {
    // TODO Check this conversion
    (index.to_raw() + field as u64).try_into().unwrap()
}

fn get_car_index(index: Object) -> usize {
    get_rib_index(index, 0)
}

fn get_cdr_index(index: Object) -> usize {
    get_rib_index(index, 1)
}

fn get_tag_index(index: Object) -> usize {
    get_rib_index(index, 2)
}

pub struct Vm<'a> {
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

impl<'a> Vm<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        let mut vm = Self {
            stack: ZERO,
            program_counter: ZERO,
            r#false: ZERO,

            position: 0,
            input,
            heap: [ZERO; HEAP_SIZE],
            symbol_table: ZERO,

            allocation_index: HEAP_BOTTOM,
            allocation_limit: HEAP_MIDDLE,
            scan: 0,
        };

        vm.initialize();

        vm
    }

    fn initialize(&mut self) {
        let init_0 = self.allocate_rib(ZERO, ZERO, SINGLETON_TAG);
        self.r#false = self.allocate_rib(init_0, init_0, SINGLETON_TAG);

        self.decode_symbol_table();
        self.decode_codes();

        let symbol_table = self.symbol_table;
        let rib = self.allocate_rib(ZERO, symbol_table, CLOSURE_TAG);
        let r#false = self.r#false;
        let r#true = self.get_true();
        let nil = self.get_nil();

        self.initialize_global(rib);
        self.initialize_global(r#false);
        self.initialize_global(r#true);
        self.initialize_global(nil);

        self.initialize_stack();
    }

    fn initialize_stack(&mut self) {
        self.push(ZERO, PAIR_TAG);
        self.push(ZERO, PAIR_TAG);

        let first = self.get_cdr(self.stack);
        self.heap[get_cdr_index(self.stack)] = ZERO;
        self.heap[get_tag_index(self.stack)] = first;

        self.heap[get_car_index(first)] = Object::Number(Instruction::Halt as u64);
        self.heap[get_cdr_index(first)] = ZERO;
        self.heap[get_tag_index(first)] = PAIR_TAG;
    }

    fn initialize_global(&mut self, object: Object) {
        let index = Object::Number(get_car_index(self.symbol_table) as u64);
        self.heap[get_car_index(index)] = object;
        self.symbol_table = self.get_cdr(self.symbol_table);
    }

    pub fn run(&mut self) -> Result<(), Error> {
        loop {
            let instruction = self.get_car(self.program_counter);
            println!("{}", instruction.to_raw() as i64);
            self.advance_program_counter();
            let instruction = self.get_car(self.program_counter);
            println!("{}", instruction.to_raw() as i64);

            match instruction.to_raw() {
                Instruction::HALT => return Ok(()),
                Instruction::APPLY => {
                    let jump = self.get_tag(self.program_counter) == ZERO;
                    let code = self.get_code();

                    if !code.is_rib() {
                        self.operate_primitive(
                            Primitive::try_from(code.to_raw())
                                .map_err(|_| Error::IllegalPrimitive)?,
                        );

                        if jump {
                            self.program_counter = self.get_continuation();
                            self.heap[get_cdr_index(self.stack)] =
                                self.get_car(self.program_counter);
                        }

                        self.advance_program_counter();
                    } else {
                        let code_object = self.get_code();
                        let argument_count = self.get_car(code_object);
                        self.heap[get_car_index(self.program_counter)] = self.get_code();

                        let procedure = self.get_procedure();
                        let mut s2 = self.allocate_rib(ZERO, procedure, PAIR_TAG);

                        for _ in 0..argument_count.to_raw() {
                            let pop_obj = self.pop();
                            s2 = self.allocate_rib(pop_obj, s2, PAIR_TAG);
                        }

                        let c2 = self.get_list_tail(s2, argument_count);

                        if jump {
                            let k = self.get_continuation();
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
                        self.get_list_tail(self.stack, cdr_obj)
                    } else {
                        self.get_cdr(self.program_counter)
                    };

                    self.heap[get_car_index(rib)] = x;

                    self.advance_program_counter();
                }
                Instruction::GET => {
                    let proc_obj = self.get_procedure();
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
                _ => return Err(Error::IllegalInstruction),
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

    fn allocate_rib(&mut self, car: Object, cdr: Object, tag: Object) -> Object {
        self.push(car, cdr);
        let stack = self.get_cdr(self.stack);
        let allocated = self.stack;

        self.heap[get_cdr_index(allocated)] = self.heap[get_tag_index(allocated)];
        self.heap[get_tag_index(allocated)] = tag;

        self.stack = stack;

        Object::Rib(allocated.to_raw())
    }

    fn allocate_rib2(&mut self, car: Object, cdr: Object, tag: Object) -> Object {
        self.push(car, tag);
        let stack = self.get_cdr(self.stack);
        let allocated = self.stack;

        self.heap[get_cdr_index(allocated)] = cdr;

        self.stack = stack;

        Object::Rib(allocated.to_raw())
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

    fn get_list_tail(&self, list: Object, index: Object) -> Object {
        if index.to_raw() == 0 {
            list
        } else {
            let rib = self.get_rib(list);
            self.get_list_tail(rib.cdr(), Object::Number(index.to_raw() - 1))
        }
    }

    fn get_symbol_ref(&self, index: Object) -> Object {
        self.get_list_tail(self.symbol_table, index)
    }

    fn get_operand(&self, object: Object) -> Object {
        self.get_rib(if object.is_rib() {
            object
        } else {
            self.get_list_tail(self.stack, object)
        })
        .car()
    }

    fn get_procedure(&self) -> Object {
        self.get_operand(self.get_cdr(self.program_counter))
    }

    fn get_code(&self) -> Object {
        self.get_car(self.get_procedure())
    }

    fn get_continuation(&self) -> Object {
        let mut stack = self.stack;

        while self.get_tag(stack).to_raw() != 0 {
            stack = self.get_cdr(stack);
        }

        stack
    }

    fn operate_primitive(&mut self, primitive: Primitive) {
        match primitive {
            Primitive::Rib => {
                let rib = self.allocate_rib(ZERO, ZERO, ZERO);
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

                self.heap[self.get_tos_index()] = self.allocate_rib(x, y, CLOSURE_TAG);
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
        let mut count = self.read_integer(0);

        while count > 0 {
            count -= 1;
            let nil = self.get_nil();
            self.create_symbol(nil);
        }

        let mut name = self.get_nil();

        loop {
            match self.read_byte() {
                44 => {
                    self.create_symbol(name);
                    name = self.get_nil();
                }
                59 => break,
                c => {
                    name = self.allocate_rib(Object::Number(c as u64), name, PAIR_TAG);
                }
            }
        }

        self.create_symbol(name);
    }

    fn create_symbol(&mut self, name: Object) {
        let len = self.get_list_length(name);
        let list = self.allocate_rib(name, len, STRING_TAG);
        let symbol = self.allocate_rib(self.r#false, list, SYMBOL_TAG);

        self.symbol_table = self.allocate_rib(symbol, self.symbol_table, PAIR_TAG);
    }

    fn decode_codes(&mut self) {
        let weights = [20, 30, 0, 10, 11, 4];

        let mut n;
        let mut d;
        let mut op;

        loop {
            let x = self.read_code();
            n = Object::Number(x as u64);
            op = -1;

            while n.to_raw() > {
                op += 1;
                d = weights[op as usize];
                d + 2
            } {
                n = Object::Number(n.to_raw() - d - 3);
            }

            if x > 90 {
                op = Instruction::If as i64;
                n = self.pop();
            } else {
                if op == 0 {
                    self.push(ZERO, ZERO);
                }

                n = if n.to_raw() >= d {
                    if n.to_raw() == d {
                        Object::Number(self.read_integer(0) as u64)
                    } else {
                        let integer = self.read_integer((n.to_raw() - d - 1) as i64);
                        self.get_symbol_ref(Object::Number(integer as u64))
                    }
                } else if op < 3 {
                    self.get_symbol_ref(n)
                } else {
                    n
                };

                if op > 4 {
                    let obj = self.pop();
                    let rib2 = self.allocate_rib2(n, ZERO, obj);
                    let nil = self.get_nil();
                    n = self.allocate_rib(rib2, nil, CLOSURE_TAG);

                    if self.stack.to_raw() == ZERO.to_raw() {
                        break;
                    }
                } else if op > 0 {
                    op -= 1;
                } else {
                    op = 0;
                }
            }

            let c = self.allocate_rib(Object::Number(op as u64), n, ZERO);
            self.heap[get_cdr_index(c)] = self.heap[self.get_tos_index()];
            self.heap[self.get_tos_index()] = c;
        }

        let car = self.get_car(n);
        let tag = self.get_tag(car);

        self.program_counter = self.get_tag(tag);
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.input[self.position];
        self.position += 1;
        byte
    }

    fn read_code(&mut self) -> i64 {
        let x = self.read_byte() as i64 - 35;

        if x < 0 {
            57
        } else {
            x
        }
    }

    fn read_integer(&mut self, mut n: i64) -> i64 {
        let x = self.read_code();
        n *= 46;

        if x < 46 {
            n + x
        } else {
            self.read_integer(n + x - 46)
        }
    }
}
