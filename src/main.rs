use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use std::{
    convert::TryInto,
    io::{stdin, Read},
    ops::{Add, Div, Mul, Sub},
    process,
};

const RIB_FIELD_COUNT: usize = 3;
const MAX_OBJECT_COUNT: u32 = 30_000;
const SPACE_SIZE: u32 = MAX_OBJECT_COUNT * RIB_FIELD_COUNT as u32;
const HEAP_SIZE: usize = SPACE_SIZE as usize * 2;
const HEAP_BOTTOM: usize = 0;
const HEAP_MIDDLE: usize = HEAP_SIZE / 2;
#[allow(dead_code)]
const HEAP_TOP: usize = HEAP_SIZE;

const NUMBER_0: Object = tag_number(0);
const PAIR_TAG: Object = tag_number(0);
const CLOSURE_TAG: Object = tag_number(1);
const SYMBOL_TAG: Object = tag_number(2);
const STRING_TAG: Object = tag_number(3);
const SINGLETON_TAG: Object = tag_number(5);

const INSTRUCTION_APPLY: u64 = 0;
const INSTRUCTION_SET: u64 = 1;
const INSTRUCTION_GET: u64 = 2;
const INSTRUCTION_CONSTANT: u64 = 3;
const INSTRUCTION_IF: u64 = 4;
const INSTRUCTION_HALT: u64 = 5;

#[repr(i32)]
enum ExitCode {
    IllegalInstruction = 6,
}

fn exit(code: Option<ExitCode>) -> ! {
    process::exit(code.map(|code| code as i32).unwrap_or(0))
}

const fn tag_number(number: i64) -> Object {
    Object::Number(number as u64)
}

const fn tag_rib(number: u64) -> Object {
    Object::Rib(number)
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum Object {
    Number(u64),
    Rib(u64),
}

const fn unwrap_object(object: &Object) -> u64 {
    match object {
        Object::Number(number) => *number,
        Object::Rib(number) => *number,
    }
}

const fn is_rib(object: &Object) -> bool {
    matches!(object, Object::Rib(_))
}

struct Rib<'a> {
    fields: &'a [Object; RIB_FIELD_COUNT],
}

struct Vm<'a> {
    // Roots
    stack: Object,
    program_counter: Object,
    r#false: Object,

    position: usize,
    input: &'a [u8],

    heap: &'a mut [Object; HEAP_SIZE],
    symbol_table: Object,

    allocation_index: usize,
    allocation_limit: usize,
    #[allow(dead_code)]
    scan: *const Object,
}

fn list_tail(vm: &mut Vm, list: usize, index: Object) -> usize {
    if unwrap_object(&index) == 0 {
        list
    } else {
        let rib = get_rib(vm, Object::Number(list as u64));
        let cdr = unwrap_object(&rib.fields[1]);
        list_tail(vm, cdr as usize, Object::Number(unwrap_object(&index) - 1))
    }
}

fn symbol_ref(vm: &mut Vm, n: Object) -> usize {
    let sym_table_idx = unwrap_object(&vm.symbol_table) as usize;
    list_tail(vm, sym_table_idx, n)
}

fn get_operand(vm: &mut Vm, object: Object) -> Object {
    let rib = if !is_rib(&object) {
        Object::Rib(list_tail(vm, unwrap_object(&vm.stack) as usize, object) as u64)
    } else {
        object
    };

    get_rib(vm, rib).fields[0]
}

fn proc(vm: &mut Vm) -> Object {
    let cdr = get_cdr(vm, vm.program_counter);
    get_operand(vm, cdr)
}

fn code(vm: &mut Vm) -> Object {
    let proc_obj = proc(vm);
    get_car(vm, proc_obj)
}

fn get_continuation(vm: &mut Vm) -> Object {
    let mut stack = vm.stack;

    while unwrap_object(&get_tag(vm, stack)) != 0 {
        stack = get_cdr(vm, stack);
    }

    stack
}

fn get_int(vm: &mut Vm, n: i64) -> i64 {
    let x = get_code(vm);
    let n = n * 46;

    if x < 46 {
        n + x
    } else {
        get_int(vm, n + x - 46)
    }
}

fn get_code(vm: &mut Vm) -> i64 {
    let x: i64 = i64::from(get_byte(vm)) - 35;

    if x < 0 {
        57
    } else {
        x
    }
}

fn get_byte(vm: &mut Vm) -> u8 {
    let byte = vm.input[vm.position];
    vm.position += 1;
    byte
}

fn get_car_index(index: Object) -> usize {
    // TODO Check this conversion
    unwrap_object(&index).try_into().unwrap()
}

fn get_cdr_index(index: Object) -> usize {
    // TODO Check this conversion
    (unwrap_object(&index) + 1).try_into().unwrap()
}

fn get_tag_index(index: Object) -> usize {
    // TODO Check this conversion
    (unwrap_object(&index) + 2).try_into().unwrap()
}

fn get_tos_index(vm: &mut Vm) -> usize {
    get_car_index(vm.stack)
}

fn get_car(vm: &mut Vm, index: Object) -> Object {
    get_rib(vm, index).fields[0]
}

fn get_cdr(vm: &mut Vm, index: Object) -> Object {
    get_rib(vm, index).fields[1]
}

fn get_tag(vm: &mut Vm, index: Object) -> Object {
    get_rib(vm, index).fields[2]
}

fn get_true(vm: &mut Vm) -> Object {
    get_car(vm, vm.r#false)
}

fn get_nil(vm: &mut Vm) -> Object {
    get_cdr(vm, vm.r#false)
}

fn get_boolean(vm: &mut Vm, value: bool) -> Object {
    if value {
        get_true(vm)
    } else {
        vm.r#false
    }
}

fn get_rib<'a>(vm: &'a mut Vm, index: Object) -> Rib<'a> {
    let index = unwrap_object(&index) as usize;

    Rib {
        fields: vm.heap[index..index + RIB_FIELD_COUNT].try_into().unwrap(),
    }
}

fn build_symbol_table(vm: &mut Vm) {
    let mut n = get_int(vm, 0);

    while n > 0 {
        n -= 1;
        let nil = get_nil(vm);
        vm.symbol_table = create_symbol(vm, nil);
    }

    let mut name = get_nil(vm);

    loop {
        let c = get_byte(vm);

        if c == 44 {
            vm.symbol_table = create_symbol(vm, name);
            name = get_nil(vm);
            continue;
        }

        if c == 59 {
            break;
        }

        name = allocate_rib(vm, tag_number(c as i64), name, PAIR_TAG);
    }

    vm.symbol_table = create_symbol(vm, name);
}

fn set_global(vm: &mut Vm, object: Object) {
    let index = Object::Number(get_car_index(vm.symbol_table) as u64);
    vm.heap[get_car_index(index)] = object;
    vm.symbol_table = get_cdr(vm, vm.symbol_table);
}

fn decode(vm: &mut Vm) {
    let weights = [20, 30, 0, 10, 11, 4];

    #[allow(unused_assignments)]
    let mut n = Object::Number(0);
    #[allow(unused_assignments)]
    let mut d = 0;
    #[allow(unused_assignments)]
    let mut op: i64 = -1;

    loop {
        let x = get_code(vm);
        n = tag_number(x);
        op = -1;

        while unwrap_object(&n) > {
            op += 1;
            d = weights[op as usize];
            d + 2
        } {
            n = Object::Number(unwrap_object(&n) - (d + 3));
        }

        if x > 90 {
            op = INSTRUCTION_IF as i64;
            n = vm.pop();
        } else {
            if op == 0 {
                vm.push(NUMBER_0, NUMBER_0);
            }

            if unwrap_object(&n) >= d {
                n = if unwrap_object(&n) == d {
                    tag_number(get_int(vm, 0))
                } else {
                    let num = (unwrap_object(&n) - d - 1) as i64;
                    let int = get_int(vm, num);
                    Object::Rib(symbol_ref(vm, tag_number(int)) as u64)
                }
            } else {
                n = if op < 3 {
                    Object::Rib(symbol_ref(vm, n) as u64)
                } else {
                    n
                }
            }

            if op > 4 {
                let obj = vm.pop();
                let rib2 = allocate_rib2(vm, n, NUMBER_0, obj);
                let nil = get_nil(vm);
                n = allocate_rib(vm, rib2, nil, CLOSURE_TAG);

                if unwrap_object(&vm.stack) == unwrap_object(&NUMBER_0) {
                    break;
                }
            } else if op > 0 {
                op -= 1;
            } else {
                op = 0;
            }
        }

        let c = allocate_rib(vm, Object::Number(op as u64), n, Object::Number(0));
        vm.heap[get_cdr_index(c)] = vm.heap[get_tos_index(vm)];
        vm.heap[get_tos_index(vm)] = c;
    }

    let car = get_car(vm, n);
    let tag = get_tag(vm, car);

    vm.program_counter = get_tag(vm, tag);
}

fn setup_stack(vm: &mut Vm) {
    vm.push(NUMBER_0, PAIR_TAG);
    vm.push(NUMBER_0, PAIR_TAG);

    let first = get_cdr(vm, vm.stack);
    vm.heap[get_cdr_index(vm.stack)] = NUMBER_0;
    vm.heap[get_tag_index(vm.stack)] = first;

    vm.heap[get_car_index(first)] = tag_number(INSTRUCTION_HALT as i64);
    vm.heap[get_cdr_index(first)] = NUMBER_0;
    vm.heap[get_tag_index(first)] = PAIR_TAG;
}

fn run(vm: &mut Vm) {
    loop {
        let instruction = get_car(vm, vm.program_counter);
        println!("{}", unwrap_object(&instruction) as i64);
        vm.advance_program_counter();
        let instruction = get_car(vm, vm.program_counter);
        println!("{}", unwrap_object(&instruction) as i64);

        match unwrap_object(&instruction) {
            INSTRUCTION_HALT => exit(None),
            INSTRUCTION_APPLY => {
                let jump = get_tag(vm, vm.program_counter) == NUMBER_0;

                if !is_rib(&code(vm)) {
                    let code_obj = code(vm);

                    vm.operate_primitive(
                        Primitive::from_u64(unwrap_object(&code_obj)).expect("valid primitive"),
                    );

                    if jump {
                        vm.program_counter = get_continuation(vm);
                        vm.heap[get_cdr_index(vm.stack)] = get_car(vm, vm.program_counter);
                    }

                    vm.advance_program_counter();
                } else {
                    let code_object = code(vm);
                    let argc = get_car(vm, code_object);
                    vm.heap[get_car_index(vm.program_counter)] = code(vm);

                    let proc_obj = proc(vm);
                    let mut s2 = allocate_rib(vm, NUMBER_0, proc_obj, PAIR_TAG);

                    for _ in 0..unwrap_object(&argc) {
                        let pop_obj = vm.pop();
                        s2 = allocate_rib(vm, pop_obj, s2, PAIR_TAG);
                    }

                    let c2 =
                        Object::Number(list_tail(vm, unwrap_object(&s2) as usize, argc) as u64);

                    if jump {
                        let k = get_continuation(vm);
                        vm.heap[get_car_index(c2)] = get_car(vm, k);
                        vm.heap[get_tag_index(c2)] = get_tag(vm, k);
                    } else {
                        vm.heap[get_car_index(c2)] = vm.stack;
                        vm.heap[get_tag_index(c2)] = get_tag(vm, vm.program_counter);
                    }

                    vm.stack = s2;

                    let new_pc = get_car(vm, vm.program_counter);
                    vm.heap[get_car_index(vm.program_counter)] = instruction;
                    vm.program_counter = get_tag(vm, new_pc);
                }
            }
            INSTRUCTION_SET => {
                let x = vm.pop();

                let rib = if !is_rib(&get_cdr(vm, vm.program_counter)) {
                    let cdr_obj = get_cdr(vm, vm.program_counter);
                    let stack = unwrap_object(&vm.stack) as usize;
                    Object::Rib(list_tail(vm, stack, cdr_obj) as u64)
                } else {
                    get_cdr(vm, vm.program_counter)
                };

                vm.heap[get_car_index(rib)] = x;

                vm.advance_program_counter();
            }
            INSTRUCTION_GET => {
                let proc_obj = proc(vm);
                vm.push(proc_obj, PAIR_TAG);
                vm.advance_program_counter();
            }
            INSTRUCTION_CONSTANT => {
                let object = get_cdr(vm, vm.program_counter);
                vm.push(object, PAIR_TAG);
                vm.advance_program_counter();
            }
            INSTRUCTION_IF => {
                let p = unwrap_object(&vm.pop());
                let false_unwrapped = unwrap_object(&vm.r#false);
                if p != false_unwrapped {
                    vm.program_counter = get_cdr(vm, vm.program_counter);
                } else {
                    vm.program_counter = get_tag(vm, vm.program_counter);
                }
            }
            _ => exit(Some(ExitCode::IllegalInstruction)),
        }
    }
}

fn create_symbol(vm: &mut Vm, name: Object) -> Object {
    let len = list_length(vm, name);
    let list = allocate_rib(vm, name, len, STRING_TAG);
    let symbol = allocate_rib(vm, vm.r#false, list, SYMBOL_TAG);
    allocate_rib(vm, symbol, vm.symbol_table, PAIR_TAG)
}

fn allocate_rib(vm: &mut Vm, car: Object, cdr: Object, tag: Object) -> Object {
    vm.push(car, cdr);
    let stack = get_cdr(vm, vm.stack);
    let allocated = vm.stack;

    vm.heap[get_cdr_index(allocated)] = vm.heap[get_tag_index(allocated)];
    vm.heap[get_tag_index(allocated)] = tag;

    vm.stack = stack;

    Object::Rib(unwrap_object(&allocated))
}

fn allocate_rib2(vm: &mut Vm, car: Object, cdr: Object, tag: Object) -> Object {
    vm.push(car, tag);
    let stack = get_cdr(vm, vm.stack);
    let allocated = vm.stack;

    vm.heap[get_cdr_index(allocated)] = cdr;

    vm.stack = stack;

    Object::Rib(unwrap_object(&allocated))
}

fn list_length(vm: &mut Vm, mut list: Object) -> Object {
    let mut len = 0;

    while is_rib(&list) && unwrap_object(&get_tag(vm, list)) == 0 {
        len += 1;
        list = get_cdr(vm, list)
    }

    tag_number(len)
}

#[derive(Clone, Copy, FromPrimitive)]
enum Primitive {
    Rib,
    Id,
    Pop,
    Skip,
    Close,
    IsRib,
    Field0,
    Field1,
    Field2,
    SetField0,
    SetField1,
    SetField2,
    Equal,
    LessThan,
    Add,
    Subtract,
    Multiply,
    Divide,
    GetC,
    PutC,
}

impl<'a> Vm<'a> {
    fn advance_program_counter(&mut self) {
        self.program_counter = get_tag(self, self.program_counter);
    }

    fn pop(&mut self) -> Object {
        let value = get_car(self, self.stack);
        self.stack = get_cdr(self, self.stack);
        value
    }

    fn push(&mut self, car: Object, tag: Object) {
        self.heap[self.allocation_index] = car;
        self.allocation_index += 1;

        self.heap[self.allocation_index] = self.stack;
        self.allocation_index += 1;

        self.heap[self.allocation_index] = tag;
        self.allocation_index += 1;

        self.stack = tag_rib((self.allocation_index - RIB_FIELD_COUNT) as u64);

        if self.allocation_index == self.allocation_limit {
            // TODO Run GC.
        }
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
                let mut tos_index = get_tos_index(self);
                let x = get_car(self, Object::Number(tos_index as u64));
                let y = get_cdr(self, self.stack);
                tos_index = get_tos_index(self);
                self.heap[tos_index] = allocate_rib(self, x, y, CLOSURE_TAG);
            }
            Primitive::IsRib => {
                let x = self.pop();
                let cond = is_rib(&x);
                let boolean = get_boolean(self, cond);
                self.push(boolean, PAIR_TAG);
            }
            Primitive::Field0 => {
                let x = self.pop();
                let car = get_car(self, x);
                self.push(car, PAIR_TAG);
            }
            Primitive::Field1 => {
                let x = self.pop();
                let cdr = get_cdr(self, x);
                self.push(cdr, PAIR_TAG);
            }
            Primitive::Field2 => {
                let x = self.pop();
                let tag = get_tag(self, x);
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

                print!("{}", unwrap_object(&x) as u8 as char);
            }
        }
    }

    fn operate_binary(&mut self, operate: fn(u64, u64) -> u64) {
        let x = self.pop();
        let y = self.pop();

        self.push(
            Object::Number(operate(unwrap_object(&x), unwrap_object(&y))),
            PAIR_TAG,
        );
    }

    fn operate_comparison(&mut self, operate: fn(u64, u64) -> bool) {
        let x = self.pop();
        let y = self.pop();
        let condition = get_boolean(self, operate(unwrap_object(&x), unwrap_object(&y)));

        self.push(condition, PAIR_TAG);
    }

    #[allow(dead_code)]
    fn collect_garbages(&mut self) {
        let to_space = if self.allocation_limit == HEAP_MIDDLE {
            HEAP_MIDDLE
        } else {
            HEAP_BOTTOM
        };

        self.allocation_limit = to_space + SPACE_SIZE as usize;
        self.allocation_index = to_space;

        // TODO Finish GC
    }
}

fn main() {
    // @@(replace ");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y" (encode 92)
    let input = String::from(");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y");
    // )@@
    let mut heap = [NUMBER_0; HEAP_SIZE];
    let scan = &heap[0] as *const Object;

    let mut vm = Vm {
        stack: NUMBER_0,
        program_counter: NUMBER_0,
        r#false: NUMBER_0,

        position: 0,
        input: input.as_bytes(),
        heap: &mut heap,
        symbol_table: NUMBER_0,

        allocation_index: HEAP_BOTTOM,
        allocation_limit: HEAP_MIDDLE,
        scan,
    };

    let init_0 = allocate_rib(&mut vm, NUMBER_0, NUMBER_0, SINGLETON_TAG);
    vm.r#false = allocate_rib(&mut vm, init_0, init_0, SINGLETON_TAG);

    build_symbol_table(&mut vm);
    decode(&mut vm);

    let symbol_table = vm.symbol_table;
    let rib = allocate_rib(&mut vm, NUMBER_0, symbol_table, CLOSURE_TAG);
    let r#false = vm.r#false;
    let r#true = get_true(&mut vm);
    let nil = get_nil(&mut vm);

    set_global(&mut vm, rib);
    set_global(&mut vm, r#false);
    set_global(&mut vm, r#true);
    set_global(&mut vm, nil);

    setup_stack(&mut vm);

    run(&mut vm);
}
