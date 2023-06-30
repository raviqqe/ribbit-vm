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

struct Environment<'a> {
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

fn list_tail(env: &mut Environment, list: usize, index: Object) -> usize {
    if unwrap_object(&index) == 0 {
        list
    } else {
        let rib = get_rib(env, Object::Number(list as u64));
        let cdr = unwrap_object(&rib.fields[1]);
        list_tail(env, cdr as usize, Object::Number(unwrap_object(&index) - 1))
    }
}

fn symbol_ref(env: &mut Environment, n: Object) -> usize {
    let sym_table_idx = unwrap_object(&env.symbol_table) as usize;
    list_tail(env, sym_table_idx, n)
}

fn get_operand(environment: &mut Environment, object: Object) -> Object {
    let rib = if !is_rib(&object) {
        Object::Rib(list_tail(
            environment,
            unwrap_object(&environment.stack) as usize,
            object,
        ) as u64)
    } else {
        object
    };

    get_rib(environment, rib).fields[0]
}

fn proc(environment: &mut Environment) -> Object {
    let cdr = get_cdr(environment, environment.program_counter);
    get_operand(environment, cdr)
}

fn code(environment: &mut Environment) -> Object {
    let proc_obj = proc(environment);
    get_car(environment, proc_obj)
}

fn get_continuation(environment: &mut Environment) -> Object {
    let mut stack = environment.stack;

    while unwrap_object(&get_tag(environment, stack)) != 0 {
        stack = get_cdr(environment, stack);
    }

    stack
}

fn get_int(environment: &mut Environment, n: i64) -> i64 {
    let x = get_code(environment);
    let n = n * 46;

    if x < 46 {
        n + x
    } else {
        get_int(environment, n + x - 46)
    }
}

fn get_code(environment: &mut Environment) -> i64 {
    let x: i64 = i64::from(get_byte(environment)) - 35;

    if x < 0 {
        57
    } else {
        x
    }
}

fn get_byte(environment: &mut Environment) -> u8 {
    let byte = environment.input[environment.position];
    environment.position += 1;
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

fn get_tos_index(env: &mut Environment) -> usize {
    get_car_index(env.stack)
}

fn get_car(environment: &mut Environment, index: Object) -> Object {
    get_rib(environment, index).fields[0]
}

fn get_cdr(environment: &mut Environment, index: Object) -> Object {
    get_rib(environment, index).fields[1]
}

fn get_tag(environment: &mut Environment, index: Object) -> Object {
    get_rib(environment, index).fields[2]
}

fn get_true(environment: &mut Environment) -> Object {
    get_car(environment, environment.r#false)
}

fn get_nil(environment: &mut Environment) -> Object {
    get_cdr(environment, environment.r#false)
}

fn get_boolean(environment: &mut Environment, value: bool) -> Object {
    if value {
        get_true(environment)
    } else {
        environment.r#false
    }
}

fn get_rib<'a>(environment: &'a mut Environment, index: Object) -> Rib<'a> {
    let index = unwrap_object(&index) as usize;

    Rib {
        fields: environment.heap[index..index + RIB_FIELD_COUNT]
            .try_into()
            .unwrap(),
    }
}

fn main() {
    // @@(replace ");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y" (encode 92)
    let input = String::from(");'u?>vD?>vRD?>vRA?>vRA?>vR:?>vR=!(:lkm!':lkv6y");
    // )@@
    let mut heap = [NUMBER_0; HEAP_SIZE];
    let scan = &heap[0] as *const Object;

    let mut environment = Environment {
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

    let init_0 = allocate_rib(&mut environment, NUMBER_0, NUMBER_0, SINGLETON_TAG);
    environment.r#false = allocate_rib(&mut environment, init_0, init_0, SINGLETON_TAG);

    build_symbol_table(&mut environment);
    decode(&mut environment);

    let symbol_table = environment.symbol_table;
    let rib = allocate_rib(&mut environment, NUMBER_0, symbol_table, CLOSURE_TAG);
    let r#false = environment.r#false;
    let r#true = get_true(&mut environment);
    let nil = get_nil(&mut environment);

    set_global(&mut environment, rib);
    set_global(&mut environment, r#false);
    set_global(&mut environment, r#true);
    set_global(&mut environment, nil);

    setup_stack(&mut environment);

    run(&mut environment);
}

fn build_symbol_table(environment: &mut Environment) {
    let mut n = get_int(environment, 0);

    while n > 0 {
        n -= 1;
        let nil = get_nil(environment);
        environment.symbol_table = create_symbol(environment, nil);
    }

    let mut name = get_nil(environment);

    loop {
        let c = get_byte(environment);

        if c == 44 {
            environment.symbol_table = create_symbol(environment, name);
            name = get_nil(environment);
            continue;
        }

        if c == 59 {
            break;
        }

        name = allocate_rib(environment, tag_number(c as i64), name, PAIR_TAG);
    }

    environment.symbol_table = create_symbol(environment, name);
}

fn set_global(environment: &mut Environment, object: Object) {
    let index = Object::Number(get_car_index(environment.symbol_table) as u64);
    environment.heap[get_car_index(index)] = object;
    environment.symbol_table = get_cdr(environment, environment.symbol_table);
}

fn decode(environment: &mut Environment) {
    let weights = [20, 30, 0, 10, 11, 4];

    #[allow(unused_assignments)]
    let mut n = Object::Number(0);
    #[allow(unused_assignments)]
    let mut d = 0;
    #[allow(unused_assignments)]
    let mut op: i64 = -1;

    loop {
        let x = get_code(environment);
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
            n = environment.pop();
        } else {
            if op == 0 {
                environment.push(NUMBER_0, NUMBER_0);
            }

            if unwrap_object(&n) >= d {
                n = if unwrap_object(&n) == d {
                    tag_number(get_int(environment, 0))
                } else {
                    let num = (unwrap_object(&n) - d - 1) as i64;
                    let int = get_int(environment, num);
                    Object::Rib(symbol_ref(environment, tag_number(int)) as u64)
                }
            } else {
                n = if op < 3 {
                    Object::Rib(symbol_ref(environment, n) as u64)
                } else {
                    n
                }
            }

            if op > 4 {
                let obj = environment.pop();
                let rib2 = allocate_rib2(environment, n, NUMBER_0, obj);
                let nil = get_nil(environment);
                n = allocate_rib(environment, rib2, nil, CLOSURE_TAG);

                if unwrap_object(&environment.stack) == unwrap_object(&NUMBER_0) {
                    break;
                }
            } else if op > 0 {
                op -= 1;
            } else {
                op = 0;
            }
        }

        let c = allocate_rib(environment, Object::Number(op as u64), n, Object::Number(0));
        environment.heap[get_cdr_index(c)] = environment.heap[get_tos_index(environment)];
        environment.heap[get_tos_index(environment)] = c;
    }

    let car = get_car(environment, n);
    let tag = get_tag(environment, car);

    environment.program_counter = get_tag(environment, tag);
}

fn setup_stack(environment: &mut Environment) {
    environment.push(NUMBER_0, PAIR_TAG);
    environment.push(NUMBER_0, PAIR_TAG);

    let first = get_cdr(environment, environment.stack);
    environment.heap[get_cdr_index(environment.stack)] = NUMBER_0;
    environment.heap[get_tag_index(environment.stack)] = first;

    environment.heap[get_car_index(first)] = tag_number(INSTRUCTION_HALT as i64);
    environment.heap[get_cdr_index(first)] = NUMBER_0;
    environment.heap[get_tag_index(first)] = PAIR_TAG;
}

fn run(environment: &mut Environment) {
    loop {
        let instruction = get_car(environment, environment.program_counter);
        println!("{}", unwrap_object(&instruction) as i64);
        environment.advance_program_counter();
        let instruction = get_car(environment, environment.program_counter);
        println!("{}", unwrap_object(&instruction) as i64);

        match unwrap_object(&instruction) {
            INSTRUCTION_HALT => exit(None),
            INSTRUCTION_APPLY => {
                let jump = get_tag(environment, environment.program_counter) == NUMBER_0;

                if !is_rib(&code(environment)) {
                    let code_obj = code(environment);

                    environment.operate_primitive(
                        Primitive::from_u64(unwrap_object(&code_obj)).expect("valid primitive"),
                    );

                    if jump {
                        environment.program_counter = get_continuation(environment);
                        environment.heap[get_cdr_index(environment.stack)] =
                            get_car(environment, environment.program_counter);
                    }

                    environment.advance_program_counter();
                } else {
                    let code_object = code(environment);
                    let argc = get_car(environment, code_object);
                    environment.heap[get_car_index(environment.program_counter)] =
                        code(environment);

                    let proc_obj = proc(environment);
                    let mut s2 = allocate_rib(environment, NUMBER_0, proc_obj, PAIR_TAG);

                    for _ in 0..unwrap_object(&argc) {
                        let pop_obj = environment.pop();
                        s2 = allocate_rib(environment, pop_obj, s2, PAIR_TAG);
                    }

                    let c2 =
                        Object::Number(
                            list_tail(environment, unwrap_object(&s2) as usize, argc) as u64
                        );

                    if jump {
                        let k = get_continuation(environment);
                        environment.heap[get_car_index(c2)] = get_car(environment, k);
                        environment.heap[get_tag_index(c2)] = get_tag(environment, k);
                    } else {
                        environment.heap[get_car_index(c2)] = environment.stack;
                        environment.heap[get_tag_index(c2)] =
                            get_tag(environment, environment.program_counter);
                    }

                    environment.stack = s2;

                    let new_pc = get_car(environment, environment.program_counter);
                    environment.heap[get_car_index(environment.program_counter)] = instruction;
                    environment.program_counter = get_tag(environment, new_pc);
                }
            }
            INSTRUCTION_SET => {
                let x = environment.pop();

                let rib = if !is_rib(&get_cdr(environment, environment.program_counter)) {
                    let cdr_obj = get_cdr(environment, environment.program_counter);
                    let stack = unwrap_object(&environment.stack) as usize;
                    Object::Rib(list_tail(environment, stack, cdr_obj) as u64)
                } else {
                    get_cdr(environment, environment.program_counter)
                };

                environment.heap[get_car_index(rib)] = x;

                environment.advance_program_counter();
            }
            INSTRUCTION_GET => {
                let proc_obj = proc(environment);
                environment.push(proc_obj, PAIR_TAG);
                environment.advance_program_counter();
            }
            INSTRUCTION_CONSTANT => {
                let object = get_cdr(environment, environment.program_counter);
                environment.push(object, PAIR_TAG);
                environment.advance_program_counter();
            }
            INSTRUCTION_IF => {
                let p = unwrap_object(&environment.pop());
                let false_unwrapped = unwrap_object(&environment.r#false);
                if p != false_unwrapped {
                    environment.program_counter = get_cdr(environment, environment.program_counter);
                } else {
                    environment.program_counter = get_tag(environment, environment.program_counter);
                }
            }
            _ => exit(Some(ExitCode::IllegalInstruction)),
        }
    }
}

fn create_symbol(environment: &mut Environment, name: Object) -> Object {
    let len = list_length(environment, name);
    let list = allocate_rib(environment, name, len, STRING_TAG);
    let symbol = allocate_rib(environment, environment.r#false, list, SYMBOL_TAG);
    allocate_rib(environment, symbol, environment.symbol_table, PAIR_TAG)
}

fn allocate_rib(environment: &mut Environment, car: Object, cdr: Object, tag: Object) -> Object {
    environment.push(car, cdr);
    let stack = get_cdr(environment, environment.stack);
    let allocated = environment.stack;

    environment.heap[get_cdr_index(allocated)] = environment.heap[get_tag_index(allocated)];
    environment.heap[get_tag_index(allocated)] = tag;

    environment.stack = stack;

    Object::Rib(unwrap_object(&allocated))
}

fn allocate_rib2(environment: &mut Environment, car: Object, cdr: Object, tag: Object) -> Object {
    environment.push(car, tag);
    let stack = get_cdr(environment, environment.stack);
    let allocated = environment.stack;

    environment.heap[get_cdr_index(allocated)] = cdr;

    environment.stack = stack;

    Object::Rib(unwrap_object(&allocated))
}

fn list_length(environment: &mut Environment, mut list: Object) -> Object {
    let mut len = 0;

    while is_rib(&list) && unwrap_object(&get_tag(environment, list)) == 0 {
        len += 1;
        list = get_cdr(environment, list)
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

impl<'a> Environment<'a> {
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
