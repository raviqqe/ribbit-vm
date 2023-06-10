use std::{
    convert::TryInto,
    io::{stdin, Read},
    process,
};

const RIB_FIELD_COUNT: usize = 3;
const MAX_OBJECT_COUNT: u32 = 30_000;
const SPACE_SIZE: u32 = MAX_OBJECT_COUNT * RIB_FIELD_COUNT as u32;
const HEAP_SIZE: usize = SPACE_SIZE as usize * 2;
const HEAP_BOTTOM: usize = 0;
const HEAP_MIDDLE: usize = HEAP_SIZE / 2;
#[allow(dead_code)]
const HEAP_TOP: usize = HEAP_SIZE - 1; // Last valid index

const NUMBER_0: Object = tag_number(0);
const PAIR_TAG: Object = tag_number(0);
const CLOSURE_TAG: Object = tag_number(1);
const SYMBOL_TAG: Object = tag_number(2);
const STRING_TAG: Object = tag_number(3);
const SINGLETON_TAG: Object = tag_number(5);

const INSTR_APPLY: i64 = 0;
const INSTR_SET: i64 = 1;
const INSTR_GET: i64 = 2;
const INSTR_CONSTANT: i64 = 3;
const INSTR_IF: i64 = 4;
const INSTRUCTION_HALT: i64 = 5;

#[repr(i32)]
enum ExitCode {
    IllegalInstructtion = 6,
}

fn exit(code: Option<ExitCode>) {
    process::exit(code.map(|code| code as i32).unwrap_or(0));
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

    alloc: usize,
    alloc_limit: usize,
    #[allow(dead_code)]
    scan: *const Object,
}

fn advance_program_counter(environment: &mut Environment) {
    environment.program_counter = get_tag(environment, environment.program_counter);
}

fn list_tail(env: &mut Environment, lst: usize, i: Object) -> usize {
    if unwrap_object(&i) == 0 {
        lst
    } else {
        let rib = get_rib(env, Object::Number(lst as u64));
        let cdr = unwrap_object(&rib.fields[1]);
        list_tail(env, cdr as usize, Object::Number(unwrap_object(&i) - 1))
    }
}

fn symbol_ref(env: &mut Environment, n: Object) -> usize {
    let sym_table_idx = unwrap_object(&env.symbol_table) as usize;
    list_tail(env, sym_table_idx, n)
}

fn get_operand(environment: &mut Environment, object: Object) -> Object {
    let rib_object = if !is_rib(&object) {
        Object::Rib(list_tail(
            environment,
            unwrap_object(&environment.stack) as usize,
            object,
        ) as u64)
    } else {
        object
    };

    let rib = get_rib(environment, rib_object);
    rib.fields[0]
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
    // TODO: Check this conversion
    unwrap_object(&index).try_into().unwrap()
}

fn get_cdr_index(index: Object) -> usize {
    // TODO: Check this conversion
    (unwrap_object(&index) + 1).try_into().unwrap()
}

fn get_tag_index(index: Object) -> usize {
    // TODO: Check this conversion
    (unwrap_object(&index) + 2).try_into().unwrap()
}

fn get_tos_index(env: &mut Environment) -> usize {
    get_car_index(env.stack)
}

fn get_car(env: &mut Environment, index: Object) -> Object {
    let rib = get_rib(env, index);
    rib.fields[0]
}

fn get_cdr(env: &mut Environment, index: Object) -> Object {
    let rib = get_rib(env, index);
    rib.fields[1]
}

fn get_tag(env: &mut Environment, index: Object) -> Object {
    let rib = get_rib(env, index);
    rib.fields[2]
}

fn get_true(env: &mut Environment) -> Object {
    get_car(env, env.r#false)
}

fn get_nil(env: &mut Environment) -> Object {
    get_cdr(env, env.r#false)
}

fn get_boolean(env: &mut Environment, cond: bool) -> Object {
    if cond {
        get_true(env)
    } else {
        env.r#false
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

        alloc: HEAP_BOTTOM,
        alloc_limit: HEAP_MIDDLE,
        scan,
    };

    let init_0 = allocate_rib(&mut environment, NUMBER_0, NUMBER_0, SINGLETON_TAG);
    environment.r#false = allocate_rib(&mut environment, init_0, init_0, SINGLETON_TAG);

    build_symbol_table(&mut environment);
    decode(&mut environment);

    let sym_table = environment.symbol_table;
    let rib = allocate_rib(&mut environment, NUMBER_0, sym_table, CLOSURE_TAG);
    let fals = environment.r#false;
    let tru = get_true(&mut environment);
    let nil = get_nil(&mut environment);

    set_global(&mut environment, rib);
    set_global(&mut environment, fals);
    set_global(&mut environment, tru);
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

    let mut accum = get_nil(environment);

    loop {
        let c = get_byte(environment);

        if c == 44 {
            environment.symbol_table = create_symbol(environment, accum);
            accum = get_nil(environment);
            continue;
        }

        if c == 59 {
            break;
        }

        accum = allocate_rib(environment, tag_number(c as i64), accum, PAIR_TAG);
    }

    environment.symbol_table = create_symbol(environment, accum);
}

fn set_global(env: &mut Environment, c: Object) {
    let car_index = Object::Number(get_car_index(env.symbol_table) as u64);
    env.heap[get_car_index(car_index)] = c;
    env.symbol_table = get_cdr(env, env.symbol_table);
}

fn decode(env: &mut Environment) {
    let weights = [20, 30, 0, 10, 11, 4];

    #[allow(unused_assignments)]
    let mut n = Object::Number(0);
    #[allow(unused_assignments)]
    let mut d = 0;
    #[allow(unused_assignments)]
    let mut op: i64 = -1;

    loop {
        let x = get_code(env);
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
            op = INSTR_IF;
            n = pop(env);
        } else {
            if op == 0 {
                push2(env, NUMBER_0, NUMBER_0);
            }

            if unwrap_object(&n) >= d {
                n = if unwrap_object(&n) == d {
                    tag_number(get_int(env, 0))
                } else {
                    let num = (unwrap_object(&n) - d - 1) as i64;
                    let int = get_int(env, num);
                    Object::Rib(symbol_ref(env, tag_number(int)) as u64)
                }
            } else {
                n = if op < 3 {
                    Object::Rib(symbol_ref(env, n) as u64)
                } else {
                    n
                }
            }

            if op > 4 {
                let obj = pop(env);
                let rib2 = alloc_rib2(env, n, NUMBER_0, obj);
                let nil = get_nil(env);
                n = allocate_rib(env, rib2, nil, CLOSURE_TAG);

                if unwrap_object(&env.stack) == unwrap_object(&NUMBER_0) {
                    break;
                }
            } else if op > 0 {
                op -= 1;
            } else {
                op = 0;
            }
        }

        let c = allocate_rib(env, Object::Number(op as u64), n, Object::Number(0));
        env.heap[get_cdr_index(c)] = env.heap[get_tos_index(env)];
        env.heap[get_tos_index(env)] = c;
    }

    let car = get_car(env, n);
    let tag = get_tag(env, car);
    env.program_counter = get_tag(env, tag);
}

fn setup_stack(environment: &mut Environment) {
    push2(environment, NUMBER_0, PAIR_TAG);
    push2(environment, NUMBER_0, PAIR_TAG);

    let first = get_cdr(environment, environment.stack);
    environment.heap[get_cdr_index(environment.stack)] = NUMBER_0;
    environment.heap[get_tag_index(environment.stack)] = first;

    environment.heap[get_car_index(first)] = tag_number(INSTRUCTION_HALT);
    environment.heap[get_cdr_index(first)] = NUMBER_0;
    environment.heap[get_tag_index(first)] = PAIR_TAG;
}

fn run(environment: &mut Environment) {
    loop {
        let instr = get_car(environment, environment.program_counter);
        println!("{}", unwrap_object(&instr) as i64);
        advance_program_counter(environment);
        let instr = get_car(environment, environment.program_counter);
        println!("{}", unwrap_object(&instr) as i64);

        match unwrap_object(&instr) as i64 {
            INSTRUCTION_HALT => exit(None),
            INSTR_APPLY => {
                let jump = get_tag(environment, environment.program_counter) == NUMBER_0;

                if !is_rib(&code(environment)) {
                    let code_obj = code(environment);

                    primitive(environment, unwrap_object(&code_obj) as i64);

                    if jump {
                        environment.program_counter = get_continuation(environment);
                        environment.heap[get_cdr_index(environment.stack)] =
                            get_car(environment, environment.program_counter);
                    }

                    advance_program_counter(environment);
                } else {
                    let code_object = code(environment);
                    let argc = get_car(environment, code_object);
                    environment.heap[get_car_index(environment.program_counter)] =
                        code(environment);

                    let proc_obj = proc(environment);
                    let mut s2 = allocate_rib(environment, NUMBER_0, proc_obj, PAIR_TAG);

                    for _ in 0..unwrap_object(&argc) {
                        let pop_obj = pop(environment);
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
                    environment.heap[get_car_index(environment.program_counter)] = instr;
                    environment.program_counter = get_tag(environment, new_pc);
                }
            }

            INSTR_SET => {
                let x = pop(environment);

                let rib = if !is_rib(&get_cdr(environment, environment.program_counter)) {
                    let cdr_obj = get_cdr(environment, environment.program_counter);
                    let stack = unwrap_object(&environment.stack) as usize;
                    Object::Rib(list_tail(environment, stack, cdr_obj) as u64)
                } else {
                    get_cdr(environment, environment.program_counter)
                };

                environment.heap[get_car_index(rib)] = x;

                advance_program_counter(environment);
            }

            INSTR_GET => {
                let proc_obj = proc(environment);
                push2(environment, proc_obj, PAIR_TAG);
                advance_program_counter(environment);
            }

            INSTR_CONSTANT => {
                let cdr_obj = get_cdr(environment, environment.program_counter);
                push2(environment, cdr_obj, PAIR_TAG);
                advance_program_counter(environment);
            }

            INSTR_IF => {
                let p = unwrap_object(&pop(environment));
                let false_unwraped = unwrap_object(&environment.r#false);
                if p != false_unwraped {
                    environment.program_counter = get_cdr(environment, environment.program_counter);
                } else {
                    environment.program_counter = get_tag(environment, environment.program_counter);
                }
            }

            _ => {
                exit(Some(ExitCode::IllegalInstructtion));
            }
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
    push2(environment, car, cdr);
    let old_stack = get_cdr(environment, environment.stack);
    let allocated = environment.stack;

    environment.heap[get_cdr_index(allocated)] = environment.heap[get_tag_index(allocated)];
    environment.heap[get_tag_index(allocated)] = tag;

    environment.stack = old_stack;

    Object::Rib(unwrap_object(&allocated))
}

fn alloc_rib2(env: &mut Environment, car: Object, cdr: Object, tag: Object) -> Object {
    push2(env, car, tag);
    let old_stack = get_cdr(env, env.stack);
    let allocated = env.stack;

    env.heap[get_cdr_index(allocated)] = cdr;

    env.stack = old_stack;

    Object::Rib(unwrap_object(&allocated))
}

fn pop(env: &mut Environment) -> Object {
    let x = get_car(env, env.stack);
    env.stack = get_cdr(env, env.stack);
    x
}

fn push2(environment: &mut Environment, car: Object, tag: Object) {
    environment.heap[environment.alloc] = car;
    environment.alloc += 1;

    environment.heap[environment.alloc] = environment.stack;
    environment.alloc += 1;

    environment.heap[environment.alloc] = tag;
    environment.alloc += 1;

    environment.stack = tag_rib((environment.alloc - RIB_FIELD_COUNT) as u64);

    if environment.alloc == environment.alloc_limit {
        // TODO: GC
    }
}

fn list_length(env: &mut Environment, list: Object) -> Object {
    let mut len: i64 = 0;
    let mut list = list;

    while is_rib(&list) && unwrap_object(&get_tag(env, list)) == 0 {
        len += 1;
        list = get_cdr(env, list)
    }

    tag_number(len)
}

// TODO: Finish GC
#[allow(dead_code)]
fn gc(env: &mut Environment) {
    let to_space = if env.alloc_limit == HEAP_MIDDLE {
        HEAP_MIDDLE
    } else {
        HEAP_BOTTOM
    };
    env.alloc_limit = to_space + SPACE_SIZE as usize;

    env.alloc = to_space;
}

fn primitive(environment: &mut Environment, primitive: i64) {
    match primitive {
        // rib
        0 => {
            let rib = allocate_rib(environment, NUMBER_0, NUMBER_0, NUMBER_0);
            environment.heap[get_car_index(rib)] = pop(environment);
            environment.heap[get_cdr_index(rib)] = pop(environment);
            environment.heap[get_tag_index(rib)] = pop(environment);
            push2(environment, rib, PAIR_TAG);
        }

        // id
        1 => {
            let x = pop(environment);
            push2(environment, x, PAIR_TAG);
        }

        // pop
        2 => {
            pop(environment);
            // TODO: Check what is the meaning of true?
        }

        // skip
        3 => {
            let x = pop(environment);
            pop(environment);
            push2(environment, x, PAIR_TAG);
        }

        // close
        4 => {
            let mut tos_index = get_tos_index(environment);
            let x = get_car(environment, Object::Number(tos_index as u64));
            let y = get_cdr(environment, environment.stack);
            tos_index = get_tos_index(environment);
            environment.heap[tos_index] = allocate_rib(environment, x, y, CLOSURE_TAG);
        }

        // is rib?
        5 => {
            let x = pop(environment);
            let cond = is_rib(&x);
            let boolean = get_boolean(environment, cond);
            push2(environment, boolean, PAIR_TAG);
        }

        // field0
        6 => {
            let x = pop(environment);
            let car = get_car(environment, x);
            push2(environment, car, PAIR_TAG);
        }

        // field1
        7 => {
            let x = pop(environment);
            let cdr = get_cdr(environment, x);
            push2(environment, cdr, PAIR_TAG);
        }

        // field2
        8 => {
            let x = pop(environment);
            let tag = get_tag(environment, x);
            push2(environment, tag, PAIR_TAG)
        }

        // set field0
        9 => {
            let x = pop(environment);
            let y = pop(environment);
            environment.heap[get_car_index(x)] = y;
            push2(environment, y, PAIR_TAG);
        }

        // set field1
        10 => {
            let x = pop(environment);
            let y = pop(environment);
            environment.heap[get_cdr_index(x)] = y;
            push2(environment, y, PAIR_TAG);
        }

        // set field2
        11 => {
            let x = pop(environment);
            let y = pop(environment);
            environment.heap[get_tag_index(x)] = y;
            push2(environment, y, PAIR_TAG);
        }

        // eq
        12 => {
            let x = pop(environment);
            let y = pop(environment);
            let cond = unwrap_object(&x) == unwrap_object(&y);
            let boolean = get_boolean(environment, cond);
            push2(environment, boolean, PAIR_TAG);
        }

        // lt
        13 => {
            let x = pop(environment);
            let y = pop(environment);
            let cond = unwrap_object(&x) < unwrap_object(&y);
            let boolean = get_boolean(environment, cond);
            push2(environment, boolean, PAIR_TAG);
        }

        // add
        14 => {
            let x = pop(environment);
            let y = pop(environment);
            let num_x = unwrap_object(&x);
            let num_y = unwrap_object(&y);
            let add = Object::Number(num_x + num_y);
            push2(environment, add, PAIR_TAG);
        }

        // sub
        15 => {
            let x = pop(environment);
            let y = pop(environment);
            let num_x = unwrap_object(&x);
            let num_y = unwrap_object(&y);
            let sub = Object::Number(num_x - num_y);
            push2(environment, sub, PAIR_TAG);
        }

        // mul
        16 => {
            let x = pop(environment);
            let y = pop(environment);
            let num_x = unwrap_object(&x);
            let num_y = unwrap_object(&y);
            let mul = Object::Number(num_x * num_y);
            push2(environment, mul, PAIR_TAG);
        }

        // div
        17 => {
            let x = pop(environment);
            let y = pop(environment);
            let num_x = unwrap_object(&x);
            let num_y = unwrap_object(&y);
            let div = Object::Number(num_x / num_y);
            push2(environment, div, PAIR_TAG);
        }

        // getc
        18 => {
            let mut buff: [u8; 1] = [0];
            // TODO
            stdin().read_exact(&mut buff).unwrap();
            let _read = buff[0];
        }

        // putc
        19 => {
            let x = pop(environment);
            let chr = unwrap_object(&x) as u8 as char;
            print!("{}", chr);
        }
        _ => exit(Some(ExitCode::IllegalInstructtion)),
    }
}
