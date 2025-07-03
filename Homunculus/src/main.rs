use camino::Utf8Path;
use compiler::codegen::common::Scheduler;
use compiler::codegen::context::CodegenCx;
use compiler::compiler::ast::ast::Root;
use compiler::compiler::parse::parser::{parse, parse_save_tokens};
use compiler::compiler::parse::syntax::TokenKind;
use eyre::{eyre, Context, Report, Result};
use fuzzing::fuzz;
use std::fs::File;
use std::io::Read;
use std::io::{self};
use std::{env, path};

static DEFAULT_PROGRAM_FILE: &str = "./forward-progress/validation/MCProgram.tla";
static DEFAULT_SCHEDULER: Scheduler = Scheduler::OBE;
static DEFAULT_WORKGROUP_SIZE: u32 = 1;
static DEFAULT_SUBGROUP_SIZE: u32 = 1;
static DEFAULT_NUM_WORKGROUPS: u32 = 2;

fn read_spir_v_file(file_path: &str) -> io::Result<String> {
    let mut file = File::open(file_path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}

#[derive(Debug)]
enum Command {
    Fuzz,
    Compile,
}
impl From<&str> for Command {
    fn from(s: &str) -> Self {
        match s {
            "fuzz" => Command::Fuzz,
            "compile" => Command::Compile,
            _ => panic!("Invalid command"),
        }
    }
}

fn compile(
    spirv_code: &str,
    sub_group_size: u32,
    work_group_size: u32,
    num_workgroup: u32,
    scheduler: Scheduler,
    path: &str,
) -> Result<()> {
    let (parse, tokens) = parse_save_tokens(spirv_code);
    let syntax = parse.syntax();
    // println!("{:?}", tokens);
    let map = parse.make_token_map();
    // let op_func_end = syntax.last_token().unwrap();
    // println!("{:?}",tokens);
    // println!("{:?}",op_func_end);
    // println!("{}",map[&op_func_end]);
    let mut codegen_ctx = CodegenCx::new(sub_group_size, work_group_size, num_workgroup, scheduler);
    let program = codegen_ctx.generate_code_with_origin_line_number(syntax, &map, &tokens);
    // for instruction in &program.instructions {
    //     println!("{:?}", instruction);
    // }
    let utf8_path = Utf8Path::new(path);
    program.write_to_file(&utf8_path)
}

fn main() {
    // Get the command-line arguments
    let args: Vec<String> = env::args().collect();

    if args.len() > 5 {
        eprintln!(
            "Usage: {} <compile/fuzz> <spirv_dis> option<validation/path>",
            args[0]
        );
        return;
    }
    let command = Command::from(args[1].as_str());
    let filename = &args[2];
    let path = if args.len() == 4 {
        &args[3]
    } else {
        DEFAULT_PROGRAM_FILE
    };
    match command {
        Command::Compile => {
            // Read the GLSL file
            match read_spir_v_file(filename) {
                Ok(spirv_code) => {
                    compile(
                        &spirv_code,
                        DEFAULT_SUBGROUP_SIZE,
                        DEFAULT_WORKGROUP_SIZE,
                        DEFAULT_NUM_WORKGROUPS,
                        DEFAULT_SCHEDULER.clone(),
                        path,
                    )
                    .unwrap();
                }
                Err(e) => eprintln!("Failed to read SPIR-V file '{}': {}", filename, e),
            }
        }
        Command::Fuzz => match read_spir_v_file(filename) {
            Ok(spirv_code) => {
                fuzz(
                    &spirv_code,
                    DEFAULT_SUBGROUP_SIZE,
                    DEFAULT_WORKGROUP_SIZE,
                    DEFAULT_NUM_WORKGROUPS,
                    DEFAULT_SCHEDULER.clone(),
                    &filename,
                )
                .unwrap();
            }
            Err(e) => eprintln!("Failed to read SPIR-V file '{}': {}", filename, e),
        },
    }
}
