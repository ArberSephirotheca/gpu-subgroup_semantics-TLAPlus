pub mod mutation;

use compiler::codegen::common::Scheduler;
use compiler::codegen::context::CodegenCx;
use compiler::compiler::parse::parser::parse_save_tokens;
use eyre::Result;

use crate::mutation::MutCtx;

pub fn fuzz(
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
    let symbol_table = codegen_ctx.get_variable_table();
    // for instruction in &program.instructions {
    //     println!("{:?}", instruction);
    // }
    MutCtx::new(program, path.to_string(), symbol_table).mutation().write_to_file()
}
