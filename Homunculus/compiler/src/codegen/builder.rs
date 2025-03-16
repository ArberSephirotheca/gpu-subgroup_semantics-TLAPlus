use crate::compiler::parse::symbol_table::VariableInfo;

use super::common::*;
use super::constant::*;
use eyre::{eyre, Result};
use smallvec::SmallVec;

#[derive(Default)]
pub struct ConstantBuilder {
    name: Option<String>,
    value: Option<ConstantType>,
}

impl ConstantBuilder {
    pub fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    pub fn value(mut self, value: ConstantType) -> Self {
        self.value = Some(value);
        self
    }

    pub fn build(self) -> Result<Constant> {
        Ok(Constant {
            name: self.name.ok_or_else(|| eyre!("Name is required"))?,
            value: self.value.ok_or_else(|| eyre!("Value is required"))?,
        })
    }
}

impl InstructionArgument {
    pub fn builder() -> InstructionArgumentBuilder {
        InstructionArgumentBuilder::default()
    }
}

#[derive(Default)]
pub struct InstructionArgumentBuilder {
    ssa_id: Option<String>,
    name: Option<String>,
    scope: Option<VariableScope>,
    value: Option<InstructionValue>,
    index: Option<IndexKind>,
}

impl InstructionArgumentBuilder {
    pub fn ssa_id(mut self, ssa_id: String) -> Self {
        self.ssa_id = Some(ssa_id);
        self
    }

    pub fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    pub fn scope(mut self, scope: VariableScope) -> Self {
        self.scope = Some(scope);
        self
    }

    pub fn value(mut self, value: InstructionValue) -> Self {
        self.value = Some(value);
        self
    }

    pub fn index(mut self, index: IndexKind) -> Self {
        self.index = Some(index);
        self
    }

    pub fn build(self) -> Result<InstructionArgument> {
        Ok(InstructionArgument {
            ssa_id: self.ssa_id.ok_or_else(|| eyre!("SSA ID is required"))?,
            name: self.name.ok_or_else(|| eyre!("Name is required"))?,
            scope: self.scope.ok_or_else(|| eyre!("Scope is required"))?,
            value: self.value.ok_or_else(|| eyre!("Value is required"))?,
            index: self.index.ok_or_else(|| eyre!("Index is required"))?,
        })
    }
}

impl InstructionArguments {
    pub fn builder() -> InstructionArgumentsBuilder {
        InstructionArgumentsBuilder::default()
    }
}

#[derive(Default)]
pub struct InstructionArgumentsBuilder {
    name: Option<InstructionName>,
    num_args: Option<u32>,
    arguments: SmallVec<[InstructionArgument; 4]>,
}

impl InstructionArgumentsBuilder {
    pub fn name(mut self, name: InstructionName) -> Self {
        self.name = Some(name);
        self
    }
    pub fn num_args(mut self, num_args: u32) -> Self {
        self.num_args = Some(num_args);
        self
    }

    pub fn get_name(&self) -> Option<InstructionName> {
        self.name
    }

    pub fn get_num_args(&self) -> Option<u32> {
        self.num_args
    }

    pub fn push_argument(mut self, argument: InstructionArgument) -> Self {
        self.arguments.push(argument);
        self
    }

    pub fn push_vec_arguments(mut self, arguments: Vec<InstructionArgument>) -> Self {
        self.arguments.extend(arguments);
        self
    }

    pub fn build(self) -> Result<InstructionArguments> {
        Ok(InstructionArguments {
            name: self
                .name
                .ok_or_else(|| eyre!("Instruction name is required"))?,
            num_args: self
                .num_args
                .ok_or_else(|| eyre!("Number of arguments is required"))?,
            arguments: self.arguments,
        })
    }
}

impl Instruction {
    pub fn builder() -> InstructionBuilder {
        InstructionBuilder::default()
    }
}

#[derive(Default)]
pub struct InstructionBuilder {
    position: Option<u32>,
    name: Option<InstructionName>,
    scope: Option<ExecutionScope>,
    arguments: Option<InstructionArguments>,
    vec_arguments: Option<Vec<InstructionArguments>>,
    line: Option<usize>,
}

impl InstructionBuilder {
    pub fn position(mut self, position: u32) -> Self {
        self.position = Some(position);
        self
    }

    pub fn name(mut self, name: InstructionName) -> Self {
        self.name = Some(name);
        self
    }

    pub fn arguments(mut self, arguments: InstructionArguments) -> Self {
        self.arguments = Some(arguments);
        self
    }

    pub fn vec_arguments(mut self, vec_arguments: Vec<InstructionArguments>) -> Self {
        self.vec_arguments = Some(vec_arguments);
        self
    }

    pub fn scope(mut self, scope: ExecutionScope) -> Self {
        self.scope = Some(scope);
        self
    }

    pub fn line(mut self, line: usize) -> Self {
        self.line = Some(line);
        self
    }

    pub fn build(self) -> Result<Instruction> {
        Ok(Instruction {
            position: self.position.ok_or_else(|| eyre!("Position is required"))?,
            name: self.name.ok_or_else(|| eyre!("Name is required"))?,
            scope: self
                .scope
                .ok_or_else(|| eyre!("Instruction scope is required"))?,
            arguments: self
                .arguments
                .ok_or_else(|| eyre!("Arguments are required"))?,
            vec_arguments: self.vec_arguments,
            line: self.line.ok_or_else(|| eyre!("Line is required"))?,
        })
    }
}

impl Thread {
    pub fn builder() -> ThreadBuilder {
        ThreadBuilder::default()
    }
}

#[derive(Default)]
pub struct ThreadBuilder {
    instructions: SmallVec<[Instruction; 30]>,
}

impl ThreadBuilder {
    pub fn instruction(mut self, instruction: Instruction) -> Self {
        self.instructions.push(instruction);
        self
    }

    pub fn build(self) -> Thread {
        Thread {
            instructions: self.instructions,
        }
    }
}

impl Program {
    pub fn builder() -> ProgramBuilder {
        ProgramBuilder::default()
    }
}

#[derive(Default)]
pub struct ProgramBuilder {
    global_vars: Vec<VariableInfo>,
    subgroup_size: Option<u32>,
    work_group_size: Option<u32>,
    num_work_groups: Option<u32>,
    num_threads: Option<u32>,
    scheduler: Option<Scheduler>,
    // thread: SmallVec<[Thread; 8]>,
    instructions: SmallVec<[Instruction; 10]>,
    constants: SmallVec<[Constant; 10]>,
    func_start_line: Option<usize>,
}

impl ProgramBuilder {
    pub fn global_var(mut self, global_vars: Vec<VariableInfo>) -> Self {
        self.global_vars.extend(global_vars);
        self
    }

    pub fn subgroup_size(mut self, subgroup_size: u32) -> Self {
        self.subgroup_size = Some(subgroup_size);
        self
    }

    pub fn work_group_size(mut self, work_group_size: u32) -> Self {
        self.work_group_size = Some(work_group_size);
        self
    }

    pub fn num_work_groups(mut self, num_work_groups: u32) -> Self {
        self.num_work_groups = Some(num_work_groups);
        self
    }

    pub fn num_threads(mut self, num_threads: u32) -> Self {
        self.num_threads = Some(num_threads);
        self
    }

    pub fn scheduler(mut self, scheduler: Scheduler) -> Self {
        self.scheduler = Some(scheduler);
        self
    }

    pub fn push_instruction(mut self, instruction: Instruction) -> Self {
        self.instructions.push(instruction);
        self
    }

    pub(crate) fn push_vec_instructions(mut self, instructions: Vec<Instruction>) -> Self {
        self.instructions.extend(instructions);
        self
    }

    pub fn func_start_line(mut self, func_start_line: usize) -> Self {
        self.func_start_line = Some(func_start_line);
        self
    }

    pub fn build(self) -> Result<Program> {
        Ok(Program {
            global_vars: self.global_vars,
            subgroup_size: self
                .subgroup_size
                .ok_or_else(|| eyre!("Subgroup size is required"))?,
            work_group_size: self
                .work_group_size
                .ok_or_else(|| eyre!("Work group size is required"))?,
            num_work_groups: self
                .num_work_groups
                .ok_or_else(|| eyre!("Number of work groups is required"))?,
            num_threads: self
                .num_threads
                .ok_or_else(|| eyre!("Number of threads is required"))?,
            scheduler: self
                .scheduler
                .ok_or_else(|| eyre!("Scheduler is required"))?,
            instructions: self.instructions,
            constants: self.constants,
            func_start_line: self
                .func_start_line
                .ok_or_else(|| eyre!("Function start line is required"))?,
        })
    }
}
