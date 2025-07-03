//! common is used to stored the common program information(e.g. number of blocks, subgroup size, thread numbers,...) in the codegen module.

use super::back::write;
use super::cfg::CFG;
use super::constant::Constant;
use crate::compiler::parse::symbol_table::{
    BuiltInVariable, ConstantInfo, StorageClass, VariableInfo,
};
use camino::Utf8Path;
use eyre::{eyre, Report, Result};
use smallvec::SmallVec;
use std::fmt::Display;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::str::FromStr;

static LAYOUT_CONFIG_HINT: &str = "(* Layout Configuration *)";
static PROGRAM_HINT: &str = "(* Program *)";
static GLOBAL_VARIABLES_HINT: &str = "(* Global Variables *)";
static CFG_HINT: &str = "(* CFG *)";
#[derive(Debug)]
pub enum BinaryExpr {
    Add,
    Sub,
    Mul,
    Div,
    NotEqual,
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum InstructionName {
    Assert,
    Assignment,
    Return,
    Load,
    Store,
    AtomicLoad,
    AtomicStore,
    Branch,
    BranchConditional,
    Switch,
    ControlBarrier,
    Label,
    SelectionMerge,
    LoopMerge,
    LogicalOr,
    LogicalAnd,
    LogicalEqual,
    LogicalNotEqual,
    LogicalNot,
    ShiftLeftLogical,
    ShiftRightLogical,
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    BitwiseOr,
    BitwiseAnd,
    Bitcast,
    Add,
    AtomicAdd,
    Sub,
    AtomicSub,
    AtomicOr,
    AtomicAnd,
    Mul,
    Mod,
    AtomicExchange,
    AtomicCompareExchange,
    GroupAll,
    GroupAny,
    GroupNonUniformAll,
    GroupNonUniformAllEqual,
    GroupNonUniformAny,
    GroupNonUniformBroadcast,
}

pub static BRANCH_INSTRUCTIONS: [InstructionName; 3] = [
    InstructionName::Branch,
    InstructionName::BranchConditional,
    InstructionName::Switch,
];

pub static TERMINATION_INSTRUCTIONS: [InstructionName; 4] = [
    InstructionName::Branch,
    InstructionName::BranchConditional,
    InstructionName::Switch,
    InstructionName::Return,
];

pub static TANGLED_INSTRUCTIONS: [InstructionName; 4] = [
    InstructionName::ControlBarrier,
    InstructionName::GroupNonUniformAll,
    InstructionName::GroupNonUniformAny,
    InstructionName::GroupNonUniformBroadcast,
];

pub(crate) static MERGE_INSTRUCTIONS: [InstructionName; 2] =
    [InstructionName::SelectionMerge, InstructionName::LoopMerge];
impl Display for InstructionName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionName::Assert => write!(f, "Assert"),
            InstructionName::Assignment => write!(f, "Assignment"),
            InstructionName::Return => write!(f, "Terminate"),
            // InstructionName::Load => write!(f, "OpLoad"),
            // InstructionName::Store => write!(f, "OpStore"),
            InstructionName::Load | InstructionName::AtomicLoad => write!(f, "OpAtomicLoad"),
            InstructionName::Store | InstructionName::AtomicStore => write!(f, "OpAtomicStore"),
            InstructionName::Branch => write!(f, "OpBranch"),
            InstructionName::BranchConditional => write!(f, "OpBranchConditional"),
            InstructionName::Switch => write!(f, "OpSwitch"),
            InstructionName::ControlBarrier => write!(f, "OpControlBarrier"),
            InstructionName::Label => write!(f, "OpLabel"),
            InstructionName::SelectionMerge => write!(f, "OpSelectionMerge"),
            InstructionName::LoopMerge => write!(f, "OpLoopMerge"),
            InstructionName::LogicalOr => write!(f, "OpLogicalOr"),
            InstructionName::LogicalAnd => write!(f, "OpLogicalAnd"),
            InstructionName::LogicalEqual => write!(f, "OpLogicalEqual"),
            InstructionName::LogicalNotEqual => write!(f, "OpLogicalNotEqual"),
            InstructionName::LogicalNot => write!(f, "OpLogicalNot"),
            InstructionName::ShiftLeftLogical => write!(f, "OpShiftLeftLogical"),
            InstructionName::ShiftRightLogical => write!(f, "OpShiftRightLogical"),
            InstructionName::Equal => write!(f, "OpEqual"),
            InstructionName::NotEqual => write!(f, "OpNotEqual"),
            InstructionName::LessThan => write!(f, "OpLess"),
            InstructionName::LessThanEqual => write!(f, "OpLessOrEqual"),
            InstructionName::GreaterThan => write!(f, "OpGreater"),
            InstructionName::GreaterThanEqual => write!(f, "OpGreaterOrEqual"),
            InstructionName::BitwiseOr => write!(f, "OpBitwiseOr"),
            InstructionName::BitwiseAnd => write!(f, "OpBitwiseAnd"),
            InstructionName::Bitcast => write!(f, "OpBitcast"),
            InstructionName::Add => write!(f, "OpAdd"),
            InstructionName::AtomicAdd => write!(f, "OpAtomicAdd"),
            InstructionName::Sub => write!(f, "OpSub"),
            InstructionName::AtomicSub => write!(f, "OpAtomicSub"),
            InstructionName::AtomicOr => write!(f, "OpAtomicOr"),
            InstructionName::AtomicAnd => write!(f, "OpAtomicAnd"),
            InstructionName::Mul => write!(f, "OpMul"),
            InstructionName::Mod => write!(f, "OpMod"),
            InstructionName::AtomicExchange => write!(f, "OpAtomicExchange"),
            InstructionName::AtomicCompareExchange => write!(f, "OpAtomicCompareExchange"),
            InstructionName::GroupAll => write!(f, "OpGroupAll"),
            InstructionName::GroupAny => write!(f, "OpGroupAny"),
            InstructionName::GroupNonUniformAll => write!(f, "OpGroupNonUniformAll"),
            InstructionName::GroupNonUniformAllEqual => write!(f, "OpGroupNonUniformAllEqual"),
            InstructionName::GroupNonUniformAny => write!(f, "OpGroupNonUniformAny"),
            InstructionName::GroupNonUniformBroadcast => write!(f, "OpGroupNonUniformBroadcast"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum VariableScope {
    Intermediate,
    Local,
    Shared,
    Global,
    Literal,
}

impl Display for VariableScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableScope::Intermediate => write!(f, "intermediate"),
            VariableScope::Local => write!(f, "local"),
            VariableScope::Shared => write!(f, "shared"),
            VariableScope::Global => write!(f, "global"),
            VariableScope::Literal => write!(f, "literal"),
        }
    }
}

impl VariableScope {
    pub fn cast(storage_class: &StorageClass) -> Self {
        match storage_class {
            StorageClass::Global => VariableScope::Global,
            StorageClass::Local => VariableScope::Local,
            StorageClass::Shared => VariableScope::Shared,
            StorageClass::Intermediate => VariableScope::Intermediate,
            StorageClass::Constant => VariableScope::Literal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExecutionScope {
    // CrossDevice = 0,
    // Device = 1,
    WorkGroup = 2,
    SubGroup = 3,
    Invocation = 4,
    None,
}

impl From<i32> for ExecutionScope {
    fn from(value: i32) -> Self {
        match value {
            2 => ExecutionScope::WorkGroup,
            3 => ExecutionScope::SubGroup,
            4 => ExecutionScope::Invocation,
            _ => ExecutionScope::None,
        }
    }
}

impl Display for ExecutionScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // ExecutionScope::CrossDevice => write!(f, "CrossDevice"),
            // ExecutionScope::Device => write!(f, "Device"),
            ExecutionScope::WorkGroup => write!(f, "workgroup"),
            ExecutionScope::SubGroup => write!(f, "subgroup"),
            ExecutionScope::Invocation => write!(f, "invocation"),
            ExecutionScope::None => write!(f, "none"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum InstructionBuiltInVariable {
    NumWorkgroups,
    WorkgroupSize,
    WorkgroupId,
    LocalInvocationId,
    GlobalInvocationId,
    SubgroupSize,
    NumSubgroups,
    SubgroupId,
    SubgroupLocalInvocationId,
}

impl Display for InstructionBuiltInVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionBuiltInVariable::NumWorkgroups => write!(f, "NumWorkGroups"),
            InstructionBuiltInVariable::WorkgroupSize => write!(f, "WorkGroupSize"),
            InstructionBuiltInVariable::SubgroupSize => write!(f, "SubgroupSize"),
            InstructionBuiltInVariable::NumSubgroups => write!(f, "NumSubgroups"),
            InstructionBuiltInVariable::WorkgroupId => write!(f, "WorkGroupId(t)"),
            InstructionBuiltInVariable::LocalInvocationId => write!(f, "LocalInvocationId(t)"),
            InstructionBuiltInVariable::GlobalInvocationId => write!(f, "GlobalInvocationId(t)"),
            InstructionBuiltInVariable::SubgroupId => write!(f, "SubgroupId(t)"),
            InstructionBuiltInVariable::SubgroupLocalInvocationId => {
                write!(f, "SubgroupInvocationId(t)")
            }
        }
    }
}

impl InstructionBuiltInVariable {
    pub(crate) fn cast(var: BuiltInVariable) -> Self {
        match var {
            BuiltInVariable::NumWorkgroups => InstructionBuiltInVariable::NumWorkgroups,
            BuiltInVariable::WorkgroupSize => InstructionBuiltInVariable::WorkgroupSize,
            BuiltInVariable::WorkgroupId => InstructionBuiltInVariable::WorkgroupId,
            BuiltInVariable::LocalInvocationId => InstructionBuiltInVariable::LocalInvocationId,
            BuiltInVariable::GlobalInvocationId => InstructionBuiltInVariable::GlobalInvocationId,
            BuiltInVariable::SubgroupSize => InstructionBuiltInVariable::SubgroupSize,
            BuiltInVariable::NumSubgroups => InstructionBuiltInVariable::NumSubgroups,
            BuiltInVariable::SubgroupId => InstructionBuiltInVariable::SubgroupId,
            BuiltInVariable::SubgroupLocalInvocationId => {
                InstructionBuiltInVariable::SubgroupLocalInvocationId
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum IndexKind {
    Literal(i32),
    Variable(String),
}

impl Display for IndexKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IndexKind::Literal(value) => write!(f, "Index({})", value),
            IndexKind::Variable(name) => write!(f, "{}", name),
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
pub enum InstructionValue {
    None,
    // Pointer(String),
    BuiltIn(InstructionBuiltInVariable),
    Bool(bool),
    String(String),
    Int(i32),
    UInt(u32),
}

impl Display for InstructionValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionValue::None => write!(f, "\"\""),
            // InstructionValue::Pointer(name) => write!(f, "\"\""),
            InstructionValue::BuiltIn(var) => write!(f, "{}", var),
            InstructionValue::Bool(value) => {
                if *value {
                    write!(f, "TRUE")
                } else {
                    write!(f, "FALSE")
                }
            }
            InstructionValue::Int(value) => write!(f, "{}", value),
            InstructionValue::UInt(value) => write!(f, "{}", value),
            InstructionValue::String(value) => write!(f, "\"{}\"", value),
        }
    }
}

impl InstructionValue {
    pub fn parse(&self) -> Result<u32> {
        match self {
            InstructionValue::Int(value) => Ok(*value as u32),
            InstructionValue::UInt(value) => Ok(*value),
            _ => Err(eyre!("Invalid value type")),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Scheduler {
    OBE,
    HSA,
}
impl std::fmt::Display for Scheduler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Scheduler::OBE => write!(f, "\"OBE\""),
            Scheduler::HSA => write!(f, "\"HSA\""),
        }
    }
}

impl FromStr for Scheduler {
    type Err = Report;
    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "hsa" => Ok(Self::HSA),
            "obe" => Ok(Self::OBE),
            _ => Err(eyre!("Invalid scheduler: {}", s)),
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct InstructionArgument {
    pub ssa_id: String,
    pub name: String,
    pub scope: VariableScope,
    pub value: InstructionValue,
    pub index: IndexKind,
}

impl Display for InstructionArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Var(\"{}\", \"{}\", {}, {})",
            self.scope, self.name, self.value, self.index
        )
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct InstructionArguments {
    pub name: InstructionName,
    pub num_args: u32,
    pub arguments: SmallVec<[InstructionArgument; 4]>,
}

impl Display for InstructionArguments {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for idx in 0..self.arguments.len() {
            write!(f, "{}", self.arguments[idx])?;
            if idx != self.arguments.len() - 1 {
                write!(f, ", ")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub position: u32,
    pub name: InstructionName,
    pub scope: ExecutionScope,
    pub arguments: InstructionArguments,
    // this is used when some instructions
    //have undetermined number of arguments (e.g. OpSwitch)
    pub vec_arguments: Option<Vec<InstructionArguments>>,
    pub line: usize,
}

#[derive(Debug)]
pub struct Thread {
    pub instructions: SmallVec<[Instruction; 30]>,
}

/// `Program` is a struct that holds the program information.
/// `subgroup_size: u32` is the size of the subgroup.
/// `work_group_size: u32` is the size of the work group.
/// `num_work_groups: u32` is the number of work groups.
/// `num_threads: u32` is the number of threads.
/// `scheduler: Scheduler` is the scheduler type.
/// `thread: Vec<Thread>` is a vector of threads.
/// `constants: Vec<Constant>` is a vector of constants.
#[derive(Debug)]
pub struct Program {
    pub global_vars: Vec<VariableInfo>,
    pub subgroup_size: u32,
    pub work_group_size: u32,
    pub num_work_groups: u32,
    pub num_threads: u32,
    pub scheduler: Scheduler,
    pub instructions: SmallVec<[Instruction; 10]>,
    pub constants: SmallVec<[Constant; 10]>,
    pub func_start_line: usize,
}

impl Program {
    fn write_cfg(&self, writer: &mut BufWriter<File>) -> Result<()> {
        let cfg = CFG::generate_cfg(
            &self.instructions.to_vec(),
            self.num_work_groups,
            self.work_group_size,
        );
        writeln!(writer, "{}", cfg)?;
        self.write_dynamic_blocks(writer, &cfg)?;
        // self.write_unique_block_id(writer)?;
        Ok(())
    }

    fn write_unique_block_id(&self, writer: &mut BufWriter<File>) -> Result<()> {
        writeln!(writer, " InitGlobalCounter == globalCounter = <<")?;
        for idx in 0..self.num_threads {
            writeln!(writer, "{{")?;

            let filtered_instructions: Vec<_> = self
                .instructions
                .iter()
                .filter(|ins| ins.name == InstructionName::Label)
                .collect();

            filtered_instructions
                .iter()
                .enumerate()
                .for_each(|(i, ins)| {
                    let is_last = i == filtered_instructions.len() - 1;
                    let separator = if is_last { "" } else { "," };
                    writeln!(
                        writer,
                        "[labelIdx |-> {}, id |-> 1]{}",
                        ins.position, separator
                    )
                    .unwrap();
                });

            if idx != self.num_threads - 1 {
                writeln!(writer, "}},")?;
            } else {
                writeln!(writer, "}}")?;
            }
        }
        writeln!(writer, ">>")?;
        Ok(())
    }

    fn write_dynamic_blocks(&self, writer: &mut BufWriter<File>, cfg: &CFG) -> Result<()> {
        writeln!(writer, "InitDB == DynamicNodeSet = {{")?;
        // each node has different op_label_idx, so we can safely unwrap the result
        let node = cfg
            .nodes
            .iter()
            .min_by(|x, y| x.op_label_idx.cmp(&y.op_label_idx))
            .unwrap();

        let current_threads = node
            .tangle
            .iter()
            .map(|s| {
                format!(
                    "{{{}}}",
                    s.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect::<Vec<_>>();
        let current_threads = current_threads.join(", ");
        let empty_set_per_wg = vec!["{}"; self.num_work_groups as usize].join(", ");
        let empty_seq_per_thread = vec!["<<>>"; self.num_threads as usize].join(", ");
        writeln!(
            writer,
            "DynamicNode(<<{}>>, <<{}>>, <<{}>>, <<{}>>, {}, 0, <<>>, {{}})",
            current_threads, current_threads, empty_set_per_wg, empty_set_per_wg, node.op_label_idx
        )?;

        writeln!(writer, "}}")?;
        Ok(())
    }

    fn write_layout(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write layout information to the lines
        writeln!(writer, "SubgroupSize == {}", self.subgroup_size)?;
        writeln!(writer, "WorkGroupSize == {}", self.work_group_size)?;
        writeln!(writer, "NumWorkGroups == {}", self.num_work_groups)?;
        writeln!(
            writer,
            "NumSubgroups == {}",
            self.num_work_groups * self.work_group_size / self.subgroup_size
        )?;
        writeln!(writer, "NumThreads == {}", self.num_threads)?;
        writeln!(writer, "Scheduler == {}", self.scheduler)?;
        Ok(())
    }
    fn write_global_variables(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write global variables to the lines
        writeln!(writer, "InitGPU == ")?;
        writeln!(writer, "\tglobalVars = {{")?;
        for (idx, global_var) in self.global_vars.iter().enumerate() {
            if idx != self.global_vars.len() - 1 {
                writeln!(
                    writer,
                    "\t\tVar(\"{}\", \"{}\", {}, {}),",
                    global_var.get_storage_class(),
                    global_var.get_var_name(),
                    global_var.initial_value(),
                    global_var.get_index(),
                )?;
            } else {
                writeln!(
                    writer,
                    "\t\tVar(\"{}\", \"{}\", {}, {})",
                    global_var.get_storage_class(),
                    global_var.get_var_name(),
                    global_var.initial_value(),
                    global_var.get_index(),
                )?;
            }
        }
        writeln!(writer, "\t}}")?;
        Ok(())
    }
    fn write_program(&self, writer: &mut BufWriter<File>) -> Result<()> {
        // Write instructions to the lines
        writeln!(
            writer,
            r"ThreadInstructions ==  [t \in 1..NumThreads |-> <<"
        )?;
        for (idx, inst) in self.instructions.iter().enumerate() {
            if idx != self.instructions.len() - 1 {
                writeln!(writer, "\"{}\",", inst.name)?;
            } else {
                writeln!(writer, "\"{}\"", inst.name)?;
            }
        }
        writeln!(writer, ">>]\n")?;

        // Insert ThreadArguments
        writeln!(writer, r"ThreadArguments == [t \in 1..NumThreads |-> <<")?;
        for (idx, inst) in self.instructions.iter().enumerate() {
            write!(writer, "<<")?;
            write!(writer, "{}", inst.arguments)?;
            if let Some(ref vec_args) = inst.vec_arguments {
                write!(writer, ", ")?;
                for (vec_arg_idx, vec_arg) in vec_args.iter().enumerate() {
                    write!(writer, "<<")?;
                    write!(writer, "{} ", vec_arg)?;
                    write!(writer, ">>")?;
                    if vec_arg_idx != vec_args.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
            }
            write!(writer, ">>")?;

            if idx != self.instructions.len() - 1 {
                writeln!(writer, ",")?;
            }
        }
        writeln!(writer, ">>]\n")?;
        Ok(())
    }

    pub fn write_to_file(&self, path: &Utf8Path) -> Result<()> {
        // Open the file for reading
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let temp_path = path.with_extension("tmp");
        let temp_file = File::create(&temp_path)?;
        let mut writer = BufWriter::new(temp_file);

        let mut found_layout = false;
        let mut found_globals = false;
        let mut found_program = false;

        for line in reader.lines() {
            let line = line?;
            if line.trim() == LAYOUT_CONFIG_HINT {
                found_layout = true;
                self.write_layout(&mut writer)?;
            } else if line.trim() == GLOBAL_VARIABLES_HINT {
                found_globals = true;
                self.write_global_variables(&mut writer)?;
            } else if line.trim() == PROGRAM_HINT {
                found_program = true;
                self.write_program(&mut writer)?;
            } else if line.trim() == CFG_HINT {
                self.write_cfg(&mut writer)?;
            } else {
                writeln!(writer, "{}", line)?;
            }
        }
        drop(writer);

        if !found_layout {
            return Err(eyre!("Layout configuration hint not found in the file."));
        }
        if !found_globals {
            return Err(eyre!("Global variables hint not found in the file."));
        }
        if !found_program {
            return Err(eyre!("Program hint not found in the file."));
        }

        // Replace the original file with the new file
        fs::rename(temp_path, path)?;
        Ok(())
    }
}
