use std::{fs::{self, File}, io::{BufRead, BufReader, BufWriter, Write}};

use camino::Utf8Path;
use compiler::{codegen::{common::{
    Instruction, InstructionName, InstructionValue, Program,
}, constant::{Constant, ConstantType}}, compiler::parse::symbol_table::{BuiltInVariable, VariableSymbolTable}};
use rand::{random_range, rng, seq::SliceRandom};
use eyre::{Result, eyre};

// write to the file at line + cursor
pub struct MutCtx<'a >{
    pub program: Program,
    pub file: String,
    // vector of tuples of instructions and if really mutated
    pub added_instructions: Vec<Instruction>,
    pub added_constants: Vec<Constant>,
    variable_table: &'a VariableSymbolTable,
    used_const: Vec<i32>,
}
impl<'a> MutCtx<'a> {
    pub fn new(program: Program, file: String, table: &'a VariableSymbolTable) -> Self {
        Self {
            program,
            file,
            added_instructions: Vec::new(),
            added_constants: Vec::new(),
            variable_table: table,
            used_const: Vec::new(),
        }
    }

    fn to_spirv(inst: &Instruction) -> Result<String> {
        let mut arg_iter = inst.arguments.arguments.iter();
        let result = match inst.name{
            InstructionName::BranchConditional => format!(""),
            InstructionName::Equal | InstructionName::NotEqual | InstructionName::LessThan | 
            InstructionName::LessThanEqual | InstructionName::GreaterThan | InstructionName::GreaterThanEqual => format!("{} =", &arg_iter.next().unwrap().ssa_id.as_str()),
            _ => return Err(eyre!("Instruction not supported to convert back to SPIR-V")),
        };
        let inst_name = match inst.name{
            InstructionName::BranchConditional => "OpBranchConditional",
            InstructionName::Equal => "OpIEqual",
            InstructionName::NotEqual => "OpINotEqual",
            InstructionName::LessThan => "OpULessThan",
            InstructionName::LessThanEqual => "OpULessThanEqual",
            InstructionName::GreaterThan => "OpUGreaterThan",
            InstructionName::GreaterThanEqual => "OpUGreaterThanEqual",
            _ => return Err(eyre!("Instruction not supported to convert back to SPIR-V")),
        };
        let result_type = match inst.name {
            InstructionName::BranchConditional => "",
            InstructionName::Equal | InstructionName::NotEqual | InstructionName::LessThan | 
            InstructionName::LessThanEqual | InstructionName::GreaterThan | InstructionName::GreaterThanEqual => "%bool",
            _ => return Err(eyre!("Instruction not supported to convert back to SPIR-V")),
        };
        let args : Vec<String> = arg_iter.map(|arg| {
            arg.ssa_id.clone()
        }).collect();

        Ok(format!("{} {} {} {} ", result, inst_name, result_type, args.join(" ")))
    }


    pub fn write_to_file(&self) -> Result<()> {
        // let mut cursor = 0;
        let start_line = self.program.instructions.first().unwrap().line - 1;
        // Open the file for reading
        let fuzzed_file = String::from(format!("{}.fuzz.txt", self.file));
        let path = Utf8Path::new(&self.file);
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let temp_path = path.with_extension("tmp");
        let temp_file = File::create(&temp_path)?;
        let mut writer = BufWriter::new(temp_file);
        let mut stmts = reader.lines().peekable();
        let mut idx : usize = 0;
        let mut const_iter = self.added_constants.iter();
        let mut instruction_iter = self.added_instructions.iter().peekable();
        let mut add_const = false;
        while stmts.peek().is_some() {
            // write additional constant value
            if !add_const && idx == start_line {
                for constant in const_iter.by_ref() {
                    writeln!(writer, "%uint_{} = OpConstant %uint {}", constant.value, constant.value)?;
                }
                add_const = true;
                continue;
                
            } 
            if let Some(&instruction) = instruction_iter.peek() {
                if  idx == instruction.line {
                    writeln!(writer, "{}", Self::to_spirv(&instruction)?)?;
                    instruction_iter.next();
                    stmts.next();
                    idx += 1;
                }
            } 
            writeln!(writer, "{}", stmts.next().unwrap()?)?;
            idx += 1;
            
        }
        drop(writer);

        // Replace the original file with the new file
        fs::rename(temp_path, fuzzed_file)?;
        Ok(())
    }

    pub(crate) fn mutation(mut self) -> Self {
        loop {
            self.trivial_mutation();
            if !self.added_instructions.is_empty() {
                break;
            } else{
                self.clean();
            }
        }
        self
    }

    fn clean(&mut self) {
        self.added_instructions.clear();
        self.added_constants.clear();
    }

    fn trivial_mutation(&mut self) {
        for (idx, instruction) in self.program.instructions.clone().into_iter().enumerate() {
            match instruction.name {
                // InstructionName::BranchConditional => {
                //     self.switch_branch_label(instruction);
                // }
                // InstructionName::Switch => {
                //     todo!()
                // }
                InstructionName::Equal
                | InstructionName::NotEqual
                | InstructionName::LessThan
                | InstructionName::LessThanEqual
                | InstructionName::GreaterThan
                | InstructionName::GreaterThanEqual => {
                        let mutated_ins = self.fuzz_comparison_condition(instruction.clone());
                        if mutated_ins.arguments != instruction.arguments {
                            self.added_instructions.push(mutated_ins);
                        }
                }
                _ => {}
            }
        }
    }

    // add additional constant to the program
    fn additional_constant(&mut self, const_val: i32) {
        if !self.exists_constant(const_val) {
            let constant = Constant {
                name: format!("%uint_{}", const_val),
                value: ConstantType::Uint(const_val as u32),
            };
            self.added_constants.push(constant);
        }
    }

    fn exists_constant(&self, const_val: i32) -> bool {
        self.variable_table.lookup(&format!("%uint_{}", const_val)).is_some() | self.added_constants.iter().any(|con| 
            con.name == format!("%uint_{}", const_val))
    }

    fn available_labels(&self) -> Vec<u32> {
        let mut labels = Vec::new();
        for instruction in &self.program.instructions {
            if let InstructionName::Label = instruction.name {
                labels.push(instruction.arguments.arguments[0].value.parse().unwrap());
            }
        }
        labels
    }

    fn fuzz_if_condition(instruction: &Instruction, program: &Program) {
        todo!()
    }

    fn fuzz_comparison_condition(&mut self, mut instruction:Instruction) -> Instruction{
        let operand_1 = &instruction.arguments.arguments[1].value;
        let operand_2 = &instruction.arguments.arguments[2].value;
        let operand_1_name = &instruction.arguments.arguments[1].name;
        let operand_2_name = &instruction.arguments.arguments[2].name;
        if let InstructionValue::Int(val) = operand_1 {
            if let Some(built_in) =  self.variable_table.lookup(operand_2_name).unwrap().built_in {
                match built_in {
                    BuiltInVariable::GlobalInvocationId => {
                        let totoal_threads = (self.program.work_group_size * self.program.num_work_groups) as i32;
                        let rand_val = random_range(0..totoal_threads);
                        self.additional_constant(rand_val);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(rand_val);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", rand_val);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", rand_val);
                    }
                    BuiltInVariable::LocalInvocationId => {
                        let local_id = random_range(0..self.program.work_group_size) as i32;
                        self.additional_constant(local_id);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(local_id);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", local_id);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", local_id);
                    }
                    BuiltInVariable::WorkgroupId => {
                        let work_group_id = random_range(0..self.program.num_work_groups) as i32;
                        self.additional_constant(work_group_id);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(work_group_id);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", work_group_id);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", work_group_id);
                    }
                    BuiltInVariable::SubgroupId => {
                        let num_subgroups =
                            self.program.num_work_groups / self.program.subgroup_size;
                        let subgroup_id = random_range(0..num_subgroups) as i32;
                        self.additional_constant(subgroup_id);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(subgroup_id);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", subgroup_id);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", subgroup_id);
                    }
                    BuiltInVariable::SubgroupLocalInvocationId => {
                        let subgroup_local_id = random_range(0..self.program.subgroup_size) as i32;
                        self.additional_constant(subgroup_local_id);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(subgroup_local_id);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", subgroup_local_id);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", subgroup_local_id);
                    }
                    BuiltInVariable::NumWorkgroups => {
                        let num_work_groups = random_range(0..=self.program.num_work_groups) as i32;
                        self.additional_constant(num_work_groups);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(num_work_groups);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", num_work_groups);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", num_work_groups);
                    }
                    BuiltInVariable::NumSubgroups => {
                        let num_subgroups = random_range(
                            0..=self.program.num_work_groups / self.program.subgroup_size,
                        ) as i32;
                        self.additional_constant(num_subgroups);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(num_subgroups);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", num_subgroups);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", num_subgroups);
                    }
                    BuiltInVariable::WorkgroupSize => {
                        let workgroup_size = random_range(0..=self.program.work_group_size) as i32;
                        self.additional_constant(workgroup_size);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(workgroup_size);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", workgroup_size);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", workgroup_size);
                    }
                    BuiltInVariable::SubgroupSize => {
                        let subgroup_size = random_range(0..=self.program.subgroup_size) as i32;
                        self.additional_constant(subgroup_size);
                        instruction.arguments.arguments[1].value = InstructionValue::Int(subgroup_size);
                        instruction.arguments.arguments[1].name = format!("%uint_{}", subgroup_size);
                        instruction.arguments.arguments[1].ssa_id = format!("%uint_{}", subgroup_size);
                    }
                }
            }
        } else if let InstructionValue::Int(val) = operand_2 {
            if let Some(built_in) =  self.variable_table.lookup(operand_1_name).unwrap().built_in {
                match built_in {
                    BuiltInVariable::GlobalInvocationId => {
                        let totoal_threads =
                            (self.program.work_group_size * self.program.num_work_groups) as i32;
                        let rand_val = random_range(0..totoal_threads);
                        self.additional_constant(rand_val);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(rand_val);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", rand_val);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", rand_val);
                    }
                    BuiltInVariable::LocalInvocationId => {
                        let local_id = random_range(0..self.program.work_group_size) as i32;
                        self.additional_constant(local_id);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(local_id);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", local_id);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", local_id);

                    }
                    BuiltInVariable::WorkgroupId => {
                        let work_group_id = random_range(0..self.program.num_work_groups) as i32;
                        self.additional_constant(work_group_id);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(work_group_id);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", work_group_id);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", work_group_id);
                    }
                    BuiltInVariable::SubgroupId => {
                        let num_subgroups =
                            self.program.num_work_groups / self.program.subgroup_size;
                        let subgroup_id = random_range(0..num_subgroups) as i32;
                        self.additional_constant(subgroup_id);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(subgroup_id);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", subgroup_id);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", subgroup_id);
                    }
                    BuiltInVariable::SubgroupLocalInvocationId => {
                        let subgroup_local_id = random_range(0..self.program.subgroup_size) as i32;
                        self.additional_constant(subgroup_local_id);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(subgroup_local_id);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", subgroup_local_id);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", subgroup_local_id);
                    }
                    BuiltInVariable::NumWorkgroups => {
                        let num_work_groups = random_range(0..=self.program.num_work_groups) as i32;
                        self.additional_constant(num_work_groups);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(num_work_groups);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", num_work_groups);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", num_work_groups);
                    }
                    BuiltInVariable::NumSubgroups => {
                        let num_subgroups = random_range(
                            0..=self.program.num_work_groups / self.program.subgroup_size,
                        ) as i32;
                        self.additional_constant(num_subgroups);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(num_subgroups);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", num_subgroups);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", num_subgroups);
                    }
                    BuiltInVariable::WorkgroupSize => {
                        let workgroup_size = random_range(0..=self.program.work_group_size) as i32;
                        self.additional_constant(workgroup_size);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(workgroup_size);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", workgroup_size);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", workgroup_size);
                    }
                    BuiltInVariable::SubgroupSize => {
                        let subgroup_size = random_range(0..=self.program.subgroup_size) as i32;
                        self.additional_constant(subgroup_size);
                        instruction.arguments.arguments[2].value = InstructionValue::Int(subgroup_size);
                        instruction.arguments.arguments[2].name = format!("%uint_{}", subgroup_size);
                        instruction.arguments.arguments[2].ssa_id = format!("%uint_{}", subgroup_size);
                    }
                }
            }
        }
        instruction
    }

    fn fuzz_branch_condition(instruction: &mut Instruction) {
        todo!()
    }

    fn fuzz_loop_condition(instruction: &mut Instruction) {
        todo!()
    }

    fn switch_branch_label(&mut self, mut instruction: Instruction) {
        match instruction.name {
            InstructionName::Branch => {}
            InstructionName::BranchConditional => {
                // Switch the branch label
                instruction.arguments.arguments.swap(1, 2);
            }
            InstructionName::Switch => {
                let mut rng = rng();
                // shuffle the labels
                if let Some(labels) = &mut instruction.vec_arguments {
                    labels.shuffle(&mut rng);
                }
            }
            _ => {}
        }
    }
}
