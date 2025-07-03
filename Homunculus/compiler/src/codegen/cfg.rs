use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::codegen::common::{InstructionValue, MERGE_INSTRUCTIONS, TERMINATION_INSTRUCTIONS};

use super::{
    back::write,
    common::{Instruction, InstructionName},
};

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum ConstructType {
    Selection,
    Loop,
    Continue,
    Switch,
    Case,
    None,
}

impl Display for ConstructType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Selection => write!(f, "Selection"),
            Self::Loop => write!(f, "Loop"),
            Self::Continue => write!(f, "Continue"),
            Self::Switch => write!(f, "Switch"),
            Self::Case => write!(f, "Case"),
            Self::None => write!(f, "None"),
        }
    }
}

#[derive(Debug, Clone)]
struct ControlFlowConstruct {
    construct_type: ConstructType,
    header_block: u32,
    merge_block: i32,
    continue_target: i32,
    blocks: HashSet<u32>,
}

#[derive(Debug, Clone)]
pub(crate) struct Node {
    pub(crate) op_label_idx: u32,
    termination_inst_idx: u32,
    pub(crate) tangle: Vec<HashSet<u32>>,
    merge: bool,
    initialize: Vec<bool>,
    construct_type: ConstructType,
    merge_block: i32,
    continue_block: i32,
    default_block: i32,
    case_blocks: Vec<i32>,
}

#[derive(Eq, Hash, PartialEq, Debug)]
pub(crate) struct Edge(u32, u32);

#[derive(Debug)]
pub(crate) struct CFG {
    pub(crate) nodes: Vec<Node>,
    pub(crate) edges: HashSet<Edge>,
    successors: HashMap<u32, HashSet<u32>>,
    predecessors: HashMap<u32, HashSet<u32>>,
    dominated: HashMap<u32, HashSet<u32>>,
    post_dominated: HashMap<u32, HashSet<u32>>,
    constructs: Vec<ControlFlowConstruct>,
}
impl Display for ControlFlowConstruct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[")?;
        writeln!(f, "constructType |-> \"{}\",", self.construct_type)?;
        writeln!(f, "headerBlock |-> {},", self.header_block)?;
        writeln!(f, "mergeBlock |-> {},", self.merge_block)?;
        writeln!(f, "continueTarget |-> {},", self.continue_target)?;
        writeln!(f, "blocks |-> {{")?;
        for (idx, block) in self.blocks.iter().enumerate() {
            if idx != self.blocks.len() - 1 {
                writeln!(f, "{},", block)?;
            } else {
                writeln!(f, "{}", block)?;
            }
        }
        writeln!(f, "}}")?;
        writeln!(f, "]")?;
        Ok(())
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[")?;
        writeln!(f, "opLabelIdx |-> {},", self.op_label_idx)?;
        writeln!(f, "terminatedInstrIdx |-> {},", self.termination_inst_idx)?;
        writeln!(f, "tangle |-> <<")?;
        for (idx, tangle) in self.tangle.iter().enumerate() {
            write!(f, "{{")?;
            for (t_idx, t) in tangle.iter().enumerate() {
                if t_idx != tangle.len() - 1 {
                    write!(f, "{},", t)?;
                } else {
                    write!(f, "{}", t)?;
                }
            }
            if idx != self.tangle.len() - 1 {
                writeln!(f, "}},")?;
            } else {
                writeln!(f, "}}")?;
            }
        }
        writeln!(f, ">>,")?;
        writeln!(
            f,
            "merge |-> {},",
            if self.merge { "TRUE" } else { "FALSE" }
        )?;
        writeln!(f, "initialized |-> <<")?;
        for (idx, init) in self.initialize.iter().enumerate() {
            if idx != self.initialize.len() - 1 {
                writeln!(f, "{},", if *init { "TRUE" } else { "FALSE" })?;
            } else {
                writeln!(f, "{}", if *init { "TRUE" } else { "FALSE" })?;
            }
        }
        writeln!(f, ">>,")?;
        writeln!(f, "constructType |-> \"{}\",", self.construct_type)?;
        writeln!(f, "mergeBlock |-> {},", self.merge_block)?;
        writeln!(f, "continueBlock |-> {},", self.continue_block)?;
        writeln!(f, "defaultBlock |-> {},", self.default_block)?;
        writeln!(f, "caseBlocks |-> <<")?;
        for (idx, case) in self.case_blocks.iter().enumerate() {
            if idx != self.case_blocks.len() - 1 {
                writeln!(f, "{},", case)?;
            } else {
                writeln!(f, "{}", case)?;
            }
        }
        writeln!(f, ">>")?;
        writeln!(f, "]")?;
        Ok(())
    }
}
impl Display for CFG {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // write edges
        writeln!(f, "CFGEdges == {{")?;
        for (idx, edge) in self.edges.iter().enumerate() {
            if idx != self.edges.len() - 1 {
                writeln!(f, "<<{}, {}>>, ", edge.0, edge.1)?;
            } else {
                writeln!(f, "<<{}, {}>>", edge.0, edge.1)?;
            }
        }
        writeln!(f, "}}")?;

        // write successors
        writeln!(f, "CFGSuccessors == {{")?;
        for (idx, (node, successor)) in self.successors.iter().enumerate() {
            writeln!(f, "<<{}, {{", node)?;
            for (s_idx, s) in successor.iter().enumerate() {
                if s_idx != successor.len() - 1 {
                    write!(f, "{},", s)?;
                } else {
                    write!(f, "{}", s)?;
                }
            }
            write!(f, "}}")?;
            if idx != self.successors.len() - 1 {
                writeln!(f, ">>,")?;
            } else {
                writeln!(f, ">>")?;
            }
        }
        writeln!(f, "}}")?;

        // write predecessors
        writeln!(f, "CFGPredecessors == {{")?;
        for (idx, (node, predecessor)) in self.predecessors.iter().enumerate() {
            writeln!(f, "<<{}, {{", node)?;
            for (p_idx, p) in predecessor.iter().enumerate() {
                if p_idx != predecessor.len() - 1 {
                    write!(f, "{},", p)?;
                } else {
                    write!(f, "{}", p)?;
                }
            }
            write!(f, "}}")?;
            if idx != self.predecessors.len() - 1 {
                writeln!(f, ">>,")?;
            } else {
                writeln!(f, ">>")?;
            }
        }
        writeln!(f, "}}")?;

        // write dominated
        writeln!(f, "Dominated == {{")?;
        for (idx, (node, dom)) in self.dominated.iter().enumerate() {
            writeln!(f, "[node |-> {},", node)?;
            writeln!(f, "dominated |-> {{")?;
            for (d_idx, d) in dom.iter().enumerate() {
                if d_idx != dom.len() - 1 {
                    write!(f, "{},", d)?;
                } else {
                    write!(f, "{}", d)?;
                }
            }
            write!(f, "}}")?;
            if idx != self.dominated.len() - 1 {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }
        writeln!(f, "}}")?;

        // write post_dominated
        writeln!(f, "PostDominated == {{")?;
        for (idx, (node, p_dom)) in self.post_dominated.iter().enumerate() {
            writeln!(f, "[node |-> {},", node)?;
            writeln!(f, "postDominated |-> {{")?;
            for (p_idx, p) in p_dom.iter().enumerate() {
                if p_idx != p_dom.len() - 1 {
                    write!(f, "{},", p)?;
                } else {
                    write!(f, "{}", p)?;
                }
            }
            write!(f, "}}")?;
            if idx != self.post_dominated.len() - 1 {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }
        writeln!(f, "}}")?;

        // write control flow construct
        writeln!(f, "ControlFlowConstructs == {{")?;
        for (idx, construct) in self.constructs.iter().enumerate() {
            write!(f, "{}", construct)?;
            if idx != self.constructs.len() - 1 {
                writeln!(f, ",")?;
            } else {
                writeln!(f, "")?;
            }
        }
        writeln!(f, "}}")?;

        // write blocks
        writeln!(f, "Blocks == <<")?;
        for (idx, block) in self.nodes.iter().enumerate() {
            write!(f, "{}", block)?;
            if idx != self.nodes.len() - 1 {
                writeln!(f, ",")?;
            } else {
                writeln!(f, "")?;
            }
        }
        writeln!(f, ">>")?;

        // write blocks
        writeln!(f, "MergeBlocks == {{")?;
        for (idx, block) in self.nodes.iter().filter(|n| n.merge == true).enumerate() {
            write!(f, "{}", block.op_label_idx)?;
            if idx != self.nodes.len() - 1 {
                writeln!(f, ",")?;
            } else {
                writeln!(f, "")?;
            }
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}
impl CFG {
    pub(crate) fn new() -> Self {
        Self {
            nodes: vec![],
            edges: HashSet::new(),
            successors: HashMap::new(),
            predecessors: HashMap::new(),
            dominated: HashMap::new(),
            post_dominated: HashMap::new(),
            constructs: vec![],
        }
    }
    pub(crate) fn generate_cfg(
        instructions: &Vec<Instruction>,
        num_work_groups: u32,
        work_group_size: u32,
    ) -> Self {
        let mut cfg = CFG::new();
        let nodes: Vec<Node> =
            Self::generate_blocks(instructions, num_work_groups, work_group_size);
        cfg.generate_edges(instructions, &nodes);
        cfg.nodes = nodes;
        cfg.dominated = Self::compute_dominated_blocks(&cfg, cfg.nodes[0].op_label_idx);
        cfg.post_dominated =
            Self::compute_post_dominated_blocks(&cfg, cfg.nodes.last().unwrap().op_label_idx);
        cfg.generate_constructs();
        cfg
    }

    fn generate_blocks(
        instructions: &Vec<Instruction>,
        num_work_groups: u32,
        work_group_size: u32,
    ) -> Vec<Node> {
        let mut current_block_idx = 0;
        let mut nodes: Vec<Node> = vec![];
        for (idx, instruction) in instructions.iter().enumerate() {
            if instruction.name == InstructionName::Label {
                // find the nearest termination instruction
                let (termination_inst_idx, termination_inst) = instructions
                    .iter()
                    .enumerate()
                    .find(|(inst_idx, inst)| {
                        *inst_idx > idx && TERMINATION_INSTRUCTIONS.contains(&inst.name)
                    })
                    .expect("CFG: unable to find termination instruction");

                let tangle = {
                    // entry block
                    if current_block_idx == 0 {
                        (0..num_work_groups)
                            .map(|workgroup_id| {
                                (1..=work_group_size)
                                    .map(move |local_tid| {
                                        workgroup_id * work_group_size + local_tid
                                    })
                                    .collect::<HashSet<u32>>()
                            })
                            .collect()
                    } else {
                        (0..num_work_groups)
                            .map(|workgroup_id| HashSet::new())
                            .collect()
                    }
                };

                let initialized = {
                    if current_block_idx == 0 {
                        (0..num_work_groups).map(|_| true).collect::<Vec<bool>>()
                    } else {
                        (0..num_work_groups).map(|_| false).collect::<Vec<bool>>()
                    }
                };

                let construct_type = {
                    match instructions[termination_inst_idx - 1].name {
                        InstructionName::SelectionMerge => {
                            if termination_inst.name == InstructionName::BranchConditional {
                                ConstructType::Selection
                            } else if termination_inst.name == InstructionName::Switch {
                                ConstructType::Switch
                            } else {
                                ConstructType::None
                            }
                        }
                        InstructionName::LoopMerge => ConstructType::Loop,
                        _ => ConstructType::None,
                    }
                };

                let merge_block = {
                    if MERGE_INSTRUCTIONS.contains(&instructions[termination_inst_idx - 1].name) {
                        instructions[termination_inst_idx - 1].arguments.arguments[0]
                            .value
                            .parse()
                            .unwrap() as i32
                    } else {
                        -1
                    }
                };

                let continue_block = {
                    if instructions[termination_inst_idx - 1].name == InstructionName::LoopMerge {
                        instructions[termination_inst_idx - 1].arguments.arguments[1]
                            .value
                            .parse()
                            .unwrap() as i32
                    } else {
                        -1
                    }
                };

                let (default_block, case_blocks) = Self::find_switch_default_targets(
                    current_block_idx as u32,
                    termination_inst_idx as u32,
                    instructions,
                );

                nodes.push(Node {
                    op_label_idx: (idx + 1) as u32,
                    termination_inst_idx: (termination_inst_idx + 1) as u32,
                    tangle,
                    merge: false,
                    initialize: initialized,
                    construct_type,
                    merge_block,
                    continue_block,
                    default_block,
                    case_blocks: case_blocks.into_iter().collect(),
                });
                current_block_idx += 1;
            }
        }
        nodes
    }

    fn generate_edges(&mut self, instructions: &Vec<Instruction>, nodes: &Vec<Node>) {
        for node in nodes.iter() {
            let source = node.op_label_idx;
            let targets = Self::find_target_blocks(
                node.op_label_idx - 1,
                node.termination_inst_idx - 1,
                instructions,
            );
            for &target in &targets {
                self.add_edge(source, target);
            }
        }
    }

    fn generate_constructs(&mut self) {
        let nodes = self.nodes.clone();
        // 1. Identify loop constructs
        for node in &nodes {
            if node.construct_type == ConstructType::Loop {
                self.identify_loop_construct(
                    node.op_label_idx,
                    node.merge_block as u32,
                    node.continue_block as u32,
                );
                self.identify_continue_construct(
                    node.continue_block as u32,
                    Self::find_back_edge_block(&self, node.op_label_idx).unwrap(),
                );
            } else if node.construct_type == ConstructType::Selection {
                self.identify_selection_construct(node.op_label_idx, node.merge_block as u32);
            } else if node.construct_type == ConstructType::Switch {
                self.identify_switch_construct(node.op_label_idx, node.merge_block as u32);
                for target in &node.case_blocks {
                    self.identify_case_construct(*target as u32, node.merge_block as u32);
                }
                self.identify_case_construct(node.default_block as u32, node.merge_block as u32);
            }
        }
    }

    fn identify_selection_construct(&mut self, header: u32, merge_block: u32) {
        let mut selection_blocks = HashSet::new();

        // Get all blocks dominated by the header
        if let Some(dominated_blocks) = self.dominated.get(&header) {
            for &block in dominated_blocks {
                if !self
                    .dominated
                    .get(&merge_block)
                    .unwrap_or(&HashSet::new())
                    .contains(&block)
                {
                    selection_blocks.insert(block);
                }
            }
        }

        self.constructs.push(ControlFlowConstruct {
            construct_type: ConstructType::Selection,
            header_block: header,
            merge_block: merge_block as i32,
            continue_target: -1,
            blocks: selection_blocks,
        });
    }

    fn identify_loop_construct(&mut self, header: u32, merge_block: u32, continue_target: u32) {
        let mut loop_blocks = HashSet::new();

        // zheyuan: for now we are not considering explicit continue instruction, so the back edge block is the continue target
        if let Some(dominated_blocks) = self.dominated.get(&header) {
            for &block in dominated_blocks {
                if !self
                    .dominated
                    .get(&continue_target)
                    .unwrap_or(&HashSet::new())
                    .contains(&block)
                    && !self
                        .dominated
                        .get(&merge_block)
                        .unwrap_or(&HashSet::new())
                        .contains(&block)
                {
                    loop_blocks.insert(block);
                }
            }
        }

        self.constructs.push(ControlFlowConstruct {
            construct_type: ConstructType::Loop,
            header_block: header,
            merge_block: merge_block as i32,
            continue_target: continue_target as i32,
            blocks: loop_blocks,
        });
    }

    fn identify_continue_construct(&mut self, continue_target: u32, back_edge_block: u32) {
        let mut continue_blocks = HashSet::new();

        if let Some(dominated_blocks) = self.dominated.get(&continue_target) {
            if let Some(post_dominated_blocks) = self.post_dominated.get(&back_edge_block) {
                for &block in dominated_blocks {
                    if post_dominated_blocks.contains(&block) {
                        continue_blocks.insert(block);
                    }
                }
            }
        }

        self.constructs.push(ControlFlowConstruct {
            construct_type: ConstructType::Continue,
            header_block: continue_target,
            merge_block: -1,
            continue_target: back_edge_block as i32,
            blocks: continue_blocks,
        });
    }

    fn identify_switch_construct(&mut self, header: u32, merge_block: u32) {
        let mut switch_blocks = HashSet::new();

        if let Some(dominated_blocks) = self.dominated.get(&header) {
            for &block in dominated_blocks {
                if !self
                    .dominated
                    .get(&merge_block)
                    .unwrap_or(&HashSet::new())
                    .contains(&block)
                {
                    switch_blocks.insert(block);
                }
            }
        }

        self.constructs.push(ControlFlowConstruct {
            construct_type: ConstructType::Switch,
            header_block: header,
            merge_block: merge_block as i32,
            continue_target: -1,
            blocks: switch_blocks,
        });
    }

    fn identify_case_construct(&mut self, target_block: u32, merge_block: u32) {
        let mut case_blocks = HashSet::new();

        if let Some(dominated_blocks) = self.dominated.get(&target_block) {
            for &block in dominated_blocks {
                if !self
                    .dominated
                    .get(&merge_block)
                    .unwrap_or(&HashSet::new())
                    .contains(&block)
                {
                    case_blocks.insert(block);
                }
            }
        }

        self.constructs.push(ControlFlowConstruct {
            construct_type: ConstructType::Case,
            header_block: target_block,
            merge_block: merge_block as i32,
            continue_target: -1,
            blocks: case_blocks,
        });
    }

    fn find_switch_default_targets(
        op_label_idx: u32,
        termination_inst_idx: u32,
        instructions: &Vec<Instruction>,
    ) -> (i32, HashSet<i32>) {
        let mut targets = HashSet::new();
        if termination_inst_idx <= op_label_idx {
            return (-1, targets);
        }
        let mut default_block = -1;
        let inst = &instructions[termination_inst_idx as usize];
        match inst.name {
            InstructionName::Switch => {
                default_block = inst.arguments.arguments[1].value.parse().unwrap() as i32;
                if let Some(cases) = &inst.vec_arguments {
                    for label in &cases[1].arguments {
                        targets.insert(label.value.parse().unwrap() as i32);
                    }
                }
            }
            _ => {}
        }

        (default_block, targets)
    }

    fn find_target_blocks(
        op_label_idx: u32,
        termination_inst_idx: u32,
        instructions: &Vec<Instruction>,
    ) -> HashSet<u32> {
        let mut targets = HashSet::new();
        if termination_inst_idx <= op_label_idx {
            return targets;
        }
        let merge_inst = &instructions[termination_inst_idx as usize - 1];
        let inst = &instructions[termination_inst_idx as usize];
        match inst.name {
            InstructionName::Branch => {
                targets.insert(inst.arguments.arguments[0].value.parse().unwrap());
            }
            InstructionName::BranchConditional => {
                targets.insert(inst.arguments.arguments[1].value.parse().unwrap());
                targets.insert(inst.arguments.arguments[2].value.parse().unwrap());
            }
            InstructionName::Switch => {
                let default_block = inst.arguments.arguments[1].value.parse().unwrap();
                targets.insert(default_block);
                if let Some(cases) = &inst.vec_arguments {
                    for label in &cases[1].arguments {
                        targets.insert(label.value.parse().unwrap());
                    }
                }
            }
            _ => {}
        }

        if MERGE_INSTRUCTIONS.contains(&merge_inst.name) {
            match merge_inst.name {
                InstructionName::SelectionMerge => {
                    let merge_block = merge_inst.arguments.arguments[0].value.parse().unwrap();
                    targets.insert(merge_block);
                }
                InstructionName::LoopMerge => {
                    let merge_block = merge_inst.arguments.arguments[0].value.parse().unwrap();
                    let continue_block = merge_inst.arguments.arguments[1].value.parse().unwrap();
                    targets.insert(merge_block);
                    targets.insert(continue_block);
                }
                _ => {}
            }
        }

        targets
    }

    fn find_back_edge_block(cfg: &CFG, header: u32) -> Option<u32> {
        for edge in &cfg.edges {
            // Check if `to` has a lower op_label_idx than `from`
            if edge.0 > edge.1 && edge.1 == header {
                // If true, `from` is a back-edge block
                return Some(edge.0);
            }
        }
        None
    }

    fn add_edge(&mut self, from: u32, to: u32) {
        self.edges.insert(Edge(from, to));
        self.successors.entry(from).or_default().insert(to);
        self.predecessors.entry(to).or_default().insert(from);
    }

    fn reverse(&self) -> Self {
        let mut reversed_cfg = CFG::new();
        for (&node, succs) in &self.successors {
            for &succ in succs {
                reversed_cfg.add_edge(succ, node);
            }
        }
        reversed_cfg.nodes = self.nodes.clone();
        reversed_cfg
    }

    fn traverse_tree(
        node: u32,
        dom_tree: &HashMap<u32, Vec<u32>>,
        dominated_blocks: &mut HashMap<u32, HashSet<u32>>,
    ) {
        // The node dominates itself
        dominated_blocks.get_mut(&node).unwrap().insert(node);
        if let Some(children) = dom_tree.get(&node) {
            for &child in children {
                dominated_blocks.get_mut(&node).unwrap().insert(child);

                // Recursively populate the dominated nodes for each child
                Self::traverse_tree(child, dom_tree, dominated_blocks);

                // Extend parent’s dominated set with child’s dominated set
                if let Some(child_dominated) = dominated_blocks.get(&child).cloned() {
                    dominated_blocks
                        .get_mut(&node)
                        .unwrap()
                        .extend(child_dominated);
                }
            }
        }
    }
    fn compute_dominators(cfg: &CFG, start_node: u32) -> HashMap<u32, HashSet<u32>> {
        let mut dom = HashMap::new();

        // Initialize each node's dominator set to all nodes, except start node, which only dominates itself.
        for node in &cfg.nodes {
            let initial_set: HashSet<u32> = if node.op_label_idx == start_node {
                HashSet::from([start_node])
            } else {
                HashSet::from(
                    cfg.nodes
                        .iter()
                        .map(|n| n.op_label_idx)
                        .into_iter()
                        .collect::<HashSet<u32>>(),
                )
            };
            dom.insert(node.op_label_idx, initial_set);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for node in &cfg.nodes {
                if node.op_label_idx == start_node {
                    continue; // Start node dominates only itself
                }

                // Compute the new dominator set: intersection of dominators of all predecessors
                let preds = cfg.predecessors.get(&node.op_label_idx);
                let mut new_dom: HashSet<u32> = cfg
                    .nodes
                    .iter()
                    .map(|n| n.op_label_idx)
                    .into_iter()
                    .collect(); // Start with all nodes
                                // in case some node does not have predecessors
                if let Some(valid_preds) = preds {
                    for &pred in valid_preds {
                        if let Some(pred_dom) = dom.get(&pred) {
                            new_dom = new_dom.intersection(pred_dom).cloned().collect();
                        }
                    }
                }
                new_dom.insert(node.op_label_idx); // Add the node itself

                // Update and check for changes
                if dom.get(&node.op_label_idx) != Some(&new_dom) {
                    dom.insert(node.op_label_idx, new_dom);
                    changed = true;
                }
            }
        }
        dom
    }

    // Build the dominator tree from the dominator sets
    fn compute_dominator_tree(
        dom: &HashMap<u32, HashSet<u32>>,
        start_node: u32,
    ) -> HashMap<u32, Vec<u32>> {
        let mut dom_tree = HashMap::new();

        for (&node, dominators) in dom {
            let immediate_dom = dominators
                .iter()
                .filter(|&&dom_node| dom_node != node)
                .max_by_key(|&&dom_node| dom.get(&dom_node).unwrap_or(&HashSet::new()).len());

            if let Some(&imm_dom) = immediate_dom {
                dom_tree.entry(imm_dom).or_insert_with(Vec::new).push(node);
            }
        }

        dom_tree
    }

    fn compute_dominated_blocks(cfg: &CFG, start_node: u32) -> HashMap<u32, HashSet<u32>> {
        // Step 1: Compute dominators of each node
        let dominators = Self::compute_dominators(cfg, start_node);
        // Step 2: Build the dominator tree from dominators
        let dom_tree = Self::compute_dominator_tree(&dominators, start_node);
        // Step 3: Traverse the dominator tree to compute dominated blocks for each node
        let mut dominated_blocks = HashMap::new();
        for &node in dominators.keys() {
            dominated_blocks.insert(node, HashSet::new());
        }

        // Start traversal from the start node
        Self::traverse_tree(start_node, &dom_tree, &mut dominated_blocks);
        dominated_blocks
    }

    fn compute_post_dominators(cfg: &CFG, exit_node: u32) -> HashMap<u32, HashSet<u32>> {
        let reversed_cfg = cfg.reverse();
        Self::compute_dominators(&reversed_cfg, exit_node)
    }

    fn compute_post_dominator_tree(
        post_dom: &HashMap<u32, HashSet<u32>>,
        exit_node: u32,
    ) -> HashMap<u32, Vec<u32>> {
        let mut post_dom_tree = HashMap::new();

        for (&node, post_dominators) in post_dom {
            // The immediate post-dominator of `node` is the closest post-dominator that is not itself
            let immediate_post_dom = post_dominators
                .iter()
                .filter(|&&post_dom_node| post_dom_node != node) // Exclude the node itself
                .max_by_key(|&&dom_node| post_dom.get(&dom_node).unwrap_or(&HashSet::new()).len()); // Closest post-dominator

            if let Some(&imm_post_dom) = immediate_post_dom {
                post_dom_tree
                    .entry(imm_post_dom)
                    .or_insert_with(Vec::new)
                    .push(node);
            }
        }

        post_dom_tree
    }

    fn compute_post_dominated_blocks(cfg: &CFG, exit_node: u32) -> HashMap<u32, HashSet<u32>> {
        // Step 1: Compute post-dominators of each node
        let post_dominators = Self::compute_post_dominators(cfg, exit_node);

        // Step 2: Build the post-dominator tree from post-dominators
        let post_dom_tree = Self::compute_post_dominator_tree(&post_dominators, exit_node);

        // Step 3: Traverse the post-dominator tree to compute post-dominated blocks for each node
        let mut post_dominated_blocks = HashMap::new();
        for &node in post_dominators.keys() {
            post_dominated_blocks.insert(node, HashSet::new());
        }

        // Start traversal from the exit node
        Self::traverse_tree(exit_node, &post_dom_tree, &mut post_dominated_blocks);

        post_dominated_blocks
    }
}

mod test {
    use super::*;
    #[test]
    fn test_edge() {}

    #[test]
    fn test_node() {}

    #[test]
    fn test_dominators() {}

    #[test]
    fn test_post_dominators() {}
}
