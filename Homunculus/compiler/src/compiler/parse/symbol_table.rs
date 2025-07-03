//! We have two tables: one for types and one for variables.
//! for type table, we have a struct SpirvTypeTable with a method insert and lookup
//! Whenever we encounter a type declaration (e.g. `OpTypeInt`, `OpTypeBool`, or complex type like `OpTypeStruct`), we add it to the type table
//! Currently supported types are `OpTypeBool`, `OpTypeInt, `OpTypeVector`, `OpTypeArray`, `OpTypeRuntimeArray`, `OpTypeStruct`, `OpTypePointer`
//! for variable table, we have a struct SymbolTable with a method insert and lookup
//! Whenever we encounter a variable declaration (e.g. `OpVariable`), we add it to the variable table
use crate::codegen::common::{IndexKind, InstructionValue};

use super::syntax::TokenKind;
use std::{
    collections::HashMap,
    fmt::{self, Display},
};
type VariableSymbol = String;
type TypeSymbol = String;
type ConstantSymbol = String;
type SSAID = String;
type Label = String;
type Position = u32;

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum StorageClass {
    // Uniform, Input and Output in SPIR-V are all Global in our case
    Global,
    // Workgroup in SPIR-V is Shared in our case
    Shared,
    // Function in SPIR-V is Local in our case
    Local,
    // This is for intermediate SSA variables
    Intermediate,
    // This is for constant variables
    Constant,
}

impl fmt::Display for StorageClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StorageClass::Global => write!(f, "global"),
            StorageClass::Shared => write!(f, "shared"),
            StorageClass::Local => write!(f, "local"),
            StorageClass::Intermediate => write!(f, "intermediate"),
            StorageClass::Constant => write!(f, "constant"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BuiltInVariable {
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

impl BuiltInVariable {
    pub fn cast(token: TokenKind) -> Self {
        match token {
            TokenKind::NumWorkgroups => BuiltInVariable::NumWorkgroups,
            TokenKind::WorkgroupSize => BuiltInVariable::WorkgroupSize,
            TokenKind::WorkgroupId => BuiltInVariable::WorkgroupId,
            TokenKind::LocalInvocationId => BuiltInVariable::LocalInvocationId,
            TokenKind::GlobalInvocationId => BuiltInVariable::GlobalInvocationId,
            TokenKind::SubgroupSize => BuiltInVariable::SubgroupSize,
            TokenKind::NumSubgroups => BuiltInVariable::NumSubgroups,
            TokenKind::SubgroupId => BuiltInVariable::SubgroupId,
            TokenKind::SubgroupLocalInvocationId => BuiltInVariable::SubgroupLocalInvocationId,
            _ => panic!("Invalid BuiltInVariable {}", token),
        }
    }
}

/// each time we encounter a type declaration, we add it to the type table
/// for high level type like array and struct, we store the symbol of the element type
/// for low level type like int and bool, we store the type directly
#[derive(Debug, PartialEq, Clone)]
pub(crate) enum SpirvType {
    Void,
    Function {
        return_type: TypeSymbol,
    },
    Bool,
    Int {
        width: u32,
        signed: bool,
    },
    Vector {
        element: TypeSymbol,
        count: u32,
    },
    Array {
        element: TypeSymbol,
        count: u32,
    },
    RuntimeArray {
        element: TypeSymbol,
    },
    Struct {
        members: TypeSymbol,
    },
    Pointer {
        ty: TypeSymbol,
        storage_class: StorageClass,
    },
    // AccessChain {
    //     ty: TypeSymbol,
    //     base: VariableSymbol,
    //     index: String,
    // },
}

/// each time we encounter a constant declaration, we add it to the constant table
#[derive(Debug, PartialEq, Clone)]
pub(crate) enum ConstantInfo {
    Int {
        width: u32,
        signed: bool,
        value: i32,
    },
    Bool {
        value: bool,
    },
    // Float{
    //     width: u32,
    //     value: f32,
    // },
}

impl Display for ConstantInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstantInfo::Int { value, .. } => write!(f, "{}", value),
            ConstantInfo::Bool { value } => {
                if *value {
                    write!(f, "TRUE")
                } else {
                    write!(f, "FALSE")
                }
            }
        }
    }
}

impl ConstantInfo {
    pub(crate) fn to_text(&self) -> String {
        match self {
            ConstantInfo::Int { value, .. } => value.to_string(),
            ConstantInfo::Bool { value } => value.to_string(),
        }
    }
    pub fn new_int(value: i32, signed: bool) -> Self {
        Self::Int {
            width: 32,
            signed,
            value,
        }
    }
    pub fn new_bool(value: bool) -> Self {
        Self::Bool { value }
    }
    pub fn get_int_value(&self) -> i32 {
        match self {
            ConstantInfo::Int { value, .. } => *value,
            _ => panic!("Invalid constant type for get_int_value"),
        }
    }
    pub fn get_bool_value(&self) -> bool {
        match self {
            ConstantInfo::Bool { value } => *value,
            _ => panic!("Invalid constant type for get_bool_value"),
        }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            ConstantInfo::Int { signed, .. } => *signed,
            _ => panic!("Invalid constant type for is_signed"),
        }
    }
}
// Type table, mapping result ID to SpirvType
#[derive(Debug)]
pub struct SpirvTypeTable {
    types: HashMap<String, SpirvType>,
}

impl SpirvTypeTable {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
        }
    }
    pub fn insert(&mut self, id: String, ty: SpirvType) {
        self.types.insert(id, ty);
    }

    pub fn lookup(&self, id: &str) -> Option<&SpirvType> {
        self.types.get(id)
    }
}

// Define a step in the access chain
#[derive(Debug, PartialEq, Clone)]
pub enum AccessStep {
    ConstIndex(i32),               // Constant index
    VariableIndex(VariableSymbol), // Variable index
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableInfo {
    pub ssa_id: String,
    pub id: String,
    pub ty: SpirvType,
    pub access_chain: Vec<AccessStep>,
    pub storage_class: StorageClass,
    pub const_value: Option<ConstantInfo>,
    pub built_in: Option<BuiltInVariable>,
    pub default_value: InstructionValue,
}

impl VariableInfo {
    pub fn new(
        // id is the variable name in the source code
        // it is different from the SSA name as it may be reused
        // by multiple variables in different scopes
        // such as OpAccessChain and OpLoad
        ssa_id: String,
        id: String,
        ty: SpirvType,
        access_chain: Vec<AccessStep>,
        storage_class: StorageClass,
        const_value: Option<ConstantInfo>,
        built_in: Option<BuiltInVariable>,
        default_value: InstructionValue,
    ) -> Self {
        Self {
            ssa_id,
            id,
            ty,
            access_chain,
            storage_class,
            const_value,
            built_in,
            default_value,
        }
    }

    pub(crate) fn new_const_int(id: String, value: i32, signed: bool) -> Self {
        Self {
            ssa_id: id.clone(),
            id,
            ty: SpirvType::Int { width: 32, signed },
            access_chain: vec![],
            storage_class: StorageClass::Constant,
            const_value: Some(ConstantInfo::new_int(value, signed)),
            built_in: None,
            default_value: InstructionValue::Int(value),
        }
    }
    pub(crate) fn new_const_bool(id: String, value: bool) -> Self {
        Self {
            ssa_id: id.clone(),
            id,
            ty: SpirvType::Bool,
            access_chain: vec![],
            storage_class: StorageClass::Constant,
            const_value: Some(ConstantInfo::new_bool(value)),
            built_in: None,
            default_value: InstructionValue::Bool(value),
        }
    }

    pub(crate) fn get_ssa_name(&self) -> String {
        self.ssa_id.clone()
    }
    pub(crate) fn get_var_name(&self) -> String {
        self.id.clone()
    }
    pub(crate) fn is_builtin(&self) -> bool {
        self.built_in.is_some()
    }

    pub(crate) fn get_builtin(&self) -> Option<BuiltInVariable> {
        self.built_in.clone()
    }
    pub(crate) fn get_ty(&self) -> SpirvType {
        self.ty.clone()
    }

    pub(crate) fn get_storage_class(&self) -> StorageClass {
        self.storage_class.clone()
    }

    pub(crate) fn initial_value(&self) -> InstructionValue {
        self.default_value.clone()
    }

    // FIXME: implement array and struct
    pub(crate) fn get_index(&self) -> IndexKind {
        match &self.ty {
            _ => IndexKind::Literal(-1),
        }
    }
    pub(crate) fn is_intermediate(&self) -> bool {
        if self.get_storage_class() == StorageClass::Intermediate {
            true
        } else {
            false
        }
    }

    pub(crate) fn is_global(&self) -> bool {
        if self.get_storage_class() == StorageClass::Global {
            true
        } else {
            false
        }
    }

    pub(crate) fn is_shared(&self) -> bool {
        if self.get_storage_class() == StorageClass::Shared {
            true
        } else {
            false
        }
    }

    pub(crate) fn is_local(&self) -> bool {
        if self.get_storage_class() == StorageClass::Local {
            true
        } else {
            false
        }
    }

    pub(crate) fn is_constant(&self) -> bool {
        if self.get_storage_class() == StorageClass::Constant {
            true
        } else {
            false
        }
    }

    pub(crate) fn get_constant_info(&self) -> ConstantInfo {
        if self.is_constant() {
            self.const_value.clone().unwrap()
        } else {
            panic!("Not a constant variable");
        }
    }
    pub(crate) fn get_constant_int(&self) -> i32 {
        if self.is_constant() {
            match &self.const_value {
                Some(ConstantInfo::Int { value, .. }) => *value,
                _ => panic!("Invalid constant type for get_constant_int"),
            }
        } else {
            panic!("Not a constant variable");
        }
    }

    pub(crate) fn get_constant_bool(&self) -> bool {
        if self.is_constant() {
            match &self.const_value {
                Some(ConstantInfo::Bool { value }) => *value,
                _ => panic!("Invalid constant type for get_constant_bool"),
            }
        } else {
            panic!("Not a constant variable");
        }
    }
}

pub struct VariableInfoBuilder {
    ty: Option<SpirvType>,
    storage_class: Option<StorageClass>,
    built_in: Option<BuiltInVariable>,
}

// Represents a scope level in the symbol table
// key is the SSA name of the variable
type Scope = HashMap<SSAID, VariableInfo>;

// Represents the entire symbol table with multiple scopes
#[derive(Debug)]
pub struct VariableSymbolTable {
    global: Scope,
    shared: Scope,
    local: Scope,
    constant: Scope,
    Indexing: Scope,
}

impl VariableSymbolTable {
    // Create a new, empty symbol table
    pub fn new() -> Self {
        Self {
            global: HashMap::new(),
            shared: HashMap::new(),
            local: HashMap::new(),
            constant: HashMap::new(),
            Indexing: HashMap::new(),
        }
    }

    // Insert a new variable declaration into the current scope
    pub fn insert(&mut self, var_name: String, var_info: VariableInfo) {
        if !var_info.access_chain.is_empty() {
            self.Indexing.insert(var_name, var_info);
        } else {
            match var_info.storage_class {
                StorageClass::Global => {
                    self.global.insert(var_name, var_info);
                }
                StorageClass::Shared => {
                    self.shared.insert(var_name, var_info);
                }
                StorageClass::Local => {
                    self.local.insert(var_name, var_info);
                }
                StorageClass::Intermediate => {
                    self.local.insert(var_name, var_info);
                }
                StorageClass::Constant => {
                    self.constant.insert(var_name, var_info);
                }
            }
        }
    }

    // Lookup a variable by name, searching from the innermost scope outward
    pub fn lookup(&self, name: &str) -> Option<VariableInfo> {
        if let Some(var) = self.Indexing.get(name) {
            return Some(var.clone());
        }
        if let Some(var) = self.local.get(name) {
            return Some(var.clone());
        }
        if let Some(var) = self.shared.get(name) {
            return Some(var.clone());
        }
        if let Some(var) = self.global.get(name) {
            return Some(var.clone());
        }
        if let Some(var) = self.constant.get(name) {
            return Some(var.clone());
        }
        None
    }

    pub fn get_global_variables(&self) -> Vec<VariableInfo> {
        let global: Vec<VariableInfo> = self
            .global
            .values()
            .cloned()
            .filter(|val| !val.is_builtin())
            .collect();
        global
    }
}

pub struct ConstantSymbolTable {
    constants: HashMap<String, ConstantInfo>,
}

impl ConstantSymbolTable {
    pub fn new() -> Self {
        Self {
            constants: HashMap::new(),
        }
    }

    pub fn insert(&mut self, id: String, constant: ConstantInfo) {
        self.constants.insert(id, constant);
    }

    pub fn lookup(&self, id: &str) -> Option<&ConstantInfo> {
        self.constants.get(id)
    }
}

#[derive(Debug)]
pub struct LabelTable {
    labels: HashMap<Label, Position>,
}

impl LabelTable {
    pub fn new() -> Self {
        Self {
            labels: HashMap::new(),
        }
    }

    pub fn insert(&mut self, label: Label, position: Position) {
        self.labels.insert(label, position);
    }

    pub fn lookup(&self, label: &str) -> Option<&Position> {
        self.labels.get(label)
    }
}
// lazy_static! {
//     pub static ref TYPE_TABLE: SpirvTypeTable = {
//         let mut table = SpirvTypeTable::new();
//         table
//     };
// }
