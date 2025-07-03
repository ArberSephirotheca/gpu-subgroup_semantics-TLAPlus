//! constant.rs is used to store the constant value defined by OpConstant or OpConstantComposite in the codegen module.

use std::fmt::Display;

#[derive(Debug)]
pub enum ConstantType {
    Bool(bool),
    String(String),
    Int(i32),
    Uint(u32),
}

#[derive(Debug)]
pub struct Constant {
    pub name: String,
    pub value: ConstantType,
}

impl Display for ConstantType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantType::Bool(b) => write!(f, "{}", b),
            ConstantType::String(s) => write!(f, "{}", s),
            ConstantType::Int(i) => write!(f, "{}", i),
            ConstantType::Uint(u) => write!(f, "{}", u),
        }
    }
}
