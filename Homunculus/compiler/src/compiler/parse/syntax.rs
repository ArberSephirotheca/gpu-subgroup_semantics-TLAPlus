use logos::Logos;
use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::{FromPrimitive, ToPrimitive};
use std::fmt;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AsukaLanguage {}

impl rowan::Language for AsukaLanguage {
    type Kind = TokenKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        Self::Kind::from_u16(raw.0).unwrap()
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.to_u16().unwrap())
    }
}

pub(crate) type SyntaxNode = rowan::SyntaxNode<AsukaLanguage>;
pub(crate) type SyntaxToken = rowan::SyntaxToken<AsukaLanguage>;
pub(crate) type SyntaxElement = rowan::SyntaxElement<AsukaLanguage>;

#[derive(Debug, PartialEq, Clone, Default)]
pub enum LexingError {
    OpUnsupported(String),
    #[default]
    Other,
}

// impl From<std::string::ParseError> for LexingError {
//     fn from(_: std::string::ParseError) -> Self {
//         LexingError::OpUnsupported
//     }
// }

/// This set is used to distinguish between instructions that are not supported by the parser and the ones that are ignored
pub(crate) static IGNORED_INSTRUCTION_SET: [TokenKind; 15] = [
    TokenKind::OpMemberDecorate,
    TokenKind::OpCapability,
    TokenKind::OpExtension,
    TokenKind::OpExtInstImport,
    TokenKind::OpMemoryModel,
    // fixme: OpEntryPoint is needed when we support function calls
    TokenKind::OpEntryPoint,
    TokenKind::OpSource,
    TokenKind::OpSourceExtension,
    TokenKind::OpName,
    TokenKind::OpMemberName,
    TokenKind::OpMemberDecorate,
    TokenKind::OpTypeFunction,
    TokenKind::OpFunction,
    TokenKind::OpFunctionEnd,
    TokenKind::OpConstantComposite,
];

pub(crate) static BUILT_IN_VARIABLE_SET: [TokenKind; 9] = [
    TokenKind::NumWorkgroups,
    TokenKind::WorkgroupSize,
    TokenKind::WorkgroupId,
    TokenKind::LocalInvocationId,
    TokenKind::GlobalInvocationId,
    TokenKind::SubgroupLocalInvocationId,
    TokenKind::SubgroupSize,
    TokenKind::NumSubgroups,
    TokenKind::SubgroupId,
];

pub(crate) static TLA_BUILTIN_SET: [TokenKind; 4] = [
    TokenKind::Scheduler,
    TokenKind::TlaNumWorkgroups,
    TokenKind::TlaSubgroupSize,
    TokenKind::TlaSynchronizationId,
];

// fn instruction_not_supported(instruction: &str) -> bool {
//     for i in INSTRUCTION_SET.iter() {
//         if i == &instruction {
//             return false;
//         }
//     }
//     true
// }

#[derive(
    Debug, Hash, Eq, PartialOrd, Ord, Copy, Clone, PartialEq, Logos, FromPrimitive, ToPrimitive,
)]
#[logos(error = LexingError)]
pub enum TokenKind {
    VariableRef,
    VariableDef,
    IgnoredOp,

    // Control flow Statement
    BranchConditionalStatement,
    BranchStatement,
    SwitchStatement,
    ControlBarrierStatement,

    // Statement
    ExecutionModeStatement,
    DecorateStatement,
    MemberDecorateStatement,
    DecorateStringStatement,
    ReturnStatement,
    FunctionEndStatement,
    StoreStatement,
    AtomicStoreStatement,

    // merge instruction
    LoopMergeStatement,
    SelectionMergeStatement,

    // Expression
    // FunctionExpr,
    VariableExpr,
    AccessChainExpr,
    LabelExpr,
    ConstantExpr,
    ConstantCompositeExpr,
    ConstantTrueExpr,
    ConstantFalseExpr,
    LogicalOrExpr,
    LogicalAndExpr,
    LogicalEqualExpr,
    LogicalNotEqualExpr,
    LogicalNotExpr,
    ShiftLeftLogicalExpr,
    ShiftRightLogicalExpr,
    AtomicOrExpr,
    AtomicAndExpr,
    LoadExpr,
    AtomicLoadExpr,
    AddExpr,
    AtomicAddExpr,
    SubExpr,
    AtomicSubExpr,
    MulExpr,
    ModExpr,
    EqualExpr,
    NotEqualExpr,
    GreaterThanExpr,
    GreaterThanEqualExpr,
    LessThanExpr,
    LessThanEqualExpr,
    AtomicExchangeExpr,
    AtomicCompareExchangeExpr,
    GroupAllExpr,
    GroupAnyExpr,
    GroupNonUniformAllExpr,
    GroupNonUniformAllEqualExpr,
    GroupNonUniformAnyExpr,
    GroupNonUniformBroadcastExpr,
    BitwiseOrExpr,
    BitwiseAndExpr,
    BitcastExpr,

    // Type expression
    TypeBoolExpr,
    TypeIntExpr,
    TypeVoidExpr,
    TypeFunctionExpr,
    TypeVectorExpr,
    TypeArrayExpr,
    TypeRuntimeArrayExpr,
    TypeStructExpr,
    TypePointerExpr,

    Root,
    Statement,
    Error,

    // Built-in variables
    #[regex("LocalSize")]
    LocalSize,
    #[regex("NumWorkgroups")]
    NumWorkgroups,
    #[regex("WorkgroupSize")]
    WorkgroupSize,
    #[regex("WorkgroupId")]
    WorkgroupId,
    #[regex("LocalInvocationId")]
    LocalInvocationId,
    #[regex("GlobalInvocationId")]
    GlobalInvocationId,
    #[regex("SubgroupSize")]
    SubgroupSize,
    #[regex("NumSubgroups")]
    NumSubgroups,
    #[regex("SubgroupId")]
    SubgroupId,
    #[regex("SubgroupLocalInvocationId")]
    SubgroupLocalInvocationId,
    #[regex("%scheduler")]
    Scheduler,
    #[regex("%tla_synchronization_id")]
    TlaSynchronizationId,
    #[regex("%tla_num_workgroups")]
    TlaNumWorkgroups,
    #[regex("%tla_subgroup_size")]
    TlaSubgroupSize,
    #[regex("UserSemantic")]
    UserSemantic,

    #[regex("OpDecorate")]
    OpDecorate,
    #[regex("OpMemberDecorate")]
    OpMemberDecorate,
    #[regex("OpDecorateString")]
    OpDecorateString,
    #[regex("OpExecutionMode")]
    OpExecutionMode,
    #[regex("OpCapability")]
    OpCapability,
    #[regex("OpExtension")]
    OpExtension,
    #[regex("OpExtInstImport")]
    OpExtInstImport,
    #[regex("OpMemoryModel")]
    OpMemoryModel,
    #[regex("OpEntryPoint")]
    OpEntryPoint,
    #[regex("OpSource")]
    OpSource,
    #[regex("OpSourceExtension")]
    OpSourceExtension,
    #[regex("BuiltIn")]
    BuiltIn,
    #[regex("None")]
    None,

    // Primitive Type instruction
    #[regex("OpTypeBool")]
    OpTypeBool,
    #[regex("OpTypeInt")]
    OpTypeInt,
    #[regex("OpTypeVoid")]
    OpTypeVoid,

    // High-level Type instruction
    #[regex("OpTypeVector")]
    OpTypeVector,
    #[regex("OpTypeArray")]
    OpTypeArray,
    #[regex("OpTypeRuntimeArray")]
    OpTypeRuntimeArray,
    #[regex("OpTypeStruct")]
    OpTypeStruct,
    #[regex("OpTypePointer")]
    OpTypePointer,
    #[regex("OpTypeFunction")]
    OpTypeFunction,

    // Storage Class

    // OpName is the variable name
    #[regex("OpName")]
    OpName,
    // OpMemberName is the member name in the layout
    #[regex("OpMemberName")]
    OpMemberName,
    #[regex("OpFunction")]
    OpFunction,
    #[regex("OpFunctionEnd")]
    OpFunctionEnd,

    #[regex("OpVariable")]
    OpVariable,
    #[regex("OpAccessChain")]
    OpAccessChain,

    // Storage class
    #[regex("UniformConstant|Uniform|CrossWorkgroup|PushConstant|StorageBuffer")]
    Global,
    #[regex("Workgroup")]
    Shared,
    #[regex("Function|Private|Input|Output|AtomicCounter")]
    Local,

    #[regex("OpLabel")]
    OpLabel,
    #[regex("OpReturn")]
    OpReturn,
    #[regex("OpLoad")]
    OpLoad,
    #[regex("OpStore")]
    OpStore,
    #[regex("OpAtomicLoad")]
    OpAtomicLoad,
    #[regex("OpAtomicStore")]
    OpAtomicStore,
    #[regex("OpConstant")]
    OpConstant,
    #[regex("OpConstantComposite")]
    OpConstantComposite,
    #[regex("OpBitcast")]
    OpBitcast,
    #[regex("OpConstantTrue")]
    OpConstantTrue,
    #[regex("OpConstantFalse")]
    OpConstantFalse,
    #[regex("OpLogicalOr")]
    OpLogicalOr,
    #[regex("OpLogicalAnd")]
    OpLogicalAnd,
    #[regex("OpLogicalEqual")]
    OpLogicalEqual,
    #[regex("OpLogicalNotEqual")]
    OpLogicalNotEqual,
    #[regex("OpLogicalNot")]
    OpLogicalNot,
    #[regex("OpShiftLeftLogical")]
    OpShiftLeftLogical,
    #[regex("OpShiftRightLogical")]
    OpShiftRightLogical,
    #[regex("OpAtomicOr")]
    OpAtomicOr,
    #[regex("OpAtomicAnd")]
    OpAtomicAnd,
    #[regex("OpIAdd")]
    OpIAdd,
    #[regex("OpAtomicIAdd")]
    OpAtomicAdd,
    #[regex("OpISub")]
    OpISub,
    #[regex("OpAtomicISub")]
    OpAtomicSub,
    #[regex("OpIMul")]
    OpIMul,
    #[regex("OpUMod")]
    OpUMod,
    #[regex("OpIEqual")]
    OpIEqual,
    #[regex("OpINotEqual")]
    OpINotEqual,
    #[regex("OpSLessThan|OpULessThan")]
    OpSLessThan,
    #[regex("OpSGreaterThan|OpUGreaterThan")]
    OpSGreaterThan,
    #[regex("OpSLessThanEqual|OpULessThanEqual")]
    OpSLessThanEqual,
    #[regex("OpSGreaterThanEqual|OpUGreaterThanEqual")]
    OpSGreaterThanEqual,
    #[regex("Aligned")]
    Aligned,
    #[regex("OpBranch")]
    OpBranch,
    #[regex("OpBranchConditional")]
    OpBranchConditional,
    #[regex("OpSwitch")]
    OpSwitch,
    #[regex("OpControlBarrier")]
    OpControlBarrier,
    #[regex("OpLoopMerge")]
    OpLoopMerge,
    #[regex("OpSelectionMerge")]
    OpSelectionMerge,
    #[regex("OpAtomicExchange")]
    OpAtomicExchange,
    #[regex("OpAtomicCompareExchange")]
    OpAtomicCompareExchange,
    #[regex("OpGroupAll")]
    OpGroupAll,
    #[regex("OpGroupAny")]
    OpGroupAny,
    #[regex("OpGroupNonUniformAll")]
    OpGroupNonUniformAll,
    #[regex("OpGroupNonUniformAllEqual")]
    OpGroupNonUniformAllEqual,
    #[regex("OpGroupNonUniformAny")]
    OpGroupNonUniformAny,
    #[regex("OpGroupNonUniformBroadcast")]
    OpGroupNonUniformBroadcast,

    #[regex("OpBitwiseOr")]
    OpBitwiseOr,
    #[regex("OpBitwiseAnd")]
    OpBitwiseAnd,
    // #[regex("Op[A-Za-z]*", |lex|
    //     let inst = lex.slice();
    //     if instruction_not_supported(inst) {
    //         Filter::Emit(())
    //     } else{
    //         Filter::Skip
    //     }
    // )]
    // OpUnsupported,
    #[regex("%[_A-Za-z_][_A-Za-z0-9_]*|%[0-9]+")]
    Ident,
    #[regex("[0-9]+\\.[0-9]+")]
    Float,
    #[regex("-?[0-9]+")]
    Int,
    #[regex("true|false")]
    Bool,
    #[regex(r#""([^"\\]|\\.)*""#)]
    String,
    #[regex("[a-zA-Z]+")]
    Unknown,
    // #[regex("v3uint|uint|bool|void")]
    // Type,

    // Single-character tokens.
    #[regex("[ ]+")]
    Whitespace,
    #[regex("\n")]
    Newline,
    #[regex(r";[^\n]*\n", logos::skip)]
    VersionInfo,
    #[regex("\"")]
    DoubleQuote,
    #[regex(",")]
    Comma,
    #[regex(r"\.")]
    Dot,
    // Operation
    #[token("=")]
    Equal,
    #[token("!")]
    Bang,
    #[token("!=")]
    NotEqual,
    #[token(">")]
    Greater,
    #[token(">=")]
    GreaterThan,
    #[token("<")]
    Less,
    #[token("<=")]
    LessThan,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    // #[token("%")]
    // Percent,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Whitespace => "whitespace",
            Self::Newline => "newline",
            Self::Ident => "identifier",
            Self::Int => "int",
            Self::Float => "float",
            Self::String => "string",
            Self::Plus => "‘+’",
            Self::Minus => "‘-’",
            Self::Star => "‘*’",
            Self::Slash => "‘/’",
            Self::Equal => "‘=’",
            Self::Bang => "!",
            Self::Comma => "‘,‘",
            Self::Dot => "‘.‘",
            // Self::SemiColon => "‘;‘",
            // Self::Percent => "‘%‘",
            Self::DoubleQuote => "‘\"‘",
            Self::OpFunction => "OpFunction",
            Self::OpFunctionEnd => "OpFunctionEnd",
            Self::OpAccessChain => "OpAccessChain",
            Self::OpLabel => "OpLabel",
            Self::OpReturn => "OpReturn",
            Self::OpLoad => "OpLoad",
            Self::OpStore => "OpStore",
            Self::OpAtomicLoad => "OpAtomicLoad",
            Self::OpAtomicStore => "OpAtomicStore",
            Self::OpConstant => "OpConstant",
            Self::OpIEqual => "OpIEqual",
            Self::OpINotEqual => "OpINotEqual",
            Self::OpSLessThan => "OpSLessThan",
            Self::OpSGreaterThan => "OpSGreaterThan",
            Self::OpSLessThanEqual => "OpSLessThanEqual",
            Self::OpSGreaterThanEqual => "OpSGreaterThanEqual",
            Self::OpBranch => "OpBranch",
            Self::OpBranchConditional => "OpBranchConditional",
            Self::OpSwitch => "OpSwitch",
            Self::OpLoopMerge => "OpLoopMerge",
            Self::OpSelectionMerge => "OpSelectionMerge",
            Self::OpAtomicExchange => "OpAtomicExchange",
            Self::OpAtomicCompareExchange => "OpAtomicCompareExchange",
            Self::OpGroupAll => "OpGroupAll",
            Self::OpVariable => "OpVariable",
            Self::OpConstantComposite => "OpConstantComposite",
            Self::OpDecorate => "OpDecorate",
            Self::OpDecorateString => "OpDecorateString",
            Self::OpTypeBool => "OpTypeBool",
            Self::OpTypeInt => "OpTypeInt",
            Self::OpTypeVector => "OpTypeVector",
            Self::OpTypeArray => "OpTypeArray",
            Self::OpTypeRuntimeArray => "OpTypeRuntimeArray",
            Self::OpTypeStruct => "OpTypeStruct",
            Self::OpTypePointer => "OpTypePointer",
            Self::BuiltIn => "BuiltIn",
            Self::NumWorkgroups => "NumWorkgroups",
            Self::WorkgroupSize => "WorkgroupSize",
            Self::WorkgroupId => "WorkgroupId",
            Self::LocalInvocationId => "LocalInvocationId",
            Self::GlobalInvocationId => "GlobalInvocationId",
            Self::SubgroupSize => "SubgroupSize",
            Self::NumSubgroups => "NumSubgroups",
            Self::SubgroupId => "SubgroupId",
            Self::SubgroupLocalInvocationId => "SubgroupLocalInvocationId",
            Self::Global => "Global",
            Self::Shared => "Shared",
            Self::Local => "Local",
            Self::Root => "Root",
            Self::Statement => "Statement",
            Self::Error => "Error",
            _ => unreachable!(),
        })
    }
}

impl TokenKind {
    pub(crate) fn is_trivial(self) -> bool {
        match self {
            Self::Whitespace => true,
            _ => false,
        }
    }

    // todo: add more keywords
    // pub(crate) fn is_keyword(self) -> bool {
    //     match self {
    //         Self::Let | Self::Function => true,
    //         _ => false,
    //     }
    // }
}

#[cfg(test)]
mod test {
    use super::TokenKind;
    use logos::Logos;

    #[test]
    fn test_ident_pure_num() {
        let input = "%11 = OpConstant %_ptr_Function_uint 0
        ";
        let mut lexer = TokenKind::lexer(input);
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpConstant));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Int));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Newline));
    }

    #[test]
    fn test_token() {
        let input = "%uint_0 = OpConstant %uint 0
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpConstant));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Int));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Newline));
    }

    #[test]
    fn test_type_decl() {
        let input = "%uint = OpTypeInt 32 0
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpTypeInt));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Int));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Int));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Newline));
    }

    #[test]
    fn test_variable_decl_uniform() {
        let input = "%__2 = OpVariable %_ptr_Uniform_InputB Uniform
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpVariable));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Global));
    }

    #[test]
    fn test_variable_decl_input() {
        let input = "%__2 = OpVariable %_ptr_Uniform_InputB Input
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpVariable));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Local));
    }

    #[test]
    fn test_variable_decl_output() {
        let input = "%__2 = OpVariable %_ptr_Uniform_InputB Output
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpVariable));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Local));
    }

    #[test]
    fn test_variable_decl_shared() {
        let input = "%__2 = OpVariable %_ptr_Uniform_InputB Workgroup
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpVariable));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Shared));
    }

    #[test]
    fn test_variable_decl_local() {
        let input = "%__2 = OpVariable %_ptr_Uniform_InputB Function
        ";
        let mut lexer = TokenKind::lexer(input);
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Equal));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpVariable));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        // assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Percent));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Local));
    }

    #[test]
    fn test_logos_skip_version_info() {
        let input = "; SPIR-V
        ; Version: 1.0
        ; Generator: Khronos Glslang Reference Front End; 11
        OpDecorate %gl_SubgroupInvocationID BuiltIn SubgroupLocalInvocationId
        ";
        let mut lexer = TokenKind::lexer(input);
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::OpDecorate));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Ident));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::BuiltIn));
        assert_eq!(lexer.next().unwrap(), Ok(TokenKind::Whitespace));
        assert_eq!(
            lexer.next().unwrap(),
            Ok(TokenKind::SubgroupLocalInvocationId)
        );
    }
}
