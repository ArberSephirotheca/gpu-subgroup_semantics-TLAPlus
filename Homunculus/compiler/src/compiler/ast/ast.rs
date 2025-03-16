use rowan::TokenAtOffset;
use smallvec::smallvec;
use syntax_node_derive::{BinaryExpr, ResultType, UnaryExpr};

use crate::compiler::parse::lexer::Token;
use crate::compiler::parse::symbol_table::{SpirvType, StorageClass};
use crate::compiler::parse::syntax::{
    SyntaxElement, SyntaxNode, SyntaxToken, TokenKind, BUILT_IN_VARIABLE_SET, TLA_BUILTIN_SET,
};

pub trait ResultType {
    fn result_type(&self) -> Option<SyntaxToken>;
}

pub trait BinaryExpr {
    fn first_operand(&self) -> Option<SyntaxToken>;
    fn second_operand(&self) -> Option<SyntaxToken>;
}

pub trait UnaryExpr {
    fn operand(&self) -> Option<SyntaxToken>;
}

#[derive(Debug)]
pub struct Root(SyntaxNode);
#[derive(Debug)]
pub struct ExecutionMode(SyntaxNode);
#[derive(Debug)]
pub struct DecorateStatement(SyntaxNode);
#[derive(Debug)]
pub struct DecorateStringStatement(SyntaxNode);
#[derive(Debug)]
pub struct VariableRef(SyntaxNode);
#[derive(Debug)]
pub struct VariableDef(SyntaxNode);
#[derive(Debug)]
pub struct FuncStatement(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct VariableExpr(SyntaxNode);
#[derive(Debug)]
pub struct TypeExpr(SyntaxNode);
#[derive(Debug)]
pub struct LabelExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct LoadExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicLoadExpr(SyntaxNode);
#[derive(Debug)]
pub struct StoreStatement(SyntaxNode);
#[derive(Debug)]
pub struct AtomicStoreStatement(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct ConstExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct ConstCompositeExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct ConstTrueExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct ConstFalseExpr(SyntaxNode);

#[derive(Debug, ResultType, BinaryExpr)]
pub struct LogicalOr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct LogicalAnd(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct LogicalEqual(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct LogicalNotEqual(SyntaxNode);
#[derive(Debug, ResultType, UnaryExpr)]
pub struct LogicalNot(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct ShiftLeftLogicalExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct AddExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicAddExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicOrExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct SubExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicSubExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct MulExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct ModExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct EqualExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct NotEqualExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct LessThanExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct GreaterThanExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct LessThanEqualExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct GreaterThanEqualExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct BitwiseOrExpr(SyntaxNode);
#[derive(Debug, ResultType, BinaryExpr)]
pub struct BitwiseAndExpr(SyntaxNode);
#[derive(Debug, ResultType, UnaryExpr)]
pub struct BitcastExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicExchangeExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct AtomicCompareExchangeExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupAllExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupAnyExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupNonUniformAllExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupNonUniformAllEqualExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupNonUniformAnyExpr(SyntaxNode);
#[derive(Debug, ResultType)]
pub struct GroupNonUniformBroadcastExpr(SyntaxNode);
#[derive(Debug)]
pub struct ReturnStatement(SyntaxNode);
#[derive(Debug)]
pub struct BranchConditionalStatement(SyntaxNode);
#[derive(Debug)]
pub struct BranchStatement(SyntaxNode);
#[derive(Debug)]
pub struct SwitchStatement(SyntaxNode);
#[derive(Debug)]
pub struct ControlBarrierStatement(SyntaxNode);
#[derive(Debug)]
pub struct LoopMergeStatement(SyntaxNode);
#[derive(Debug)]
pub struct SelectionMergeStatement(SyntaxNode);

#[derive(Debug)]
pub enum Expr {
    VariableExpr(VariableExpr),
    TypeExpr(TypeExpr),
    VariableRef(VariableRef),
    LabelExpr(LabelExpr),
    LoadExpr(LoadExpr),
    AtomicLoadExpr(AtomicLoadExpr),
    ConstExpr(ConstExpr),
    ConstCompositeExpr(ConstCompositeExpr),
    ConstTrueExpr(ConstTrueExpr),
    ConstFalseExpr(ConstFalseExpr),
    LogicalOr(LogicalOr),
    LogicalAnd(LogicalAnd),
    LogicalEqual(LogicalEqual),
    LogicalNotEqual(LogicalNotEqual),
    LogicalNot(LogicalNot),
    ShiftLeftLogicalExpr(ShiftLeftLogicalExpr),
    AddExpr(AddExpr),
    AtomicAddExpr(AtomicAddExpr),
    SubExpr(SubExpr),
    AtomicSubExpr(AtomicAddExpr),
    AtomicOrExpr(AtomicOrExpr),
    MulExpr(MulExpr),
    ModExpr(ModExpr),
    EqualExpr(EqualExpr),
    NotEqualExpr(NotEqualExpr),
    LessThanExpr(LessThanExpr),
    GreaterThanExpr(GreaterThanExpr),
    LessThanEqualExpr(LessThanEqualExpr),
    GreaterThanEqualExpr(GreaterThanEqualExpr),
    BitwiseOrExpr(BitwiseOrExpr),
    BitwiseAndExpr(BitwiseAndExpr),
    BitcastExpr(BitcastExpr),
    AtomicExchangeExpr(AtomicExchangeExpr),
    AtomicCompareExchangeExpr(AtomicCompareExchangeExpr),
    GroupAllExpr(GroupAllExpr),
    GroupAnyExpr(GroupAnyExpr),
    GroupNonUniformAllExpr(GroupNonUniformAllExpr),
    GroupNonUniformAllEqualExpr(GroupNonUniformAllEqualExpr),
    GroupNonUniformAnyExpr(GroupNonUniformAnyExpr),
    GroupNonUniformBroadcastExpr(GroupNonUniformBroadcastExpr),
}

#[derive(Debug)]
pub enum Stmt {
    ExecutionMode(ExecutionMode),
    DecorateStatement(DecorateStatement),
    DecorateStringStatement(DecorateStringStatement),
    VariableDef(VariableDef),
    StoreStatement(StoreStatement),
    AtomicStoreStatement(AtomicStoreStatement),
    FuncStatement(FuncStatement),
    ReturnStatement(ReturnStatement),
    BranchConditionalStatement(BranchConditionalStatement),
    BranchStatement(BranchStatement),
    SwitchStatement(SwitchStatement),
    ControlBarrierStatement(ControlBarrierStatement),
    LoopMergeStatement(LoopMergeStatement),
    SelectionMergeStatement(SelectionMergeStatement),
    Expr(Expr),
}

impl Expr {
    pub(crate) fn cast(node: SyntaxNode) -> Option<Self> {
        match node.kind() {
            TokenKind::TypeFunctionExpr
            | TokenKind::TypeVoidExpr
            | TokenKind::TypeBoolExpr
            | TokenKind::TypeIntExpr
            | TokenKind::TypeVectorExpr
            | TokenKind::TypeArrayExpr
            | TokenKind::TypeRuntimeArrayExpr
            | TokenKind::TypeStructExpr
            | TokenKind::TypePointerExpr => Some(Self::TypeExpr(TypeExpr(node))),
            TokenKind::VariableExpr => Some(Self::VariableExpr(VariableExpr(node))),
            TokenKind::AccessChainExpr => Some(Self::VariableRef(VariableRef(node))),
            TokenKind::LabelExpr => Some(Self::LabelExpr(LabelExpr(node))),
            TokenKind::LoadExpr => Some(Self::LoadExpr(LoadExpr(node))),
            TokenKind::AtomicLoadExpr => Some(Self::AtomicLoadExpr(AtomicLoadExpr(node))),
            TokenKind::ConstantExpr => Some(Self::ConstExpr(ConstExpr(node))),
            TokenKind::ConstantCompositeExpr => {
                Some(Self::ConstCompositeExpr(ConstCompositeExpr(node)))
            }
            TokenKind::ConstantTrueExpr => Some(Self::ConstTrueExpr(ConstTrueExpr(node))),
            TokenKind::ConstantFalseExpr => Some(Self::ConstFalseExpr(ConstFalseExpr(node))),
            TokenKind::LogicalOrExpr => Some(Self::LogicalOr(LogicalOr(node))),
            TokenKind::LogicalAndExpr => Some(Self::LogicalAnd(LogicalAnd(node))),
            TokenKind::LogicalEqualExpr => Some(Self::LogicalEqual(LogicalEqual(node))),
            TokenKind::LogicalNotEqualExpr => Some(Self::LogicalNotEqual(LogicalNotEqual(node))),
            TokenKind::LogicalNotExpr => Some(Self::LogicalNot(LogicalNot(node))),
            TokenKind::ShiftLeftLogicalExpr => {
                Some(Self::ShiftLeftLogicalExpr(ShiftLeftLogicalExpr(node)))
            }
            TokenKind::AddExpr => Some(Self::AddExpr(AddExpr(node))),
            TokenKind::AtomicAddExpr => Some(Self::AtomicAddExpr(AtomicAddExpr(node))),
            TokenKind::SubExpr => Some(Self::SubExpr(SubExpr(node))),
            TokenKind::AtomicSubExpr => Some(Self::AtomicAddExpr(AtomicAddExpr(node))),
            TokenKind::AtomicOrExpr => Some(Self::AtomicOrExpr(AtomicOrExpr(node))),
            TokenKind::MulExpr => Some(Self::MulExpr(MulExpr(node))),
            TokenKind::ModExpr => Some(Self::ModExpr(ModExpr(node))),
            TokenKind::EqualExpr => Some(Self::EqualExpr(EqualExpr(node))),
            TokenKind::NotEqualExpr => Some(Self::NotEqualExpr(NotEqualExpr(node))),
            TokenKind::GreaterThanExpr => Some(Self::GreaterThanExpr(GreaterThanExpr(node))),
            TokenKind::GreaterThanEqualExpr => {
                Some(Self::GreaterThanEqualExpr(GreaterThanEqualExpr(node)))
            }

            TokenKind::LessThanExpr => Some(Self::LessThanExpr(LessThanExpr(node))),
            TokenKind::LessThanEqualExpr => Some(Self::LessThanEqualExpr(LessThanEqualExpr(node))),
            TokenKind::BitwiseOrExpr => Some(Self::BitwiseOrExpr(BitwiseOrExpr(node))),
            TokenKind::BitwiseAndExpr => Some(Self::BitwiseAndExpr(BitwiseAndExpr(node))),
            TokenKind::BitcastExpr => Some(Self::BitcastExpr(BitcastExpr(node))),
            TokenKind::AtomicExchangeExpr => {
                Some(Self::AtomicExchangeExpr(AtomicExchangeExpr(node)))
            }

            TokenKind::AtomicCompareExchangeExpr => Some(Self::AtomicCompareExchangeExpr(
                AtomicCompareExchangeExpr(node),
            )),
            TokenKind::GroupAllExpr => Some(Self::GroupAllExpr(GroupAllExpr(node))),
            TokenKind::GroupAnyExpr => Some(Self::GroupAnyExpr(GroupAnyExpr(node))),
            TokenKind::GroupNonUniformAllExpr => {
                Some(Self::GroupNonUniformAllExpr(GroupNonUniformAllExpr(node)))
            }
            TokenKind::GroupNonUniformAllEqualExpr => Some(Self::GroupNonUniformAllEqualExpr(
                GroupNonUniformAllEqualExpr(node),
            )),
            TokenKind::GroupNonUniformAnyExpr => {
                Some(Self::GroupNonUniformAnyExpr(GroupNonUniformAnyExpr(node)))
            }
            TokenKind::GroupNonUniformBroadcastExpr => Some(Self::GroupNonUniformBroadcastExpr(
                GroupNonUniformBroadcastExpr(node),
            )),
            _ => None,
        }
    }

    fn token(&self) -> SyntaxToken {
        match self {
            Self::VariableExpr(x) => x.0.first_token().unwrap(),
            Self::TypeExpr(x) => x.0.first_token().unwrap(),
            Self::VariableRef(x) => x.0.first_token().unwrap(),
            Self::LabelExpr(x) => x.0.first_token().unwrap(),
            Self::LoadExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicLoadExpr(x) => x.0.first_token().unwrap(),
            Self::ConstExpr(x) => x.0.first_token().unwrap(),
            Self::ConstCompositeExpr(x) => x.0.first_token().unwrap(),
            Self::ConstTrueExpr(x) => x.0.first_token().unwrap(),
            Self::ConstFalseExpr(x) => x.0.first_token().unwrap(),
            Self::LogicalOr(x) => x.0.first_token().unwrap(),
            Self::LogicalAnd(x) => x.0.first_token().unwrap(),
            Self::LogicalEqual(x) => x.0.first_token().unwrap(),
            Self::LogicalNotEqual(x) => x.0.first_token().unwrap(),
            Self::LogicalNot(x) => x.0.first_token().unwrap(),
            Self::ShiftLeftLogicalExpr(x) => x.0.first_token().unwrap(),
            Self::AddExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicAddExpr(x) => x.0.first_token().unwrap(),
            Self::SubExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicSubExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicOrExpr(x) => x.0.first_token().unwrap(),
            Self::MulExpr(x) => x.0.first_token().unwrap(),
            Self::ModExpr(x) => x.0.first_token().unwrap(),
            Self::EqualExpr(x) => x.0.first_token().unwrap(),
            Self::NotEqualExpr(x) => x.0.first_token().unwrap(),
            Self::GreaterThanExpr(x) => x.0.first_token().unwrap(),
            Self::GreaterThanEqualExpr(x) => x.0.first_token().unwrap(),
            Self::LessThanExpr(x) => x.0.first_token().unwrap(),
            Self::LessThanEqualExpr(x) => x.0.first_token().unwrap(),
            Self::BitwiseOrExpr(x) => x.0.first_token().unwrap(),
            Self::BitwiseAndExpr(x) => x.0.first_token().unwrap(),
            Self::BitcastExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicExchangeExpr(x) => x.0.first_token().unwrap(),
            Self::AtomicCompareExchangeExpr(x) => x.0.first_token().unwrap(),
            Self::GroupAllExpr(x) => x.0.first_token().unwrap(),
            Self::GroupAnyExpr(x) => x.0.first_token().unwrap(),
            Self::GroupNonUniformAllExpr(x) => x.0.first_token().unwrap(),
            Self::GroupNonUniformAllEqualExpr(x) => x.0.first_token().unwrap(),
            Self::GroupNonUniformAnyExpr(x) => x.0.first_token().unwrap(),
            Self::GroupNonUniformBroadcastExpr(x) => x.0.first_token().unwrap(),
        }
    }
}

impl Stmt {
    pub(crate) fn cast(node: SyntaxNode) -> Option<Self> {
        match node.kind() {
            TokenKind::IgnoredOp => None,
            TokenKind::ExecutionModeStatement => Some(Self::ExecutionMode(ExecutionMode(node))),
            TokenKind::DecorateStatement => Some(Self::DecorateStatement(DecorateStatement(node))),
            TokenKind::DecorateStringStatement => {
                Some(Self::DecorateStringStatement(DecorateStringStatement(node)))
            }
            TokenKind::VariableDef => Some(Self::VariableDef(VariableDef(node))),
            TokenKind::ReturnStatement => Some(Self::ReturnStatement(ReturnStatement(node))),
            TokenKind::StoreStatement => Some(Self::StoreStatement(StoreStatement(node))),
            TokenKind::AtomicStoreStatement => {
                Some(Self::AtomicStoreStatement(AtomicStoreStatement(node)))
            }
            TokenKind::BranchConditionalStatement => Some(Self::BranchConditionalStatement(
                BranchConditionalStatement(node),
            )),
            TokenKind::BranchStatement => Some(Self::BranchStatement(BranchStatement(node))),
            TokenKind::SwitchStatement => Some(Self::SwitchStatement(SwitchStatement(node))),
            TokenKind::ControlBarrierStatement => {
                Some(Self::ControlBarrierStatement(ControlBarrierStatement(node)))
            }
            TokenKind::LoopMergeStatement => {
                Some(Self::LoopMergeStatement(LoopMergeStatement(node)))
            }
            TokenKind::SelectionMergeStatement => {
                Some(Self::SelectionMergeStatement(SelectionMergeStatement(node)))
            }
            _ => Some(Self::Expr(Expr::cast(node)?)),
        }
    }

    pub(crate) fn token(&self) -> SyntaxToken {
        match self {
            Self::ExecutionMode(x) => x.0.first_token().unwrap(),
            Self::DecorateStatement(x) => x.0.first_token().unwrap(),
            Self::DecorateStringStatement(x) => x.0.first_token().unwrap(),
            Self::VariableDef(x) => x.0.first_token().unwrap(),
            Self::ReturnStatement(x) => x.0.first_token().unwrap(),
            Self::StoreStatement(x) => x.0.first_token().unwrap(),
            Self::AtomicStoreStatement(x) => x.0.first_token().unwrap(),
            Self::FuncStatement(x) => x.0.first_token().unwrap(),
            Self::BranchConditionalStatement(x) => x.0.first_token().unwrap(),
            Self::BranchStatement(x) => x.0.first_token().unwrap(),
            Self::SwitchStatement(x) => x.0.first_token().unwrap(),
            Self::ControlBarrierStatement(x) => x.0.first_token().unwrap(),
            Self::LoopMergeStatement(x) => x.0.first_token().unwrap(),
            Self::SelectionMergeStatement(x) => x.0.first_token().unwrap(),
            Self::Expr(x) => x.token(),
        }
    }
}

impl Root {
    pub(crate) fn stmts(&self) -> impl Iterator<Item = Stmt> {
        self.0.children().filter_map(Stmt::cast)
    }
    pub(crate) fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == TokenKind::Root {
            Some(Self(node))
        } else {
            None
        }
    }
}

impl TypeExpr {
    pub fn ty(&self) -> SpirvType {
        let tokens: Vec<SyntaxToken> = self
            .0
            .children_with_tokens()
            .filter_map(|child| {
                let token = child.into_token()?;
                // Filter out whitespace tokens and percent
                if token.kind() != TokenKind::Whitespace {
                    Some(token)
                } else {
                    None
                }
            })
            // fixme: make this more robust
            .take(10)
            .collect();

        match &tokens[0].kind() {
            TokenKind::OpTypeBool => SpirvType::Bool,
            TokenKind::OpTypeInt => {
                let width = &tokens[1];
                let signed = &tokens[2];
                match (&width.kind(), &signed.kind()) {
                    (TokenKind::Int, TokenKind::Int) => {
                        return SpirvType::Int {
                            width: width.text().parse().unwrap(),
                            signed: match signed.text().parse().unwrap() {
                                0 => false,
                                1 => true,
                                _ => panic!("Invalid signed value {:#?}", signed),
                            },
                        };
                    }
                    _ => panic!("Invalid width {:#?}, and signed value {:#?}", width, signed),
                }
            }
            TokenKind::OpTypeVoid => SpirvType::Void,
            // TokenKind::OpTypeFunction => SpirvType::Function {
            //     return_type: tokens[1].to_string(),
            // },
            TokenKind::OpTypeVector => {
                // fixme: error handling
                let inner_ty_symbol = &tokens[1];
                let count = &tokens[2];
                SpirvType::Vector {
                    element: inner_ty_symbol.text().to_string(),
                    count: count.text().parse().unwrap(),
                }
            }
            TokenKind::OpTypeArray => todo!(),
            TokenKind::OpTypeRuntimeArray => todo!(),
            TokenKind::OpTypeStruct => {
                let member = &tokens[1];
                SpirvType::Struct {
                    members: member.text().to_string(),
                }
            }
            TokenKind::OpTypePointer => {
                let storage_class = &tokens[1];
                let ty = &tokens[2];
                SpirvType::Pointer {
                    ty: ty.text().to_string(),
                    storage_class: match storage_class.kind() {
                        TokenKind::Global => StorageClass::Global,
                        TokenKind::Shared => StorageClass::Shared,
                        TokenKind::Local => StorageClass::Local,
                        _ => panic!("Invalid storage class {:#?}", storage_class),
                    },
                }
            }
            // TokenKind::AccessChainExpr => {
            //     let ty = &tokens[1];
            //     let base = &tokens[2];
            //     let index = &tokens[3];
            //     SpirvType::AccessChain {
            //         ty: ty.text().to_string(),
            //         base: base.text().to_string(),
            //         index: index.text().to_string(),
            //     }
            // }
            _ => panic!("Invalid type {}", self.0.first_token().unwrap().text()),
        }
    }
    pub fn name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::OpTypeBool || x.kind() == TokenKind::OpTypeInt)
    }
}

impl VariableExpr {
    pub(crate) fn ty_name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|child| child.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn storage_class(&self) -> Option<StorageClass> {
        let token = self
            .0
            .children_with_tokens()
            .filter_map(|child| child.into_token())
            .find(|x| {
                x.kind() == TokenKind::Global
                    || x.kind() == TokenKind::Shared
                    || x.kind() == TokenKind::Local
            });
        match token {
            Some(token) => match token.kind() {
                TokenKind::Global => Some(StorageClass::Global),
                TokenKind::Shared => Some(StorageClass::Shared),
                TokenKind::Local => Some(StorageClass::Local),
                _ => None,
            },
            None => None,
        }
    }
}
impl VariableRef {
    pub(crate) fn ty(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn base_var_name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn index_name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl VariableDef {
    // we want
    pub(crate) fn name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn value(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }
}

impl LoadExpr {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub(crate) fn ty(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|token| token.kind() == TokenKind::Ident)
            .nth(1)
    }
}

impl AtomicLoadExpr {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub(crate) fn ty(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|token| token.kind() == TokenKind::Ident)
            .nth(1)
    }
}

impl StoreStatement {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }
    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn object(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|token| token.kind() == TokenKind::Ident)
            .nth(1)
    }
}

impl AtomicStoreStatement {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|token| token.kind() == TokenKind::Ident)
            .nth(3)
    }
}

impl ConstExpr {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub(crate) fn ty(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Int)
    }
}

impl ConstCompositeExpr {
    pub(crate) fn constituents(&self) -> Vec<SyntaxToken> {
        let mut tokens_iter = self
            .0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .peekable();

        let mut result: Vec<SyntaxToken> = Vec::new();

        // skip result type
        tokens_iter.next();

        while let Some(constituent) = tokens_iter.next() {
            if constituent.kind() == TokenKind::Ident {
                result.push(constituent);
            } else {
                panic!("Invalid constituent {:#?}", constituent);
            }
        }

        result
    }
}

impl AddExpr {}

impl AtomicAddExpr {
    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn memory_semantics(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(4)
    }
}
impl SubExpr {}

impl AtomicSubExpr {
    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn memory_semantics(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(4)
    }
}

impl AtomicOrExpr {
    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn memory_semantics(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(4)
    }
}

impl MulExpr {
    pub(crate) fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }
}

impl EqualExpr {}

impl NotEqualExpr {
    pub(crate) fn ty(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }
}

impl LessThanExpr {}

impl GreaterThanExpr {}

impl LessThanEqualExpr {}

impl GreaterThanEqualExpr {}

impl AtomicExchangeExpr {
    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn memory_semantics(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(4)
    }
}

impl AtomicCompareExchangeExpr {
    pub(crate) fn result_type(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn pointer(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn memory_semantics_equal(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }

    pub(crate) fn memory_semantics_unequal(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(4)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(5)
    }

    pub(crate) fn comparator(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(
                |x: &rowan::SyntaxToken<crate::compiler::parse::syntax::AsukaLanguage>| {
                    x.kind() == TokenKind::Ident
                },
            )
            .nth(6)
    }
}
impl GroupAllExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn predicate(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl GroupAnyExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn predicate(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl GroupNonUniformAllExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn predicate(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl GroupNonUniformAllEqualExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl GroupNonUniformAnyExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn predicate(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl GroupNonUniformBroadcastExpr {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn value(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }

    pub(crate) fn id(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(3)
    }
}

impl ExecutionMode {
    pub(crate) fn local_size_x(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Int)
    }
    pub(crate) fn local_size_y(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Int)
            .nth(1)
    }
    pub(crate) fn local_size_z(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Int)
            .nth(2)
    }
}
impl DecorateStatement {
    pub(crate) fn name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn built_in_var(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| BUILT_IN_VARIABLE_SET.contains(&x.kind()))
    }
}

impl DecorateStringStatement {
    pub(crate) fn tla_builtin(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| TLA_BUILTIN_SET.contains(&x.kind()))
    }

    pub(crate) fn id(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn string(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::String)
    }
}

impl ReturnStatement {
    // todo: implement
}

impl BranchConditionalStatement {
    pub(crate) fn condition(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn true_label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn false_label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl BranchStatement {
    pub(crate) fn label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }
}

impl SwitchStatement {
    pub(crate) fn selector(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn default(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn target_sets(&self) -> Vec<(SyntaxToken, SyntaxToken)> {
        let mut tokens_iter = self
            .0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Int || x.kind() == TokenKind::Ident)
            .peekable();

        let mut result: Vec<(SyntaxToken, SyntaxToken)> = Vec::new();

        // skip selector and default
        tokens_iter.next();
        tokens_iter.next();

        while let Some(first) = tokens_iter.next() {
            if first.kind() == TokenKind::Int {
                if let Some(second) = tokens_iter.next() {
                    if second.kind() == TokenKind::Ident {
                        result.push((first, second));
                    }
                }
            }
        }

        result
    }
}

impl ControlBarrierStatement {
    pub(crate) fn execution_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn memory_scope(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }

    pub(crate) fn memory_semantics(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(2)
    }
}

impl LoopMergeStatement {
    pub(crate) fn merge_label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }

    pub(crate) fn continue_label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .filter(|x| x.kind() == TokenKind::Ident)
            .nth(1)
    }
}

impl SelectionMergeStatement {
    pub(crate) fn merge_label(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .find(|x| x.kind() == TokenKind::Ident)
    }
}

#[cfg(test)]
mod test {
    use super::Expr;
    use super::Root;
    use crate::compiler::parse::symbol_table::SpirvType;
    use crate::compiler::parse::symbol_table::StorageClass;
    use crate::compiler::{
        ast::ast::Stmt,
        parse::{parser::parse, syntax::TokenKind},
    };
    use expect_test::expect;
    fn check(input: &str, expected_tree: expect_test::Expect) {
        let parse = parse(input);
        expected_tree.assert_eq(&parse.debug_tree());
    }

    #[test]
    fn check_type() {
        let parse = parse(
            "OpTypeInt 32 0
        ",
        );
        let syntax = parse.syntax();
        let root = Root::cast(syntax).unwrap();
        let stmt = root.stmts().next().unwrap();
        let type_expr = match stmt {
            Stmt::Expr(Expr::TypeExpr(type_expr)) => type_expr,
            _ => panic!("Expected variable definition"),
        };
        assert_eq!(type_expr.name().unwrap().text(), "OpTypeInt");
        assert_eq!(
            type_expr.ty(),
            SpirvType::Int {
                width: 32,
                signed: false
            }
        );
    }

    #[test]
    fn check_variable_expr() {
        let input = "OpVariable %_ptr_Uniform_Output Uniform";
        let expected_name = "%_ptr_Uniform_Output";
        let parse = parse(input);
        let syntax = parse.syntax();
        let root = Root::cast(syntax).unwrap();
        let stmt = root.stmts().next().unwrap();
        let variable_expr = match stmt {
            Stmt::Expr(Expr::VariableExpr(variable_expr)) => variable_expr,
            _ => panic!("Expected variable definition"),
        };
        assert_eq!(variable_expr.ty_name().unwrap().text(), expected_name);
        assert_eq!(variable_expr.storage_class().unwrap(), StorageClass::Global);
    }

    #[test]
    fn check_skip_ignored_instructions() {
        let input = "OpCapability Shader
        OpMemoryModel Logical GLSL450
        OpEntryPoint Fragment %main \"main\" %frag_color
        %1 = OpExtInstImport \"GLSL.std.450\"
        OpExecutionMode %main LocalSize 256 1 1
        OpSource GLSL 450
        OpSourceExtension \"GL_ARB_separate_shader_objects\"
        OpName %main \"main\"
        OpName %frag_color \"frag_color\"
        OpDecorate %frag_color Location 0
        OpDecorate %subgroup_size BuiltIn SubgroupSize
        ";
        let parse = parse(input);
        let syntax = parse.syntax();
        let root = Root::cast(syntax).unwrap();
        let stmt = root.stmts().next().unwrap();
        let execution_mode_stmt = match stmt {
            Stmt::ExecutionMode(exec_mode) => exec_mode,
            _ => panic!("Expected execution mode statement, but got {:#?}", stmt),
        };
        assert_eq!(
            execution_mode_stmt
                .local_size_x()
                .unwrap()
                .text()
                .parse::<u32>(),
            Ok(256)
        );
        assert_eq!(
            execution_mode_stmt
                .local_size_y()
                .unwrap()
                .text()
                .parse::<u32>(),
            Ok(1)
        );
        assert_eq!(
            execution_mode_stmt
                .local_size_z()
                .unwrap()
                .text()
                .parse::<u32>(),
            Ok(1)
        );

        let opdecor_stmt = match root.stmts().nth(1).unwrap() {
            Stmt::DecorateStatement(decorate_stmt) => decorate_stmt,
            _ => panic!("Expected decorate statement"),
        };
        assert_eq!(opdecor_stmt.name().unwrap().text(), "%subgroup_size");
        assert_eq!(
            opdecor_stmt.built_in_var().unwrap().kind(),
            TokenKind::SubgroupSize
        );
    }

    #[test]
    fn check_skipped_token() {
        let input = "; SPIR-V
        ; Version: 1.0
        ; Generator: Khronos Glslang Reference Front End; 11
        OpDecorate %gl_SubgroupInvocationID BuiltIn SubgroupLocalInvocationId
        ";
        let parse = parse(input);
        let syntax = parse.syntax();
        let root = Root::cast(syntax).unwrap();
        let stmt = root.stmts().next().unwrap();
        let decorate_stmt = match stmt {
            Stmt::DecorateStatement(decorate_stmt) => decorate_stmt,
            _ => panic!("Expected decorate statement, but got {:#?}", stmt),
        };
        assert_eq!(
            decorate_stmt.name().unwrap().text(),
            "%gl_SubgroupInvocationID"
        );
        assert_eq!(
            decorate_stmt.built_in_var().unwrap().kind(),
            TokenKind::SubgroupLocalInvocationId
        );
    }
}
