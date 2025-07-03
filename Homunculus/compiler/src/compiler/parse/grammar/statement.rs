use crate::compiler::parse::{
    event::Event,
    lexer::Token,
    marker::CompletedMarker,
    parser::{Parse, Parser},
    symbol_table::*,
    syntax::{TokenKind, BUILT_IN_VARIABLE_SET, IGNORED_INSTRUCTION_SET},
};

pub(super) fn stmt(p: &mut Parser) -> Option<CompletedMarker> {
    if p.at(TokenKind::Ident) {
        variable_def(p)
    } else if p.at(TokenKind::OpExecutionMode) {
        op_execution_mode_stmt(p)
    } else if p.at(TokenKind::OpDecorate) {
        op_decorate_stmt(p)
    } else if p.at(TokenKind::OpDecorateString) {
        op_decorate_string_stmt(p)
    }
    // else if p.at(TokenKind::OpFunction) {
    //     Some(op_function_expr(p))
    // } else if p.at(TokenKind::OpFunctionEnd) {
    //     Some(op_function_end_statement(p))
    // }
    else if p.at(TokenKind::OpTypeInt) {
        Some(op_type_int_expr(p))
    } else if p.at(TokenKind::OpTypeBool) {
        Some(op_type_bool_expr(p))
    } else if p.at(TokenKind::OpTypeVoid) {
        Some(op_type_void_expr(p))
    }
    // else if p.at(TokenKind::OpTypeFunction) {
    //     Some(op_type_function_expr(p))
    // }
    else if p.at(TokenKind::OpTypeVector) {
        Some(op_type_vector_expr(p))
    } else if p.at(TokenKind::OpTypeArray) {
        Some(op_type_array_expr(p))
    } else if p.at(TokenKind::OpTypeRuntimeArray) {
        Some(op_type_runtime_array_expr(p))
    } else if p.at(TokenKind::OpTypeStruct) {
        Some(op_type_struct_expr(p))
    } else if p.at(TokenKind::OpTypePointer) {
        Some(op_type_pointer_expr(p))
    } else if p.at(TokenKind::OpVariable) {
        Some(op_variable_expr(p))
    } else if p.at(TokenKind::OpAccessChain) {
        Some(op_access_chain_expr(p))
    } else if p.at(TokenKind::OpLabel) {
        Some(op_label_expr(p))
    } else if p.at(TokenKind::OpConstant) {
        Some(op_constant_expr(p))
    }
    // else if p.at(TokenKind::OpConstantComposite) {
    //     Some(op_constant_composite_expr(p))
    // }
    else if p.at(TokenKind::OpConstantTrue) {
        Some(op_constant_true_expr(p))
    } else if p.at(TokenKind::OpConstantFalse) {
        Some(op_constant_false_expr(p))
    } else if p.at(TokenKind::OpLogicalOr) {
        Some(op_logical_or_expr(p))
    } else if p.at(TokenKind::OpLogicalAnd) {
        Some(op_logical_and_expr(p))
    } else if p.at(TokenKind::OpLogicalEqual) {
        Some(op_logical_equal_expr(p))
    } else if p.at(TokenKind::OpLogicalNotEqual) {
        Some(op_logical_not_equal_expr(p))
    } else if p.at(TokenKind::OpLogicalNot) {
        Some(op_logical_not_expr(p))
    } else if p.at(TokenKind::OpShiftLeftLogical) {
        Some(op_shift_left_logical(p))
    } else if p.at(TokenKind::OpShiftRightLogical) {
        Some(op_shift_right_logical(p))
    } else if p.at(TokenKind::OpReturn) {
        Some(op_return_statement(p))
    } else if p.at(TokenKind::OpLoad) {
        Some(op_load_expr(p))
    } else if p.at(TokenKind::OpStore) {
        Some(op_store_statement(p))
    } else if p.at(TokenKind::OpAtomicLoad) {
        Some(op_atomic_load_expr(p))
    } else if p.at(TokenKind::OpAtomicStore) {
        Some(op_atomic_store_statement(p))
    } else if p.at(TokenKind::OpIEqual) {
        Some(op_equal_expr(p))
    } else if p.at(TokenKind::OpINotEqual) {
        Some(op_not_equal_expr(p))
    } else if p.at(TokenKind::OpSGreaterThan) {
        Some(op_greater_than_expr(p))
    } else if p.at(TokenKind::OpSGreaterThanEqual) {
        Some(op_greater_than_equal_expr(p))
    } else if p.at(TokenKind::OpSLessThan) {
        Some(op_less_than_expr(p))
    } else if p.at(TokenKind::OpSLessThanEqual) {
        Some(op_less_than_equal_expr(p))
    } else if p.at(TokenKind::OpIAdd) {
        Some(op_add_expr(p))
    } else if p.at(TokenKind::OpAtomicAdd) {
        Some(op_atomic_add_expr(p))
    } else if p.at(TokenKind::OpISub) {
        Some(op_sub_expr(p))
    } else if p.at(TokenKind::OpAtomicSub) {
        Some(op_atomic_sub_expr(p))
    } else if p.at(TokenKind::OpAtomicOr) {
        Some(op_atomic_or_expr(p))
    } else if p.at(TokenKind::OpAtomicAnd) {
        Some(op_atomic_and_expr(p))
    } else if p.at(TokenKind::OpIMul) {
        Some(op_mul_expr(p))
    } else if p.at(TokenKind::OpUMod) {
        Some(op_mod_expr(p))
    } else if p.at(TokenKind::OpAtomicExchange) {
        Some(op_atomic_exchange_expr(p))
    } else if p.at(TokenKind::OpAtomicCompareExchange) {
        Some(op_atomic_compare_exchange_expr(p))
    } else if p.at(TokenKind::OpGroupAll) {
        Some(op_group_all_expr(p))
    } else if p.at(TokenKind::OpGroupAny) {
        Some(op_group_any_expr(p))
    } else if p.at(TokenKind::OpGroupNonUniformAll) {
        Some(op_group_nonuniform_all_expr(p))
    } else if p.at(TokenKind::OpGroupNonUniformAllEqual) {
        Some(op_group_nonuniform_all_equal_expr(p))
    } else if p.at(TokenKind::OpGroupNonUniformAny) {
        Some(op_group_nonuniform_any_expr(p))
    } else if p.at(TokenKind::OpGroupNonUniformBroadcast) {
        Some(op_group_nonuniform_broadcast_expr(p))
    } else if p.at(TokenKind::OpBranch) {
        Some(op_branch_statement(p))
    } else if p.at(TokenKind::OpBranchConditional) {
        Some(op_branch_conditional_statement(p))
    } else if p.at(TokenKind::OpSwitch) {
        Some(op_switch_statement(p))
    } else if p.at(TokenKind::OpControlBarrier) {
        Some(op_control_barrier_statement(p))
    } else if p.at(TokenKind::OpLoopMerge) {
        Some(op_loop_merge_statement(p))
    } else if p.at(TokenKind::OpSelectionMerge) {
        Some(op_selection_merge_statement(p))
    } else if p.at(TokenKind::OpBitwiseOr) {
        Some(op_bitwise_or_expr(p))
    } else if p.at(TokenKind::OpBitwiseAnd) {
        Some(op_bitwise_and_expr(p))
    } else if p.at(TokenKind::OpBitcast) {
        Some(op_bitcast_expr(p))
    } else if p.at_set(&IGNORED_INSTRUCTION_SET) {
        skip_ignored_op(p)
    } else {
        // todo: add more info
        panic!("unexpected token {:?}", p.peek());
    }
}

/// skip ignored instructions
fn skip_ignored_op(p: &mut Parser) -> Option<CompletedMarker> {
    let m = p.start();
    while !p.at(TokenKind::Newline) {
        p.bump();
    }
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::IgnoredOp, p.get_line());
    p.increment_line();
    None
}
/// example: OpExecutionMode %main LocalSize 256 1 1
fn op_execution_mode_stmt(p: &mut Parser) -> Option<CompletedMarker> {
    let m = p.start();
    // skip OpExecutionMode token
    p.bump();
    p.expect(TokenKind::Ident);

    // we only care LocalSize ExecutionMode
    if p.at(TokenKind::LocalSize) {
        p.bump();
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Newline);
        let line = p.get_line();
        p.increment_line();
        Some(m.complete(p, TokenKind::ExecutionModeStatement, line))
    } else {
        while !p.at(TokenKind::Newline) {
            p.bump();
        }
        p.expect(TokenKind::Newline);
        let line = p.get_line();
        p.increment_line();
        Some(m.complete(p, TokenKind::IgnoredOp, line))
    }
}
/// example: OpDecorate %gl_GlobalInvocationID BuiltIn GlobalInvocationId
fn op_decorate_stmt(p: &mut Parser) -> Option<CompletedMarker> {
    let m = p.start();
    // skip OpDecorate token
    p.bump();
    p.expect(TokenKind::Ident);

    // we only care BuiltIn decoration
    if p.at(TokenKind::BuiltIn) {
        p.bump();
    } else {
        while !p.at(TokenKind::Newline) {
            p.bump();
        }
        p.expect(TokenKind::Newline);
        m.complete(p, TokenKind::IgnoredOp, p.get_line());
        p.increment_line();
        return None;
    }

    if p.at_set(&BUILT_IN_VARIABLE_SET) {
        p.bump();
    } else {
        while !p.at(TokenKind::Newline) {
            p.bump();
        }
        p.expect(TokenKind::Newline);
        m.complete(p, TokenKind::IgnoredOp, p.get_line());
        p.increment_line();
        return None;
    }
    p.expect(TokenKind::Newline);
    let line = p.get_line();
    p.increment_line();
    Some(m.complete(p, TokenKind::DecorateStatement, line))
}

/// example: OpDecorateString %scheduler Usersemantic "HSA"
fn op_decorate_string_stmt(p: &mut Parser) -> Option<CompletedMarker> {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpDecorateString token
    p.bump();
    // if p.at(TokenKind::Scheduler)
    //     || p.at(TokenKind::TlaNumWorkgroups)
    //     || p.at(TokenKind::TlaSubgroupSize)
    // {
    //     ignored = false;
    // }
    // p.bump();
    // // else {
    // //     while !p.at(TokenKind::Newline) {
    // //         p.bump();
    // //     }
    // //     p.expect(TokenKind::Newline);
    // //     m.complete(p, TokenKind::IgnoredOp, line);
    // //     return None;
    // // }

    // p.bump();
    // // if p.at(TokenKind::UserSemantic) {
    // //     p.bump();
    // // } else {
    // //     while !p.at(TokenKind::Newline) {
    // //         p.bump();
    // //     }
    // //     p.expect(TokenKind::Newline);
    // //     m.complete(p, TokenKind::IgnoredOp, line);
    // //     return None;
    // // }
    while !p.at(TokenKind::Newline) {
        p.bump();
    }
    // p.expect(TokenKind::String);
    p.expect(TokenKind::Newline);
    Some(m.complete(p, TokenKind::DecorateStringStatement, line))
}
/// example: OpFunction %void None %1
// fn op_function_expr(p: &mut Parser) -> CompletedMarker {
//     let m = p.start();
//     // skip OpFunction token
//     p.bump();
//     p.expect(TokenKind::Ident);
//     if p.at(TokenKind::OpTypeBool)
//         || p.at(TokenKind::OpTypeInt)
//         || p.at(TokenKind::OpTypeBool)
//         || p.at(TokenKind::OpTypeVoid)
//     {
//         p.bump();
//     } else {
//         p.error();
//     }
//     p.expect(TokenKind::Ident);
//     p.expect(TokenKind::Newline);
//     m.complete(p, TokenKind::FunctionExpr)
// }

/// example: OpFunctionEnd
fn op_function_end_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpFunctionEnd token
    p.bump();
    m.complete(p, TokenKind::FunctionEndStatement, line)
}

/// example OpTypeInt 32 0
fn op_type_int_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeInt token
    p.bump();
    p.expect(TokenKind::Int);
    p.expect(TokenKind::Int);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeIntExpr, line)
}

/// example OpTypeBool
fn op_type_bool_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeBool token
    p.bump();
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeBoolExpr, line)
}

/// example OpTypeVoid
fn op_type_void_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeVoid token
    p.bump();
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeVoidExpr, line)
}

/// fixme: support arguments
/// example OpTypeFunction %void
fn op_type_function_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeFunction token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeFunctionExpr, line)
}

/// example OpTypeVector %uint 3
fn op_type_vector_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeVector token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Int);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeVectorExpr, line)
}

/// example OpTypeArray %arr_uint %uint 256
fn op_type_array_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeArray token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Int);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeArrayExpr, line)
}

/// example OpTypeRuntimeArray %arr_uint %uint
fn op_type_runtime_array_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeRuntimeArray token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeRuntimeArrayExpr, line)
}

/// example OpTypeStruct %sruntimearr_uint_0
/// fixme: currently we only support one member, implement multiple members
fn op_type_struct_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypeStruct token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypeStructExpr, line)
}

/// example OpTypePointer Function %_ptr_Function_uint
fn op_type_pointer_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpTypePointer token
    p.bump();
    // accept Uniform, Input, Output, Workgroup, Function
    if p.at(TokenKind::Global) || p.at(TokenKind::Shared) || p.at(TokenKind::Local) {
        p.bump();
    } else {
        p.error();
    }
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::TypePointerExpr, line)
}
/// example: OpVariable %_ptr_Function_uint Function
fn op_variable_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpVariable token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // it can be Uniform, Input, Output, Workgroup, Function
    if p.at(TokenKind::Global) || p.at(TokenKind::Shared) || p.at(TokenKind::Local) {
        p.bump();
    } else {
        p.error();
    }
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::VariableExpr, line)
}

/// example: OpAccessChain %_ptr_Uniform_uint %_ %int_0
fn op_access_chain_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAccessChain token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AccessChainExpr, line)
}
/// example: OpLabel
fn op_label_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLabel token
    p.bump();
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LabelExpr, line)
}

/// example: OpConstant %uint 0
fn op_constant_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpConstant token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Int);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ConstantExpr, line)
}

/// example: OpConstantComposite %v3uint %uint_256 %uint_1 %uint_1
fn op_constant_composite_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpConstantComposite token
    p.bump();
    p.expect(TokenKind::Ident);
    while !p.at(TokenKind::Newline) {
        p.expect(TokenKind::Ident);
    }
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ConstantCompositeExpr, line)
}

/// example: OpConstantTrue %bool
fn op_constant_true_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpConstantTrue token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ConstantTrueExpr, line)
}

/// example: OpConstantFalse %bool
fn op_constant_false_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpConstantFalse token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ConstantFalseExpr, line)
}

/// example: OpLogicalOr %bool %14 %15
fn op_logical_or_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLogicalOr token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LogicalOrExpr, line)
}

/// example: OpLogicalAnd %bool %14 %15
fn op_logical_and_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLogicalAnd token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LogicalAndExpr, line)
}

/// example: OpLogicalEqual %bool %14 %15
fn op_logical_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLogicalEqual token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LogicalEqualExpr, line)
}

/// example: OpLogicalNotEqual %bool %14 %15
fn op_logical_not_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLogicalNotEqual token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LogicalNotEqualExpr, line)
}

/// example: OpLogicalNot %bool %14
fn op_logical_not_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLogicalNot token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LogicalNotExpr, line)
}

/// example: OpShiftLeftLogical %uint %uint_1 %64
fn op_shift_left_logical(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpShiftLeftLogical token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ShiftLeftLogicalExpr, line)
}

/// example: OpShiftRightLogical %uint %uint_1 %64
fn op_shift_right_logical(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpShiftRightLogical token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ShiftRightLogicalExpr, line)
}
/// example: OpReturn
fn op_return_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpReturn token
    p.bump();
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ReturnStatement, line)
}

/// example: OpLoad %float %arrayidx Aligned 4
fn op_load_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLoad token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    if p.at(TokenKind::Aligned) {
        p.bump();
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Newline);
    } else {
        p.expect(TokenKind::Newline);
    }
    m.complete(p, TokenKind::LoadExpr, line)
}

/// example: OpStore %arrayidx2 %add Aligned 4
/// example: OpStore %9 %3
fn op_store_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpStore token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    if p.at(TokenKind::Aligned) {
        p.bump();
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Newline);
    } else {
        p.expect(TokenKind::Newline);
    }
    m.complete(p, TokenKind::StoreStatement, line)
}

/// example: OpAtomicLoad %uint %ptr %uint_0 %uint_1
fn op_atomic_load_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    p.bump();

    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicLoadExpr, line)
}

/// example: OpAtomicStore %4 %uint_0 %uint_1 %val
fn op_atomic_store_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    p.bump();

    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicStoreStatement, line)
}

/// example: OpIEqual %bool %1 %2
fn op_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpIEqual token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::EqualExpr, line)
}

/// example: OpINotEqual %bool %call %num_elements
fn op_not_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpINotEqual token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::NotEqualExpr, line)
}

/// example: OpSGreaterThan %bool %call %num_elements
fn op_greater_than_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSGreaterThan token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GreaterThanExpr, line)
}

/// example: OpSGreaterThanEqual %bool %call %num_elements
fn op_greater_than_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSGreaterThanEqual token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GreaterThanEqualExpr, line)
}

/// example: OpSLessThan %bool %call %num_elements
fn op_less_than_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSLessThan token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LessThanExpr, line)
}

/// example: OpSLessThanEqual %bool %call %num_elements
fn op_less_than_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSLessThanEqual token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LessThanEqualExpr, line)
}

/// example: OpIAdd %int %int_0 %int_1
fn op_add_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpIAdd token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AddExpr, line)
}

/// example: OpAtomicAdd %uint  %result_ptr %uint_0 %uint_0 %value
fn op_atomic_add_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicAdd token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicAddExpr, line)
}

/// example: OpAtomicSub %uint  %result_ptr %uint_0 %uint_0 %value
fn op_atomic_sub_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicSub token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicSubExpr, line)
}

/// example: OpAtomicOr %uint  %result_ptr %uint_0 %uint_0 %value
fn op_atomic_or_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicSub token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicOrExpr, line)
}

/// example: OpAtomicAnd %uint  %result_ptr %uint_0 %uint_0 %value
fn op_atomic_and_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicAnd token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::AtomicAndExpr, line)
}

/// example: OpISub %int %int_0 %int_1
fn op_sub_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpISub token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::SubExpr, line)
}

/// example: OpIMul %int %int_0 %int_1
fn op_mul_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpIMul token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::MulExpr, line)
}

/// example: OpUMod %uint %uint_0 %uint_1
fn op_mod_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpUMod token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ModExpr, line)
}

/// example: OpBranchConditional %cmp_not %if_end %if_then
fn op_branch_conditional_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpBranchConditional token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::BranchConditionalStatement, line)
}

/// example: OpBranch %if_end
fn op_branch_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpBranch token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::BranchStatement, line)
}

// example: OpSwitch %uint_0 %if_end 1 %if_then
fn op_switch_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSwitch token
    p.bump();
    // Selector
    p.expect(TokenKind::Ident);
    // Default
    p.expect(TokenKind::Ident);
    // literal, label
    while !p.at(TokenKind::Newline) {
        p.expect(TokenKind::Int);
        p.expect(TokenKind::Ident);
    }
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::SwitchStatement, line)
}

/// example: OpControlBarrier %uint_0 %uint_0 %uint_0
fn op_control_barrier_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpControlBarrier token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::ControlBarrierStatement, line)
}

/// example: OpLoopMerge %51 %52 None
fn op_loop_merge_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpLoopMerge token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::LoopMergeStatement, line)
}

/// example: OpSelectionMerge %29 None
fn op_selection_merge_statement(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpSelectionMerge token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::None);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::SelectionMergeStatement, line)
}

/// example: OpAtomicExchange %uint %result %result_ptr %uint_0 %value
fn op_atomic_exchange_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicExchange token
    p.bump();
    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);

    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);

    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);

    // p.expect(TokenKind::Ident);

    p.expect(TokenKind::Ident);

    // p.expect(TokenKind::Percent);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);

    m.complete(p, TokenKind::AtomicExchangeExpr, line)
}

/// example: OpAtomicCompareExchange %uint %27 %uint_1 %uint_0 %uint_0 %19 %18
fn op_atomic_compare_exchange_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpAtomicExchange token
    p.bump();

    // result type
    p.expect(TokenKind::Ident);
    // pointer
    p.expect(TokenKind::Ident);
    // memory scope
    p.expect(TokenKind::Ident);
    // memory senmatics equal
    p.expect(TokenKind::Ident);
    // memory semantics unequal
    p.expect(TokenKind::Ident);
    // value
    p.expect(TokenKind::Ident);
    // comparator
    p.expect(TokenKind::Ident);

    p.expect(TokenKind::Newline);

    m.complete(p, TokenKind::AtomicCompareExchangeExpr, line)
}

/// example: OpGroupAll %bool %uint_0 %value
fn op_group_all_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupAll token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupAllExpr, line)
}

/// example: OpGroupAny %bool %uint_0 %value
fn op_group_any_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupAny token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupAnyExpr, line)
}

/// example: OpGroupNonUniformAll %bool %uint_0 %value
fn op_group_nonuniform_all_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupNonUniformAll token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupNonUniformAllExpr, line)
}

/// example: OpGroupNonUniformAllEqual %bool %uint_0 %value
fn op_group_nonuniform_all_equal_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupNonUniformAllEqual token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupNonUniformAllEqualExpr, line)
}

/// example: OpGroupNonUniformAny %bool %uint_0 %value
fn op_group_nonuniform_any_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupNonUniformAny token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupNonUniformAnyExpr, line)
}

/// example: OpGroupNonUniformBroadcast %uint %uint_3 %90 %92
fn op_group_nonuniform_broadcast_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpGroupNonUniformBroadcast token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::GroupNonUniformBroadcastExpr, line)
}

/// example: OpBitwiseOr %result %uint_0 %uint_1
fn op_bitwise_or_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpBitwiseOr token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::BitwiseOrExpr, line)
}

/// example: OpBitwiseAnd %result %uint_0 %uint_1
fn op_bitwise_and_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpBitwiseAnd token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::BitwiseAndExpr, line)
}

/// example: OpBitcast %uint %uint_0
fn op_bitcast_expr(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // skip OpBitcast token
    p.bump();
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Ident);
    p.expect(TokenKind::Newline);
    m.complete(p, TokenKind::BitcastExpr, line)
}

fn variable_def(p: &mut Parser) -> Option<CompletedMarker> {
    let m = p.start();
    let line = p.get_line();
    p.increment_line();
    // p.expect(TokenKind::Percent);
    if p.at(TokenKind::Ident) {
        p.bump();
    } else {
        p.error();
    }

    p.expect(TokenKind::Equal);

    if stmt(p).is_none() {
        m.complete(p, TokenKind::IgnoredOp, line);
        None
    } else {
        Some(m.complete(p, TokenKind::VariableDef, line))
    }
}
