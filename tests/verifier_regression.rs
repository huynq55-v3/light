use light::ast::Program;
use light::codegen::MachineCodeEmitter;
use light::ivl::{IvlExpr, IvlLowerer};
use light::parser::Parser;
use light::vcgen::VcGen;
use light::verifier::{PropertyCategory, VerificationResult, Verifier};
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// TEST HARNESS (ANTI-VACUOUS-PASS & ELF64 EXECUTION HELPERS)
// ============================================================================

fn parse_and_verify(code: &str, func_name: Option<&str>) -> (Program, Vec<VerificationResult>) {
    let program =
        Parser::parse(code).unwrap_or_else(|e| panic!("Parse error: {:?}\nCode:\n{}", e, code));
    let func = match func_name {
        Some(name) => program
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("Function '{}' not found", name)),
        None => &program.functions[0],
    };
    let results = Verifier::verify_function(func, Some(&program));
    (program, results)
}

/// Kiểm tra chặt chẽ (chống Pass Ảo):
/// 1. Danh sách kết quả KHÔNG ĐƯỢC RỖNG (`!results.is_empty()`).
/// 2. 100% goals phải là `VerificationResult::Verified` (không được có Failed, Unknown, hay SolverNotFound).
/// 3. Nếu truyền `expected_goal_substr`, bắt buộc phải có ít nhất 1 goal khớp tên đó.
fn assert_verified(
    code: &str,
    func_name: Option<&str>,
    expected_goal_substr: Option<&str>,
) -> Vec<VerificationResult> {
    let (_, results) = parse_and_verify(code, func_name);
    assert!(
        !results.is_empty(),
        "Vacuous pass detected! Verifier returned 0 verification goals for function {:?}!\nCode:\n{}",
        func_name,
        code
    );
    for r in &results {
        assert!(
            matches!(r, VerificationResult::Verified { .. }),
            "Expected all goals to be Verified, but got failure/unknown: {:?}\nAll results: {:?}",
            r,
            results
        );
    }
    if let Some(sub) = expected_goal_substr {
        let has_goal = results.iter().any(
            |r| matches!(r, VerificationResult::Verified { goal_name, .. } if goal_name.contains(sub)),
        );
        assert!(
            has_goal,
            "Expected Verified goal containing '{}', but got: {:?}",
            sub, results
        );
    }
    results
}

/// Kiểm tra chặt chẽ rằng hàm PHẢI BỊ BẮT LỖI (`VerificationResult::Failed`)
/// đúng loại `expected_cat` và khớp chuỗi `expected_substr` (trong `goal_name` hoặc `reason`),
/// đồng thời KHÔNG phải do lỗi cú pháp/sort của Z3 Solver!
fn assert_failed(
    code: &str,
    func_name: Option<&str>,
    expected_cat: Option<PropertyCategory>,
    expected_substr: &str,
) -> Vec<VerificationResult> {
    let (_, results) = parse_and_verify(code, func_name);
    for r in &results {
        if let VerificationResult::Failed { reason, .. } = r {
            assert!(
                !reason.contains("Z3 solver error") && !reason.contains("Failed to spawn Z3"),
                "Unexpected internal Z3 solver/syntax error: {}",
                reason
            );
        }
    }
    let matched = results.iter().any(|r| match r {
        VerificationResult::Failed {
            category,
            goal_name,
            reason,
            ..
        } => {
            expected_cat.map_or(true, |c| *category == c)
                && (goal_name.contains(expected_substr) || reason.contains(expected_substr))
        }
        _ => false,
    });
    assert!(
        matched,
        "Expected VerificationResult::Failed (category: {:?}, matching '{}'), but got: {:?}",
        expected_cat, expected_substr, results
    );
    results
}

/// Kiểm tra trường hợp Verifier trả về `VerificationResult::Unknown`
fn assert_unknown(
    code: &str,
    func_name: Option<&str>,
    expected_substr: &str,
) -> Vec<VerificationResult> {
    let (_, results) = parse_and_verify(code, func_name);
    let matched = results.iter().any(|r| match r {
        VerificationResult::Unknown {
            goal_name, reason, ..
        } => goal_name.contains(expected_substr) || reason.contains(expected_substr),
        _ => false,
    });
    assert!(
        matched,
        "Expected VerificationResult::Unknown matching '{}', but got: {:?}",
        expected_substr, results
    );
    results
}

/// Kiểm chứng toàn bộ các hàm trong chương trình (đảm bảo tổng số goals > 0 và 100% Verified),
/// sau đó biên dịch AOT sang nhị phân Linux ELF64, thực thi và trả về exit code.
fn verify_and_run_elf(code: &str, verify_first: bool) -> i32 {
    static BIN_SEQ: AtomicUsize = AtomicUsize::new(0);
    let program = Parser::parse(code).expect("Parse program for ELF execution");
    if verify_first {
        let mut total_goals = 0usize;
        for func in &program.functions {
            let results = Verifier::verify_function(func, Some(&program));
            total_goals += results.len();
            for r in &results {
                assert!(
                    matches!(r, VerificationResult::Verified { .. }),
                    "Verification failed in function '{}': {:?}",
                    func.name,
                    r
                );
            }
        }
        assert!(
            total_goals > 0,
            "Vacuous verification before ELF execution: 0 goals generated across program!"
        );
    }

    let mut emitter = MachineCodeEmitter::new();
    emitter
        .compile_for_elf(&program)
        .expect("Compile AOT ELF64");
    let seq = BIN_SEQ.fetch_add(1, Ordering::Relaxed);
    let tmp_bin = format!("/tmp/light_test_bin_{}_{}", std::process::id(), seq);
    emitter.emit_elf64(&tmp_bin).expect("Emit ELF64 binary");
    let status = std::process::Command::new(&tmp_bin)
        .status()
        .expect("Execute compiled ELF64 binary");
    let _ = std::fs::remove_file(&tmp_bin);
    status.code().expect("Process terminated by signal")
}

// ============================================================================
// REGRESSION TESTS (V1 .. V112)
// ============================================================================

#[test]
fn test_v1_inductive_step_mutation_step2_fails() {
    let code = r#"
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000
  %i = CONST i64 0
  %acc = CONST i64 0
  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 2
    %acc = ADD i64 %acc %next_i
    %i = MOV %next_i
  END_LOOP sum_loop
  ENSURE %acc >= 0
  RET %acc
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Inductive),
        "Step 2: Inductive Step",
    );
}

#[test]
fn test_v2_accumulator_subtraction_invariant_fails() {
    let code = r#"
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000
  %i = CONST i64 0
  %acc = CONST i64 0
  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    INVARIANT %acc >= 0
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %acc = SUB i64 %acc 100
    %i = MOV %next_i
  END_LOOP sum_loop
  ENSURE %acc >= 0
  RET %acc
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Inductive),
        "Step 2: Inductive Step",
    );
}

#[test]
fn test_v3_omitted_counter_update_termination_fails() {
    let code = r#"
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000
  %i = CONST i64 0
  %acc = CONST i64 0
  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %acc = ADD i64 %acc %next_i
  END_LOOP sum_loop
  ENSURE %acc >= 0
  RET %acc
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Termination), "Step 4b");
}

#[test]
fn test_v4_inverted_ranking_function_fails() {
    let code = r#"
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000
  %i = CONST i64 0
  %acc = CONST i64 0
  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    DECREASES %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %acc = ADD i64 %acc %next_i
    %i = MOV %next_i
  END_LOOP sum_loop
  ENSURE %acc >= 0
  RET %acc
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Termination), "Step 4b");
}

#[test]
fn test_v5_callsite_precondition_violation_fails() {
    let code = r#"
FUNC callee(x: i64) -> i64
  REQUIRE x >= 0 && x <= 1000
  RET x
END_FUNC

FUNC caller() -> i64
  %arg = CONST i64 1005
  %res = CALL callee %arg
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        Some("caller"),
        Some(PropertyCategory::Safety),
        "Verify REQUIRE contract of 'callee'",
    );
}

#[test]
fn test_v6_unsupported_instruction_in_loop_yields_unknown() {
    let code = r#"
FUNC loop_with_unsupported(n: i64) -> i64
  REQUIRE n >= 0
  %i = CONST i64 0
  LOOP bad_loop
    INVARIANT %i >= 0
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %res = SYSCALL 60 %next_i 0 0
    %i = MOV %next_i
  END_LOOP bad_loop
  RET %i
END_FUNC
"#;
    assert_unknown(code, None, "Symbolic Loop Execution");
}

#[test]
fn test_v7_assert_false_fails() {
    let code = r#"
FUNC check_assert() -> i64
  %a = CONST i64 5
  ASSERT %a == 10
  RET %a
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v8_memory_bounds_load8_out_of_bounds_fails() {
    let code = r#"
FUNC check_oob() -> i64
  %buf = ALLOC slice<u8> 16
  %val = LOAD8 %buf 20
  RET %val
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit bounds check",
    );
}

#[test]
fn test_v9_div_zero_dynamic_context_fails() {
    let code = r#"
FUNC check_div() -> i64
  %a = CONST i64 5
  %b = CONST i64 5
  %denom = SUB i64 %a %b
  %res = DIV i64 100 %denom
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Division-by-Zero safety",
    );
}

#[test]
fn test_v10_negative_constants_work_without_syntax_error() {
    let code = r#"
FUNC check_negative(x: i64) -> i64
  REQUIRE x <= -50 && x >= -1000
  %sub = SUB i64 x 100
  ENSURE %sub < -40
  RET %sub
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v11_ssa_reassignment_vacuous_truth_prevention() {
    let code = r#"
FUNC check_vacuous() -> i64
  %x = CONST i64 1
  %x = ADD i64 %x 1
  ENSURE %x == 999
  RET %x
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ENSURE postcondition",
    );
}

#[test]
fn test_v12_in_loop_out_of_bounds_fails() {
    let code = r#"
FUNC test_loop_oob() -> i64
  ALLOC %buf 8
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 10
    DECREASES 10 - %i
    %done = GTE i64 %i 10
    BREAK_IF %done
    STORE8 %buf %i 42
    %next_i = ADD i64 %i 1
    %i = MOV %next_i
  END_LOOP l1
  RET 0
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit bounds check on '%buf'",
    );
}

#[test]
fn test_v13_forward_jump_label_branching() {
    let code = r#"
FUNC test_branch() -> i64
  %cond = CONST bool false
  BR_IF %cond .then_branch
  %res = CONST i64 100
  JUMP .end_branch
  LABEL .then_branch
  %res = CONST i64 200
  LABEL .end_branch
  ASSERT %res == 100
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v14_multibreak_loop_ite_merge() {
    let code = r#"
FUNC test_multibreak(mode: i64) -> i64
  REQUIRE mode >= 0 && mode <= 1
  %val = CONST i64 10
  LOOP mb_loop
    INVARIANT %val >= 10 && %val <= 20
    %c1 = EQ i64 mode 0
    BREAK_IF %c1
    %val = CONST i64 20
    %c2 = CONST bool true
    BREAK_IF %c2
  END_LOOP mb_loop
  ENSURE %val >= 10 && %val <= 20
  RET %val
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v15_loop_invariant_constant_preservation() {
    let code = r#"
FUNC test_const_preservation(n: i64) -> i64
  REQUIRE n >= 0 && n <= 100
  %limit = CONST i64 50
  %i = CONST i64 0
  LOOP cp_loop
    INVARIANT %i >= 0 && %i <= %limit
    DECREASES %limit - %i
    %done = GTE i64 %i %limit
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %i = MOV %next_i
  END_LOOP cp_loop
  ENSURE %i == %limit
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v16_early_return_violating_ensure_fails() {
    let code = r#"
FUNC abs_bad(x: i64) -> i64
  ENSURE %res > 0
  %is_neg = LT i64 x 0
  %res = MOV x
  RET_IF %is_neg %res
  %res = ADD i64 x 1
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "early return (RET_IF)",
    );
}

#[test]
fn test_v17_branching_join_phi_node_soundness() {
    let code = r#"
FUNC test_join(cond: bool) -> i64
  BR_IF cond .then_branch
  %x = CONST i64 10
  JUMP .join
  LABEL .then_branch
  %x = CONST i64 -999
  LABEL .join
  ASSERT %x > 0
  RET %x
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v18_loop_without_invariant_fails_exit_step() {
    let code = r#"
FUNC loop_no_inv() -> i64
  %i = CONST i64 0
  LOOP my_loop
    %done = GTE i64 %i 10
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %i = MOV %next_i
  END_LOOP my_loop
  ENSURE %i == 10
  RET %i
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Step 3: Exit Step",
    );
}

#[test]
fn test_v19_bool_sort_in_contracts() {
    let code = r#"
FUNC test_bool_contract(flag: bool) -> i64
  REQUIRE flag
  %res = CONST i64 1
  ASSERT flag
  ASSERT !false
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v20_parser_operator_precedence_and_unary_minus() {
    let vc = VcGen::new();
    let expr1 = Parser::parse_expr("%x - -5", 1).expect("parse expr1");
    assert_eq!(
        vc.expr_to_bv(&IvlExpr::from(&expr1)),
        "(bvsub x (bvneg (_ bv5 64)))"
    );

    let expr2 = Parser::parse_expr("10 - 5 + 2", 1).expect("parse expr2");
    assert_eq!(
        vc.expr_to_bv(&IvlExpr::from(&expr2)),
        "(bvadd (bvsub (_ bv10 64) (_ bv5 64)) (_ bv2 64))"
    );

    let expr3 = Parser::parse_expr("%x * %y", 1).expect("parse expr3");
    assert_eq!(vc.expr_to_bv(&IvlExpr::from(&expr3)), "(bvmul x y)");
}

#[test]
fn test_v21_post_loop_safety_out_of_bounds_fails() {
    let code = r#"
FUNC test_post_loop_oob() -> i64
  ALLOC %buf 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 15
    DECREASES 15 - %i
    %done = EQ i64 %i 15
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %i = MOV %next_i
  END_LOOP l1
  %x = LOAD8 %buf %i
  RET %x
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit bounds check on '%buf'",
    );
}

#[test]
fn test_v22_mid_ret_violating_ensure_fails() {
    let code = r#"
FUNC test_mid_ret(x: i64) -> i64
  %cond = LT i64 x 0
  BR_IF %cond .neg_branch
  %res = CONST i64 100
  RET %res
  LABEL .neg_branch
  %bad_res = CONST i64 -1
  RET %bad_res
  ENSURE %res >= 0
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ENSURE on branch return (RET)",
    );
}

#[test]
fn test_v23_branch_before_ret_does_not_pollute_later_labels() {
    let code = r#"
FUNC test_dead_path(c: bool) -> i64
  BR_IF c .branch_true
  %res = CONST i64 42
  RET %res
  LABEL .branch_true
  %res2 = CONST i64 99
  ASSERT %res2 == 99
  RET %res2
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v24_in_loop_branching_phi_node() {
    let code = r#"
FUNC test_loop_branching(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000
  %i = CONST i64 0
  %acc = CONST i64 0
  LOOP branch_loop
    INVARIANT %i >= 0 && %i <= n && %acc >= %i && %acc <= %i * 2
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %rem = MOD i64 %i 2
    %even = EQ i64 %rem 0
    BR_IF %even .is_even
    %acc = ADD i64 %acc 1
    JUMP .join
    LABEL .is_even
    %acc = ADD i64 %acc 2
    LABEL .join
    %i = ADD i64 %i 1
  END_LOOP branch_loop
  RET %acc
END_FUNC
"#;
    assert_verified(code, None, Some("Step 2: Inductive Step"));
}

#[test]
fn test_v25_call_with_constant_args_propagates_ensure() {
    let code = r#"
FUNC square(x: i64) -> i64
  REQUIRE x >= 0
  %sq = MUL i64 x x
  ENSURE %sq >= 0
  RET %sq
END_FUNC

FUNC caller() -> i64
  %val = CALL square 5
  ASSERT %val >= 0
  RET %val
END_FUNC
"#;
    assert_verified(code, Some("caller"), Some("Verify ASSERT directive"));
}

#[test]
fn test_v26_parenthesized_expressions_in_contracts() {
    let vc = VcGen::new();
    let expr1 = Parser::parse_expr("(%a + %b) * 2 == %res", 1).expect("parse expr1");
    assert_eq!(
        vc.expr_to_bool(&IvlExpr::from(&expr1)),
        "(= (bvmul (bvadd a b) (_ bv2 64)) res)"
    );

    let expr2 = Parser::parse_expr("(%x > 0 && %y > 0) || %z == 0", 1).expect("parse expr2");
    assert_eq!(
        vc.expr_to_bool(&IvlExpr::from(&expr2)),
        "(or (and (bvsgt x (_ bv0 64)) (bvsgt y (_ bv0 64))) (= z (_ bv0 64)))"
    );
}

#[test]
fn test_v27_post_loop_break_state_restored_accurately() {
    let code = r#"
FUNC test_post_loop_exact() -> i64
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 10
    DECREASES 10 - %i
    %done = EQ i64 %i 10
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    %i = MOV %next_i
  END_LOOP l1
  ASSERT %i == 10
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v28_loop_with_early_ret_if_verified_against_ensure() {
    let code = r#"
FUNC search_or_default(n: i64) -> i64
  %bad = LT i64 n 0
  %neg_one = CONST i64 -1
  RET_IF %bad %neg_one
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %res >= 0
  %res = CONST i64 1
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ENSURE on early return (RET_IF)",
    );
}

#[test]
fn test_v29_early_ret_value_aliased_to_canonical_ret_var() {
    let code = r#"
FUNC check_nonneg(x: i64) -> i64
  %is_neg = LT i64 x 0
  %zero = CONST i64 0
  RET_IF %is_neg %zero
  %ret = MOV x
  ENSURE %ret >= 0
  RET %ret
END_FUNC
"#;
    assert_verified(code, None, Some("early return (RET_IF)"));
}

#[test]
fn test_v30_pre_loop_binary_expression_preserved_in_contracts() {
    let code = r#"
FUNC test_pre_loop_binop(n: i64) -> i64
  REQUIRE n >= 0 && n <= 100
  %ten = CONST i64 10
  %limit = ADD i64 n %ten
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= %limit
    DECREASES %limit - %i
    %done = GTE i64 %i %limit
    BREAK_IF %done
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == %limit
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v31_unary_minus_expressions_parsed_as_subtraction() {
    let vc = VcGen::new();
    let expr1 = Parser::parse_expr("-%a", 1).expect("parse -%a");
    assert_eq!(
        vc.expr_to_bv(&IvlExpr::from(&expr1)),
        "(bvsub (_ bv0 64) a)"
    );

    let expr2 = Parser::parse_expr("-(%a + %b)", 1).expect("parse -(%a + %b)");
    assert_eq!(
        vc.expr_to_bv(&IvlExpr::from(&expr2)),
        "(bvsub (_ bv0 64) (bvadd a b))"
    );
}

#[test]
fn test_v32_both_branches_end_in_ret() {
    let code = r#"
FUNC max_val(a: i64, b: i64) -> i64
  %cmp = GT i64 a b
  BR_IF %cmp .is_a
  %res1 = MOV b
  ENSURE %res >= a && %res >= b
  RET %res1
  LABEL .is_a
  %res = MOV a
  RET %res
END_FUNC
"#;
    let results = assert_verified(code, None, Some("Verify ENSURE on branch return (RET)"));
    assert_eq!(results.len(), 2);
}

#[test]
fn test_v33_pre_loop_intermediate_binary_chain() {
    let code = r#"
FUNC loop_with_pre_chain(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10
  %one = CONST i64 1
  %two = CONST i64 2
  %tmp = ADD i64 n %one
  %limit = MUL i64 %tmp %two
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= %limit
    DECREASES %limit - %i
    %done = GTE i64 %i %limit
    BREAK_IF %done
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == %limit
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v34_loop_with_continue_if_verifies() {
    let code = r#"
FUNC loop_with_continue(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %skip = LT i64 %i 0
    CONTINUE_IF %skip
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == n
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("CONTINUE_IF"));
}

#[test]
fn test_v35_subst_expr_vars_len_preserves_length() {
    let mut map = HashMap::new();
    map.insert(
        "buf_len".to_string(),
        IvlExpr::Var("buf_length_val".to_string()),
    );
    map.insert("buf".to_string(), IvlExpr::Var("buf_ptr_v0".to_string()));

    let expr = IvlExpr::Len("buf".to_string());
    let substituted = IvlLowerer::subst_expr_map(&expr, &map);
    assert_eq!(substituted, IvlExpr::Var("buf_length_val".to_string()));

    let vc = VcGen::new();
    assert_eq!(vc.expr_to_bv(&substituted), "buf_length_val");
}

#[test]
fn test_v36_both_branches_different_ret_registers_straightline() {
    let code = r#"
FUNC max_simple(a: i64, b: i64) -> i64
  ENSURE %ret >= a && %ret >= b
  %gt = GT i64 a b
  BR_IF %gt .is_a
  %b_val = MOV b
  RET %b_val
  LABEL .is_a
  %ret = MOV a
  RET %ret
END_FUNC
"#;
    let results = assert_verified(code, None, Some("Verify ENSURE postcondition"));
    assert_eq!(results.len(), 2);
}

#[test]
fn test_v37_post_loop_slicelen_and_load8() {
    let code = r#"
FUNC post_loop_memory() -> i64
  %buf = ALLOC slice<u8> 10
  %zero = CONST i64 0
  %ten = CONST i64 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= %ten
    DECREASES %ten - %i
    %done = GTE i64 %i %ten
    BREAK_IF %done
    %i = ADD i64 %i 1
  END_LOOP l1
  %len = SLICE_LEN %buf
  %byte = LOAD8 %buf %zero
  ENSURE %len == 10 && %byte >= 0 && %byte <= 255
  RET %len
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v38_straightline_with_const_ret() {
    let code = r#"
FUNC returns_zero(x: i64) -> i64
  REQUIRE x >= 0
  ENSURE %ret == 0
  RET 0
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_ivl_verify_function_end_to_end() {
    let code = r#"
FUNC abs_val(x: i64) -> i64
  REQUIRE x >= 0
  %two = CONST i64 2
  %half = DIV i64 x %two
  ENSURE %ret >= 0
  RET %half
END_FUNC
"#;
    let results = assert_verified(code, None, Some("Verify ENSURE postcondition"));
    assert_eq!(results.len(), 2);
}

#[test]
fn test_ivl_on_real_loop_hoare_logic_steps() {
    let code = r#"
FUNC sum_to_n(n: i64) -> i64
    REQUIRE n >= 0 && n <= 1000
    ENSURE %ret >= 0
    %s = CONST i64 0
    %i = CONST i64 0
    LOOP l1
        INVARIANT %s >= 0 && %s <= %i * 1000
        INVARIANT %i >= 0 && %i <= n
        DECREASES n - %i
        %done = GTE i64 %i n
        BREAK_IF %done
        %s = ADD i64 %s %i
        %i = ADD i64 %i 1
    END_LOOP l1
    RET %s
END_FUNC
"#;
    let results = assert_verified(code, None, Some("Step 3: Exit Step"));
    assert_eq!(
        results.len(),
        7,
        "Cần có đủ 7 goals: 2 x Step 1, 2 x Step 2, Step 4a, Step 4b, Step 3"
    );
}

#[test]
fn test_v39_div_overflow_i64_min_neg1_fails() {
    let code = r#"
FUNC div_overflow(x: i64, y: i64) -> i64
  REQUIRE x == -9223372036854775808 && y == -1
  %ans = DIV i64 x y
  RET %ans
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Division-by-Zero safety",
    );
}

#[test]
fn test_v40_z3_output_unsat_in_variable_name_not_confused() {
    let code = r#"
FUNC check_unsat_name(x: i64) -> i64
  %is_unsat = CONST i64 1
  ASSERT %is_unsat == 0
  RET %is_unsat
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "ASSERT");
}

#[test]
fn test_v41_call_uninitialized_arg_fails_definite_assignment() {
    let code = r#"
FUNC helper(a: i64) -> i64
  RET a
END_FUNC

FUNC caller() -> i64
  %res = CALL helper %uninit
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        Some("caller"),
        Some(PropertyCategory::Safety),
        "SSA Definite Assignment",
    );
}

#[test]
fn test_v42_memory_in_loop_havoc_prevents_unsound_pass() {
    let code = r#"
FUNC loop_memory_mutation(n: i64) -> i64
  REQUIRE n > 0 && n <= 10
  ALLOC %buf 16
  STORE8 %buf 0 42
  %i = CONST i64 0
  LOOP l_mem
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    STORE8 %buf 0 99
    %i = ADD i64 %i 1
  END_LOOP l_mem
  %val = LOAD8 %buf 0
  ASSERT %val == 42
  RET %val
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "ASSERT");
}

#[test]
fn test_v43_diamond_branch_assume_isolation() {
    let code = r#"
FUNC min_val(a: i64) -> i64
  %cond = GT i64 a 0
  BR_IF %cond .then
  %x = CONST i64 -1
  JUMP .join
  LABEL .then
  %x = CONST i64 1
  LABEL .join
  ASSERT %x == 0
  RET %x
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "ASSERT");
}

#[test]
fn test_v44_load8_store8_no_vacuous_truth() {
    let code = r#"
FUNC test_load8_vacuous() -> i64
  ALLOC %buf 8
  STORE8 %buf 0 -1
  %val = LOAD8 %buf 0
  ASSERT %val == 0
  RET %val
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "ASSERT");
}

#[test]
fn test_v45_diamond_branch_memory_phi() {
    let code = r#"
FUNC test_branch_mem(cond: i64) -> i64
  ALLOC %buf 8
  %c = GT i64 cond 0
  BR_IF %c .then
  STORE8 %buf 0 10
  JUMP .join
  LABEL .then
  STORE8 %buf 0 20
  LABEL .join
  %val = LOAD8 %buf 0
  ASSERT %val == 20
  RET %val
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "ASSERT");
}

#[test]
fn test_v46_sequential_loops_both_verified() {
    let code = r#"
FUNC two_loops(n: i64) -> i64
  REQUIRE n >= 0 && n <= 100
  %i = CONST i64 0
  LOOP loop1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %d1 = GTE i64 %i n
    BREAK_IF %d1
    %i = ADD i64 %i 1
  END_LOOP loop1

  %j = CONST i64 0
  LOOP loop2
    INVARIANT %j >= 100
    DECREASES n - %j
    %d2 = GTE i64 %j n
    BREAK_IF %d2
    %j = ADD i64 %j 1
  END_LOOP loop2

  RET %j
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Inductive), "Step 1");
}

#[test]
fn test_v47_call_undefined_or_arg_mismatch_fails() {
    let code = r#"
FUNC good_func(x: i64) -> i64
  RET x
END_FUNC

FUNC test_bad_calls() -> i64
  %a = CONST i64 1
  %b = CONST i64 2
  %r1 = CALL good_func %a %b
  RET %r1
END_FUNC
"#;
    assert_failed(
        code,
        Some("test_bad_calls"),
        Some(PropertyCategory::Safety),
        "Call argument count mismatch",
    );
}

#[test]
fn test_v48_ensure_without_ret_fails() {
    let code = r#"
FUNC no_ret_func(x: i64) -> i64
  ENSURE %ret > 0
  %y = ADD i64 x 1
END_FUNC
"#;
    assert_failed(code, None, Some(PropertyCategory::Functional), "has no RET");
}

#[test]
fn test_v49_diamond_one_branch_memory_mutation_no_sort_error() {
    let code = r#"
FUNC one_branch_mem(cond: i64) -> i64
  ALLOC %buf 8
  %c = GT i64 cond 0
  BR_IF %c .then
  %zero = CONST i64 0
  JUMP .join
  LABEL .then
  STORE8 %buf 0 42
  LABEL .join
  RET cond
END_FUNC
"#;
    assert_verified(code, None, Some("Memory 8-bit bounds check on '%buf'"));
}

#[test]
fn test_v50_nested_loops_invariant_isolation() {
    let code = r#"
FUNC nested_loops_test(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10
  %i = CONST i64 0
  LOOP outer
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %d1 = GTE i64 %i n
    BREAK_IF %d1
    %j = CONST i64 0
    LOOP inner
      INVARIANT %j >= 0 && %j <= 5
      DECREASES 5 - %j
      %d2 = GTE i64 %j 5
      BREAK_IF %d2
      %j = ADD i64 %j 1
    END_LOOP inner
    %i = ADD i64 %i 1
  END_LOOP outer
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 2: Inductive Step"));
}

#[test]
fn test_v51_diamond_branch_with_call_and_store_str() {
    let code = r#"
FUNC helper_callee(v: i64) -> i64
  ENSURE %ret == v + 1
  %res = ADD i64 v 1
  RET %res
END_FUNC

FUNC branch_call(c: i64) -> i64
  ALLOC %buf 16
  %cond = GT i64 c 0
  BR_IF %cond .then
  %val = CONST i64 0
  STORE_STR %buf 0 "A"
  JUMP .join
  LABEL .then
  %val = CALL helper_callee c
  LABEL .join
  %byte = LOAD8 %buf 0
  RET %val
END_FUNC
"#;
    assert_verified(
        code,
        Some("branch_call"),
        Some("Memory 8-bit bounds check on '%buf'"),
    );
}

#[test]
fn test_v52_store_str_verified_by_load8() {
    let code = r#"
FUNC test_str() -> i64
  ALLOC %buf 8
  STORE_STR %buf 0 "Hello"
  %ch = LOAD8 %buf 0
  ASSERT %ch == 72
  RET %ch
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v53_slice_ptr_buffer_aliasing() {
    let code = r#"
FUNC test_alias() -> i64
  ALLOC %buf 16
  %ptr = SLICE_PTR %buf
  STORE8 %buf 0 42
  %val = LOAD8 %ptr 0
  ASSERT %val == 42
  RET %val
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v54_multibreak_loop_state_merge() {
    let code = r#"
FUNC multibreak_loop(mode: i64) -> i64
  REQUIRE mode >= 0 && mode <= 1
  %i = CONST i64 0
  %res = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 10
    DECREASES 10 - %i
    %b1 = EQ i64 mode 0
    %res = CONST i64 100
    BREAK_IF %b1
    %res = CONST i64 200
    %b2 = CONST bool true
    BREAK_IF %b2
  END_LOOP l1
  ENSURE (mode == 0 && %res == 100) || (mode != 0 && %res == 200)
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v55_loop_no_inv_with_oob_after_break_fails() {
    let code = r#"
FUNC loop_no_inv_with_bug(n: i64) -> i64
  ALLOC %buf 8
  %i = CONST i64 0
  LOOP my_loop
    %done = GTE i64 %i n
    BREAK_IF %done
    %bad = LOAD8 %buf 999
    %i = ADD i64 %i 1
  END_LOOP my_loop
  RET %i
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit bounds check on '%buf'",
    );
}

#[test]
fn test_v56_mov_buffer_alias_after_store_no_sort_conflict() {
    let code = r#"
FUNC test_mov_alias() -> i64
  ALLOC %buf 16
  STORE8 %buf 0 42
  %ptr = MOV %buf
  %val = LOAD8 %ptr 0
  ASSERT %val == 42
  RET %val
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v57_bitwise_operations_verification() {
    let code = r#"
FUNC test_bitwise(a: i64, b: i64) -> i64
  REQUIRE a == 60 && b == 13
  %and_res = AND i64 a b
  ASSERT %and_res == 12
  %or_res = OR i64 a b
  ASSERT %or_res == 61
  %xor_res = XOR a b
  ASSERT %xor_res == 49
  %two = CONST i64 2
  %shl_res = SHL a %two
  ASSERT %shl_res == 240
  %shr_res = SHR a %two
  ASSERT %shr_res == 15
  ENSURE %xor_res == 49
  RET %xor_res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v58_not_operator_bitwise_and_bool() {
    let code = r#"
FUNC test_not(flag: bool, x: i64) -> i64
  REQUIRE flag == true && x == 0
  %not_flag = NOT flag
  ASSERT %not_flag == false
  %not_x = NOT i64 x
  ASSERT %not_x == -1
  RET %not_x
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v59_contract_bitwise_operators() {
    let code = r#"
FUNC test_contract_ops(a: i64) -> i64
  REQUIRE (a ^ a) == 0 && (a << 1) == a * 2
  %res = CONST i64 0
  ENSURE %res == 0
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v60_bitwise_and_vs_logical_and_soundness() {
    let code = r#"
FUNC test_soundness() -> i64
  %two = CONST i64 2
  %one = CONST i64 1
  %bit = AND i64 %two %one
  ASSERT %bit == 0
  %t1 = CONST bool true
  %t2 = CONST bool true
  %log = AND %t1 %t2
  ASSERT %log == true
  %band_res = BAND %two %one
  ASSERT %band_res == 0
  %bor_res = BOR %two %one
  ASSERT %bor_res == 3
  RET %bit
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v61_shift_masked_at_64_bits_soundness() {
    let code = r#"
FUNC test_shift_64() -> i64
  %one = CONST i64 1
  %c_64 = CONST i64 64
  %res = SHL %one %c_64
  ASSERT %res == 1
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v62_alloc_in_aot_execution() {
    let code = r#"
FUNC main() -> i64
  ALLOC %buf 32
  %c_0 = CONST i64 0
  %c_77 = CONST i64 77
  STORE8 %buf %c_0 %c_77
  %val = LOAD8 %buf %c_0
  RET %val
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 77);
}

#[test]
fn test_v63_mmap_syscall_execution() {
    let code = r#"
FUNC main() -> i64
  %c_9 = CONST i64 9
  %c_0 = CONST i64 0
  %c_len = CONST i64 4096
  %c_prot = CONST i64 3
  %c_flags = CONST i64 34
  %c_neg1 = CONST i64 -1
  %ptr = SYSCALL %c_9 %c_0 %c_len %c_prot %c_flags %c_neg1 %c_0
  %c_88 = CONST i64 88
  STORE8 %ptr %c_0 %c_88
  %val = LOAD8 %ptr %c_0
  %c_11 = CONST i64 11
  %unmap = SYSCALL %c_11 %ptr %c_len %c_0 %c_0 %c_0 %c_0
  RET %val
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 88);
}

#[test]
fn test_v64_arena_allocator_verification_and_native_execution() {
    let code = r#"
FUNC align8(size: i64) -> i64
  REQUIRE size >= 0 && size <= 1073741824
  %tmp = ADD i64 size 7
  %mask = CONST i64 -8
  %aligned = BAND i64 %tmp %mask
  ENSURE %aligned >= size && %aligned <= size + 7
  RET %aligned
END_FUNC

FUNC arena_can_alloc(used: i64, capacity: i64, req_size: i64) -> bool
  REQUIRE used >= 0 && capacity >= used && req_size >= 0 && req_size <= 1073741824
  %rem = SUB i64 capacity used
  %ok = GTE i64 %rem req_size
  RET %ok
END_FUNC

FUNC arena_create(capacity: i64) -> i64
  REQUIRE capacity > 0 && capacity <= 1073741824
  %total = ADD i64 capacity 24
  %c_9 = CONST i64 9
  %c_0 = CONST i64 0
  %c_3 = CONST i64 3
  %c_34 = CONST i64 34
  %c_neg1 = CONST i64 -1
  %mmap_ptr = SYSCALL %c_9 %c_0 %total %c_3 %c_34 %c_neg1 %c_0
  %failed = LT i64 %mmap_ptr 0
  BR_IF %failed .create_fail
  %base_ptr = ADD i64 %mmap_ptr 24
  %off_0 = CONST i64 0
  %off_8 = CONST i64 8
  %off_16 = CONST i64 16
  STORE64 %mmap_ptr %off_0 %base_ptr
  STORE64 %mmap_ptr %off_8 capacity
  STORE64 %mmap_ptr %off_16 %c_0
  RET %mmap_ptr
LABEL .create_fail
  RET %c_0
END_FUNC

FUNC arena_alloc(arena: i64, req_size: i64) -> i64
  REQUIRE arena > 0 && req_size > 0 && req_size <= 1073741824
  %off_0 = CONST i64 0
  %off_8 = CONST i64 8
  %off_16 = CONST i64 16
  %base_ptr = LOAD64 arena %off_0
  %capacity = LOAD64 arena %off_8
  %used = LOAD64 arena %off_16
  %aligned = CALL align8 req_size
  %rem = SUB i64 %capacity %used
  %can_alloc = GTE i64 %rem %aligned
  BR_IF %can_alloc .do_alloc
  %zero = CONST i64 0
  RET %zero
LABEL .do_alloc
  %res_ptr = ADD i64 %base_ptr %used
  %new_used = ADD i64 %used %aligned
  STORE64 arena %off_16 %new_used
  RET %res_ptr
END_FUNC

FUNC arena_destroy(arena: i64) -> i64
  REQUIRE arena > 0
  %off_8 = CONST i64 8
  %capacity = LOAD64 arena %off_8
  %total = ADD i64 %capacity 24
  %c_11 = CONST i64 11
  %c_0 = CONST i64 0
  %res = SYSCALL %c_11 arena %total %c_0 %c_0 %c_0 %c_0
  RET %res
END_FUNC

FUNC main() -> i64
  %cap = CONST i64 65536
  %arena = CALL arena_create %cap
  %is_err = LTE i64 %arena 0
  BR_IF %is_err .exit_err
  %sz1 = CONST i64 10
  %chunk1 = CALL arena_alloc %arena %sz1
  %val42 = CONST i64 42
  %c_0 = CONST i64 0
  STORE8 %chunk1 %c_0 %val42
  %sz2 = CONST i64 20
  %chunk2 = CALL arena_alloc %arena %sz2
  %val55 = CONST i64 55
  STORE8 %chunk2 %c_0 %val55
  %r1 = LOAD8 %chunk1 %c_0
  %r2 = LOAD8 %chunk2 %c_0
  %sum = ADD i64 %r1 %r2
  %d = CALL arena_destroy %arena
  RET %sum
LABEL .exit_err
  %err = CONST i64 1
  RET %err
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 97);
}

#[test]
fn test_v65_simultaneous_substitution_prevents_variable_capture() {
    let code = r#"
FUNC foo(a: i64, b: i64) -> i64
  REQUIRE a < b
  %res = CONST i64 1
  ENSURE %res == 1
  RET %res
END_FUNC

FUNC caller() -> i64
  %b = CONST i64 10
  %a = CONST i64 20
  %r = CALL foo %b %a
  RET %r
END_FUNC
"#;
    assert_verified(
        code,
        Some("caller"),
        Some("Verify REQUIRE contract of 'foo'"),
    );
}

#[test]
fn test_v66_slice_param_out_of_bounds_detection() {
    let code = r#"
FUNC bad_read(s: slice<u8>) -> i64
  %ptr = SLICE_PTR s
  %idx = CONST i64 10
  %val = LOAD8 %ptr %idx
  RET %val
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit bounds check",
    );
}

#[test]
fn test_v67_buffer_name_collision_different_functions() {
    let code = r#"
FUNC func_a() -> i64
  %buf = ALLOC slice<u8> 16
  STORE_STR %buf "Hello\0"
  %len = SLICE_LEN %buf
  RET %len
END_FUNC

FUNC main() -> i64
  %buf = ALLOC slice<u8> 64
  STORE_STR %buf "A very long string that would overflow a 16 byte buffer easily!\0"
  %len_a = CALL func_a
  %len_main = SLICE_LEN %buf
  %sum = ADD i64 %len_a %len_main
  RET %sum
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 80);
}

#[test]
fn test_v68_continue_if_omitted_counter_update_termination_fails() {
    let code = r#"
FUNC loop_with_bad_continue(n: i64) -> i64
  REQUIRE n >= 5 && n <= 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %skip = EQ i64 %i 2
    CONTINUE_IF %skip
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == n
  RET %i
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Termination),
        "CONTINUE_IF",
    );
}

#[test]
fn test_v69_undefined_var_in_contract_fails_static_assignment() {
    let code_ensure_typo = r#"
FUNC typo_in_ensure(x: i64) -> i64
  REQUIRE x >= 0
  %res = ADD i64 x 1
  ENSURE %resutl >= 0
  RET %res
END_FUNC
"#;
    assert_failed(
        code_ensure_typo,
        None,
        Some(PropertyCategory::Safety),
        "resutl",
    );

    let code_assert_typo = r#"
FUNC typo_in_assert(x: i64) -> i64
  REQUIRE x >= 0
  %res = ADD i64 x 1
  ASSERT %undefined_var > 0
  RET %res
END_FUNC
"#;
    assert_failed(
        code_assert_typo,
        None,
        Some(PropertyCategory::Safety),
        "undefined_var",
    );
}

#[test]
fn test_v70_arbitrary_unstructured_jump_yields_unknown() {
    let code = r#"
FUNC test_free_jump() -> i64
  LABEL .loop_head
  %res = CONST i64 42
  JUMP .loop_head
  RET %res
END_FUNC
"#;
    assert_unknown(code, None, "Unsupported backward/external JUMP");
}

#[test]
fn test_v71_codegen_epilogue_not_skipped_when_instruction_ends_with_c3_byte() {
    let code = r#"
FUNC func_ending_in_c3() -> i64
  %c = CONST i64 -4395504899778281472
END_FUNC

FUNC main() -> i64
  %dummy = CALL func_ending_in_c3
  %ret = CONST i64 42
  RET %ret
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, false), 42);
}

#[test]
fn test_v72_slice_fat_pointer_call_abi_runtime() {
    let code = r#"
FUNC get_slice_len(s: slice<u8>) -> i64
  REQUIRE len(s) >= 0
  %l = SLICE_LEN s
  ENSURE %l == len(s)
  RET %l
END_FUNC

FUNC main() -> i64
  %buf = ALLOC slice<u8> 42
  STORE_STR %buf "Hello World"
  %res = CALL get_slice_len %buf
  RET %res
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 42);
}

#[test]
fn test_v73_parser_modulo_without_space_and_escaped_comment() {
    let code = r#"
FUNC parse_modulo_test(a: i64) -> i64
  REQUIRE a > 0 && a%2 == 0
  # Comment with escaped quote \" and then a comment char # inside string:
  %dummy = CONST i64 0
  %rem = MOD i64 a 2
  ENSURE %rem == 0
  RET %rem
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v74_call_havocs_memory_slice_argument() {
    let code = r#"
FUNC helper_write(b: slice<u8>) -> i64
  REQUIRE len(b) > 0
  STORE8 b 0 99
  RET 0
END_FUNC

FUNC main_unsound_check() -> i64
  %buf = ALLOC slice<u8> 16
  STORE8 %buf 0 42
  %dummy = CALL helper_write %buf
  %val = LOAD8 %buf 0
  ASSERT %val == 42
  RET %val
END_FUNC
"#;
    assert_failed(
        code,
        Some("main_unsound_check"),
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v75_break_cond_reassigned_after_break() {
    let code = r#"
FUNC test_reassigned_break(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %done = CONST bool true
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == n
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v76_continue_if_with_counter_reassignment() {
    let code = r#"
FUNC test_continue_reassign(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %done = GTE i64 %i n
    BREAK_IF %done
    %skip = LT i64 %i 0
    CONTINUE_IF %skip
    %skip = CONST bool true
    %i = ADD i64 %i 1
  END_LOOP l1
  ENSURE %i == n
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v77_nested_loops_decreases_isolation() {
    let code = r#"
FUNC test_nested_decreases(n: i64) -> i64
  REQUIRE n >= 0 && n <= 5
  %i = CONST i64 0
  LOOP outer
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %d1 = GTE i64 %i n
    BREAK_IF %d1
    %j = CONST i64 0
    LOOP inner
      INVARIANT %j >= 0 && %j <= 3
      DECREASES 3 - %j
      %d2 = GTE i64 %j 3
      BREAK_IF %d2
      %j = ADD i64 %j 1
    END_LOOP inner
    %i = ADD i64 %i 1
  END_LOOP outer
  ENSURE %i == n
  RET %i
END_FUNC
"#;
    assert_verified(code, None, Some("Step 3: Exit Step"));
}

#[test]
fn test_v78_slice_ptr_and_mov_length_propagation() {
    let code = r#"
FUNC test_slice_alias(s: slice<u8>) -> i64
  REQUIRE len(s) == 10
  %ptr = SLICE_PTR s
  %len1 = SLICE_LEN %ptr
  ASSERT %len1 == 10
  %mov_ptr = MOV %ptr
  %len2 = SLICE_LEN %mov_ptr
  ASSERT %len2 == 10
  ENSURE %ret == 10
  RET %len2
END_FUNC

FUNC main() -> i64
  %arr = ALLOC slice<u8> 10
  %ptr = SLICE_PTR %arr
  %res = CALL test_slice_alias %ptr
  RET %res
END_FUNC
"#;
    assert_verified(
        code,
        Some("test_slice_alias"),
        Some("Verify ENSURE postcondition"),
    );
    assert_eq!(verify_and_run_elf(code, true), 10);
}

#[test]
fn test_v79_multi_hop_buffer_size_propagation() {
    let code = r#"
FUNC test_multihop_buf() -> i64
  ALLOC %a 16
  %b = MOV %a
  %c = SLICE_PTR %b
  %d = MOV %c
  STORE8 %d 15 42
  %val = LOAD8 %d 15
  ASSERT %val == 42
  RET %val
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v80_slice_modified_in_loop_havocs_length() {
    let code = r#"
FUNC test_loop_rebind(s: slice<u8>, s2: slice<u8>) -> i64
  REQUIRE len(s) == 10 && len(s2) == 10
  %curr = MOV s
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 5
    INVARIANT len(%curr) == 10
    DECREASES 5 - %i
    %done = GTE i64 %i 5
    BREAK_IF %done
    %curr = MOV s2
    %i = ADD i64 %i 1
  END_LOOP l1
  %final_len = SLICE_LEN %curr
  ASSERT %final_len == 10
  RET %final_len
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v81_loop_structure_validation_mismatched_and_unclosed() {
    let code_mismatched = r#"
FUNC test_mismatch() -> i64
  %done = CONST bool true
  LOOP loop_a
    BREAK_IF %done
  END_LOOP loop_b
  RET 0
END_FUNC
"#;
    assert_failed(
        code_mismatched,
        None,
        Some(PropertyCategory::Safety),
        "Mismatched END_LOOP",
    );

    let code_unclosed = r#"
FUNC main() -> i64
  %done = CONST bool true
  LOOP loop_never_closed
    BREAK_IF %done
  RET 0
END_FUNC
"#;
    let (prog_unclosed, _) = parse_and_verify(code_unclosed, None);
    assert_failed(
        code_unclosed,
        None,
        Some(PropertyCategory::Safety),
        "Unclosed LOOP",
    );

    let mut emitter = MachineCodeEmitter::new();
    let codegen_err = emitter.compile_for_elf(&prog_unclosed);
    assert!(codegen_err.is_err());
    assert!(codegen_err.unwrap_err().contains("Unclosed LOOP"));

    let code_undefined_jump = r#"
FUNC test_undefined_jump() -> i64
  JUMP .non_existent_label
  RET 0
END_FUNC
"#;
    assert_failed(
        code_undefined_jump,
        None,
        Some(PropertyCategory::Safety),
        "Undefined label",
    );
}

#[test]
fn test_v82_break_continue_outside_loop() {
    let code_break = r#"
FUNC main() -> i64
  %t = CONST bool true
  BREAK_IF %t
  RET 0
END_FUNC
"#;
    let (prog_b, _) = parse_and_verify(code_break, None);
    assert_failed(
        code_break,
        None,
        Some(PropertyCategory::Safety),
        "BREAK_IF must be placed inside a LOOP",
    );
    let mut emitter_b = MachineCodeEmitter::new();
    assert!(
        emitter_b
            .compile_for_elf(&prog_b)
            .unwrap_err()
            .contains("BREAK_IF outside of LOOP")
    );

    let code_cont = r#"
FUNC main() -> i64
  %t = CONST bool true
  CONTINUE_IF %t
  RET 0
END_FUNC
"#;
    let (prog_c, _) = parse_and_verify(code_cont, None);
    assert_failed(
        code_cont,
        None,
        Some(PropertyCategory::Safety),
        "CONTINUE_IF must be placed inside a LOOP",
    );
    let mut emitter_c = MachineCodeEmitter::new();
    assert!(
        emitter_c
            .compile_for_elf(&prog_c)
            .unwrap_err()
            .contains("CONTINUE_IF outside of LOOP")
    );
}

#[test]
fn test_v83_slice_rebind_different_length_requires_invariant() {
    let code_unsound = r#"
FUNC test_unsound_rebind(s: slice<u8>, s2: slice<u8>) -> i64
  REQUIRE len(s) == 10 && len(s2) == 5
  %curr = MOV s
  %i = CONST i64 0
  LOOP l1
    INVARIANT %i >= 0 && %i <= 5
    DECREASES 5 - %i
    %done = GTE i64 %i 5
    BREAK_IF %done
    %curr = MOV s2
    %i = ADD i64 %i 1
  END_LOOP l1
  %final_len = SLICE_LEN %curr
  ASSERT %final_len == 10
  RET %final_len
END_FUNC
"#;
    assert_failed(
        code_unsound,
        None,
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v84_runtime_store_str_codegen_and_execution() {
    let code = r#"
FUNC main() -> i64
  %buf = ALLOC slice<u8> 16
  STORE8 %buf 0 88
  STORE8 %buf 1 88
  STORE_STR %buf 0 "OK"
  %c0 = LOAD8 %buf 0
  %c1 = LOAD8 %buf 1
  %eq0 = EQ i64 %c0 79
  %eq1 = EQ i64 %c1 75
  %and = AND %eq0 %eq1
  BR_IF %and .good
  RET 1
LABEL .good
  RET 0
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 0);
}

#[test]
fn test_v85_unsigned_arithmetic_div_and_comparisons() {
    let code = r#"
FUNC unsigned_math() -> i64
  %a = CONST u64 18446744073709551615
  %b = CONST u64 10
  %is_lt = LT u64 %a %b
  ASSERT %is_lt == false
  %res = DIV u64 %a %b
  ASSERT %res > 0
  RET 0
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ASSERT directive"));
}

#[test]
fn test_v86_load64_unaligned_fails_alignment_check() {
    let code = r#"
FUNC unaligned_load(p: i64) -> i64
  %off = CONST i64 1
  %val = LOAD64 p %off
  RET %val
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "8-byte alignment check",
    );
}

#[test]
fn test_v87_cfg_branch_unassigned_variable_fails() {
    let code = r#"
FUNC bad_branch(cond: bool) -> i64
  BR_IF cond .then
  JUMP .merge
LABEL .then
  %x = CONST i64 100
LABEL .merge
  %res = ADD i64 %x 1
  RET %res
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "SSA Definite Assignment",
    );
}

#[test]
fn test_v88_mixed_memory_sort_load8_and_load64_fails() {
    let code = r#"
FUNC mixed_sort() -> i64
  %buf = ALLOC slice<u8> 16
  STORE8 %buf 0 1
  %w = LOAD64 %buf 0
  RET %w
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory Sort Consistency",
    );
}

#[test]
fn test_v89_main_with_argc_argv_runtime() {
    let code = r#"
FUNC main(argc: i64, argv: i64) -> i64
  %ok = GTE i64 argc 1
  BR_IF %ok .success
  RET 1
LABEL .success
  RET 0
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, false), 0);
}

#[test]
fn test_v90_f64_rejection_type_check() {
    let code_parser = r#"
FUNC float_fn(x: f64) -> i64
  RET 0
END_FUNC
"#;
    let parse_res = Parser::parse(code_parser);
    assert!(parse_res.is_err());
    assert!(
        parse_res
            .unwrap_err()
            .message
            .contains("Floating-point type 'f64' is not yet supported")
    );
}

#[test]
fn test_v91_store_str_exact_length_no_overflow() {
    let code = r#"
FUNC main() -> i64
  %buf = ALLOC slice<u8> 5
  STORE_STR %buf 0 "Hello"
  %c0 = LOAD8 %buf 0
  %c4 = LOAD8 %buf 4
  %eq0 = EQ i64 %c0 72
  %eq4 = EQ i64 %c4 111
  %and = AND %eq0 %eq4
  BR_IF %and .ok
  RET 1
LABEL .ok
  RET 0
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 0);

    let code_overflow = r#"
FUNC overflow() -> i64
  %buf = ALLOC slice<u8> 5
  STORE_STR %buf 0 "Hello!"
  RET 0
END_FUNC
"#;
    assert_failed(
        code_overflow,
        None,
        Some(PropertyCategory::Safety),
        "String write within buffer",
    );
}

#[test]
fn test_v92_u64_contract_unsigned_comparison() {
    let code = r#"
FUNC test_u64(a: u64, b: u64) -> u64
  REQUIRE a < b
  %res = SUB u64 b a
  ENSURE %res > 0
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v93_syscall_havocs_memory_buffer() {
    let code = r#"
FUNC test_sys_havoc() -> i64
  %buf = ALLOC slice<u8> 16
  STORE8 %buf 0 65
  %c_0 = CONST i64 0
  %c_16 = CONST i64 16
  %read_ret = SYSCALL %c_0 %c_0 %buf %c_16
  %c0 = LOAD8 %buf 0
  ASSERT %c0 == 65
  RET 0
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v94_float_contract_correct_line_number() {
    let code = "FUNC foo(x: i64) -> i64\n  REQUIRE x > 3.14159\n  RET x\nEND_FUNC\n";
    let err = Parser::parse(code).expect_err("Parser must reject float in REQUIRE");
    assert_eq!(err.line_no, 2);
    assert!(
        err.message
            .contains("Floating-point numbers are not supported in Light contracts")
    );
}

#[test]
fn test_v95_cross_loop_jump_validation() {
    let code = r#"
FUNC bad_jump() -> i64
  %c = CONST bool true
  BR_IF %c .inside_loop
  LOOP l1
    INVARIANT true
    DECREASES 0
    BREAK_IF %c
    LABEL .inside_loop
    %x = CONST i64 42
  END_LOOP l1
  RET 0
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "crosses loop boundaries",
    );
}

#[test]
fn test_v96_negative_constants_in_contracts_not_treated_as_unsigned() {
    let code = r#"
FUNC sys_wrapper(fd: i64) -> i64
  REQUIRE fd >= 0
  %rax = CONST i64 3
  %z = CONST i64 0
  %res = SYSCALL %rax fd %z %z
  ENSURE %res >= -4096
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v97_canonical_ret_var_ignores_input_parameters_in_ret_if() {
    let code = r#"
FUNC clamp_test(val: i64, low: i64, high: i64) -> i64
  REQUIRE low <= high
  ENSURE %ret >= low && %ret <= high
  %is_low = LT i64 val low
  RET_IF %is_low low
  %is_high = GT i64 val high
  BR_IF %is_high .lbl_high
  %res = MOV val
  JUMP .lbl_merge
LABEL .lbl_high
  %res = MOV high
LABEL .lbl_merge
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v98_entire_standard_library_verifies_cleanly() {
    for std_file in [
        "std/alloc.lit",
        "std/fs.lit",
        "std/io.lit",
        "std/string.lit",
    ] {
        let prog =
            Parser::parse_file(std_file).unwrap_or_else(|e| panic!("Parse {}: {}", std_file, e));
        let mut file_goals = 0usize;
        for func in &prog.functions {
            let results = Verifier::verify_function(func, Some(&prog));
            file_goals += results.len();
            for r in &results {
                assert!(
                    matches!(r, VerificationResult::Verified { .. }),
                    "Stdlib verification failed in {}::{}: {:?}",
                    std_file,
                    func.name,
                    r
                );
            }
        }
        assert!(
            file_goals > 0,
            "Stdlib file {} emitted 0 verification goals!",
            std_file
        );
    }
}

#[test]
fn test_v99_loop_call_havocs_memory_soundness() {
    let code = r#"
FUNC clobber(buf: slice<u8>) -> i64
  REQUIRE len(buf) >= 4
  ENSURE %r == 0
  STORE8 buf 0 99
  %r = MOV 0
  RET %r
END_FUNC

FUNC caller_loop_unsound() -> i64
  ENSURE %v == 42
  %buf = ALLOC slice<u8> 8
  STORE8 %buf 0 42
  %i = MOV 0
  LOOP
    INVARIANT %i >= 0 && %i <= 3
    DECREASES 3 - %i
    %done = EQ i64 %i 3
    BREAK_IF %done
    %dummy = CALL clobber %buf
    %i = ADD i64 %i 1
  END_LOOP
  %v = LOAD8 u8 %buf 0
  RET %v
END_FUNC
"#;
    assert_failed(
        code,
        Some("caller_loop_unsound"),
        Some(PropertyCategory::Functional),
        "Step 3: Exit Step",
    );
}

#[test]
fn test_v100_slice_load64_underflow_bounds_check() {
    let code = r#"
FUNC bad_slice_load64(s: slice<u8>) -> i64
  ENSURE %v == %v
  %v = LOAD64 s 0
  RET %v
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 64-bit bounds check",
    );
}

#[test]
fn test_v101_mixed_store_str_and_load64_fails_sort_check() {
    let code = r#"
FUNC mixed_str_and_64() -> i64
  ENSURE %v == %v
  %buf = ALLOC slice<u8> 16
  STORE_STR %buf "hello"
  %v = LOAD64 %buf 0
  RET %v
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory Sort Consistency",
    );
}

#[test]
fn test_v102_ret_overwriting_param_name_isolation() {
    let code = r#"
FUNC multi_branch_ret(x: i64) -> i64
  REQUIRE x >= 10 && x <= 1000
  ENSURE %res >= 10 && x >= 10
  %c = EQ i64 x 10
  RET_IF %c 10
  %res = ADD i64 x 1
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v103_stdlib_parse_i64_ensures_non_negative() {
    let code = r#"
FUNC caller_uses_parse_i64(s: slice<u8>) -> i64
  REQUIRE len(s) > 0 && len(s) <= 18
  ENSURE %val >= 0
  %val = CALL str_parse_i64 s
  RET %val
END_FUNC
"#;
    let mut prog = Parser::parse_file("std/string.lit").expect("Parse std/string.lit");
    let caller_prog = Parser::parse(code).expect("Parse V103 caller");
    let caller_fn = caller_prog.functions[0].clone();
    prog.functions.push(caller_fn.clone());
    let res = Verifier::verify_function(&caller_fn, Some(&prog));
    assert!(!res.is_empty());
    assert!(
        res.iter()
            .all(|r| matches!(r, VerificationResult::Verified { .. }))
    );
}

#[test]
fn test_v104_signed_right_shift_in_contracts_uses_arithmetic_shift() {
    let code = r#"
FUNC test_signed_sar(x: i64) -> i64
  REQUIRE x == -8
  ENSURE %res == (x >> 1) && %res == -4
  %res = SAR i64 x 1
  RET %res
END_FUNC
"#;
    assert_verified(code, None, Some("Verify ENSURE postcondition"));
}

#[test]
fn test_v105_alloc_slice_i64_multiplies_by_element_byte_size() {
    let code = r#"
FUNC main() -> i64
  %arr = ALLOC slice<i64> 4
  STORE64 %arr 24 77
  %val = LOAD64 %arr 24
  ASSERT %val == 77
  ENSURE %val == 77
  RET %val
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 77);
}

#[test]
fn test_v106_u64_large_immediate_and_implicit_type_comparison() {
    let code = r#"
FUNC main() -> i64
  %a = CONST u64 10
  %sum = ADD u64 %a 18446744073709551600
  %is_lt = LT %a %sum
  ASSERT %is_lt == true
  BR_IF %is_lt .ok
  RET 1
LABEL .ok
  RET 0
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 0);
}

#[test]
fn test_v107_load8_raw_pointer_negative_offset_rejected() {
    let code = r#"
FUNC bad_ptr_load8(p: ptr) -> i64
  %v = LOAD8 p -5
  RET %v
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Memory 8-bit pointer offset non-negative check",
    );
}

#[test]
fn test_v108_duplicate_label_in_function_rejected_by_verifier() {
    let code = r#"
FUNC dup_lbl(x: i64) -> i64
  LABEL .same
  %a = ADD i64 x 1
  LABEL .same
  RET %a
END_FUNC
"#;
    assert_failed(
        code,
        None,
        Some(PropertyCategory::Safety),
        "Duplicate Label/Loop",
    );
}

#[test]
fn test_v109_nested_loop_no_duplicate_verification_goals() {
    let code = r#"
FUNC nested_count(n: i64) -> i64
  REQUIRE n >= 0 && n <= 5
  %i = CONST i64 0
  LOOP outer
    INVARIANT %i >= 0 && %i <= n
    DECREASES n - %i
    %d1 = GTE i64 %i n
    BREAK_IF %d1
    %j = CONST i64 0
    LOOP inner
      INVARIANT %j >= 0 && %j <= 3
      DECREASES 3 - %j
      %d2 = GTE i64 %j 3
      BREAK_IF %d2
      %j = ADD i64 %j 1
    END_LOOP inner
    %i = ADD i64 %i 1
  END_LOOP outer
  RET %i
END_FUNC
"#;
    let results = assert_verified(code, None, Some("Step 2: Inductive Step"));
    assert_eq!(results.len(), 8);
}

#[test]
fn test_v110_call_dest_same_as_arg_prevents_vacuous_truth() {
    // Khi biến nhận kết quả `%x` của `CALL` trùng tên với đối số truyền vào (`%x = CALL inc %x`),
    // `IvlLowerer` phải chụp giá trị Pre-state của `%x` trước khi `Havoc(%x)`,
    // tránh biến `ENSURE %ret == a + 1` thành `%x == %x + 1` (UNSAT -> Vacuous Truth!).
    let code_good = r#"
FUNC inc(a: i64) -> i64
  REQUIRE a >= 0 && a <= 100
  %r = ADD i64 a 1
  ENSURE %r == a + 1
  RET %r
END_FUNC

FUNC caller_good() -> i64
  %x = CONST i64 10
  %x = CALL inc %x
  ASSERT %x == 11
  RET %x
END_FUNC
"#;
    assert_verified(
        code_good,
        Some("caller_good"),
        Some("Verify ASSERT directive"),
    );

    let code_bad = r#"
FUNC inc(a: i64) -> i64
  REQUIRE a >= 0 && a <= 100
  %r = ADD i64 a 1
  ENSURE %r == a + 1
  RET %r
END_FUNC

FUNC caller_bad() -> i64
  %x = CONST i64 10
  %x = CALL inc %x
  ASSERT %x == 999
  RET %x
END_FUNC
"#;
    assert_failed(
        code_bad,
        Some("caller_bad"),
        Some(PropertyCategory::Functional),
        "Verify ASSERT directive",
    );
}

#[test]
fn test_v111_syscall_without_dest_writes_to_rax_slot() {
    // SYSCALL không có `%dest =` mặc định ghi kết quả vào biến `%rax` (trong cả Verifier lẫn Codegen).
    let code = r#"
FUNC main() -> i64
  %sys_getpid = CONST i64 39
  %z = CONST i64 0
  SYSCALL %sys_getpid %z %z %z
  ASSERT %rax >= -4096
  %ok = GT i64 %rax 0
  BR_IF %ok .good
  RET 1
LABEL .good
  RET 0
END_FUNC
"#;
    assert_eq!(verify_and_run_elf(code, true), 0);
}

#[test]
fn test_v112_parser_rejects_empty_or_unclosed_len() {
    let err_empty = Parser::parse_expr("len() > 0", 5).expect_err("Empty len() must fail");
    assert_eq!(err_empty.line_no, 5);
    assert!(err_empty.message.contains("Empty 'len()'"));

    let err_unclosed = Parser::parse_expr("len(%arr > 0", 7).expect_err("Unclosed len( must fail");
    assert_eq!(err_unclosed.line_no, 7);
    assert!(err_unclosed.message.contains("Unclosed 'len(...)'"));
}
