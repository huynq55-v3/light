use light::ast::Expr;
use light::parser::Parser;
use light::verifier::{PropertyCategory, VerificationResult, Verifier};

#[test]
fn test_v1_inductive_step_mutation_step2_fails() {
    // V1: Loop steps by 2 instead of 1 (%next_i = ADD %i 2)
    // Invariant %i <= n must fail induction because when %i = n - 1, %next_i = n + 1 > n.
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

    let program = Parser::parse(code).expect("Parse V1");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_inductive = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Inductive && goal_name.contains("Step 2: Inductive Step")
        }
        _ => false,
    });

    assert!(
        failed_inductive,
        "V1 Mutation test failed: Verifier should have failed Step 2 Inductive Step for %i + 2 step! Got: {:?}",
        results
    );
}

#[test]
fn test_v2_accumulator_subtraction_invariant_fails() {
    // V2: Loop subtracts 100 from %acc (%acc = SUB %acc 100)
    // Invariant %acc >= 0 must fail inductive step because %next_acc can become negative.
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

    let program = Parser::parse(code).expect("Parse V2");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_inductive = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Inductive && goal_name.contains("Step 2: Inductive Step")
        }
        _ => false,
    });

    assert!(
        failed_inductive,
        "V2 Mutation test failed: Verifier should have failed Step 2 Inductive Step for subtracting 100 from %acc! Got: {:?}",
        results
    );
}

#[test]
fn test_v3_omitted_counter_update_termination_fails() {
    // V3: Counter is never advanced (%i = MOV %next_i is omitted).
    // DECREASES n - %i must fail Step 4b (strictly decreasing ranking function).
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
    # Omitted: %i = MOV %next_i
  END_LOOP sum_loop
  ENSURE %acc >= 0
  RET %acc
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V3");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_termination = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Termination && goal_name.contains("Step 4b")
        }
        _ => false,
    });

    assert!(
        failed_termination,
        "V3 Mutation test failed: Verifier should have failed Step 4b (ranking strictly decreases) when %i is not updated! Got: {:?}",
        results
    );
}

#[test]
fn test_v4_inverted_ranking_function_fails() {
    // V4: DECREASES %i in an increasing loop (%i grows from 0 to n).
    // Ranking function strictly increases instead of decreasing, so Step 4b must fail.
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

    let program = Parser::parse(code).expect("Parse V4");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_termination = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Termination && goal_name.contains("Step 4b")
        }
        _ => false,
    });

    assert!(
        failed_termination,
        "V4 Mutation test failed: Verifier should have caught DECREASES %i strictly decreasing violation! Got: {:?}",
        results
    );
}

#[test]
fn test_v5_callsite_precondition_violation_fails() {
    // V5: Caller passes argument violating callee REQUIRE precondition (passes 1005 when callee requires <= 1000)
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

    let program = Parser::parse(code).expect("Parse V5");
    let caller_fn = program.functions.iter().find(|f| f.name == "caller").unwrap();
    let results = Verifier::verify_function(caller_fn, Some(&program));

    let failed_safety = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Verify REQUIRE contract of 'callee'")
        }
        _ => false,
    });

    assert!(
        failed_safety,
        "V5 Mutation test failed: Verifier should have rejected caller passing 1005 to callee(REQUIRE x <= 1000)! Got: {:?}",
        results
    );
}

#[test]
fn test_v6_unsupported_instruction_in_loop_yields_unknown() {
    // V6: An instruction unsupported by loop symbolic VCGen (e.g. SYSCALL) inside loop body
    // Soundness guarantee: Verifier must return Unknown instead of reporting false Verified!
    let code = r#"
FUNC loop_with_unsupported(n: i64) -> i64
  REQUIRE n >= 0
  %i = CONST i64 0
  LOOP bad_loop
    INVARIANT %i >= 0
    %done = GTE i64 %i n
    BREAK_IF %done
    %next_i = ADD i64 %i 1
    # Raw Syscall inside loop is not supported by symbolic transition extractor
    %res = SYSCALL 60 %next_i 0 0
    %i = MOV %next_i
  END_LOOP bad_loop
  RET %i
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V6");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let got_unknown = results.iter().any(|r| match r {
        VerificationResult::Unknown { category, goal_name, .. } => {
            *category == PropertyCategory::Inductive && goal_name.contains("Symbolic Loop Execution")
        }
        _ => false,
    });

    assert!(
        got_unknown,
        "V6 Soundness test failed: Unsupported loop instruction should yield VerificationResult::Unknown! Got: {:?}",
        results
    );
}

#[test]
fn test_v7_assert_false_fails() {
    // V7: Explicit ASSERT false directive must fail verification
    let code = r#"
FUNC check_assert() -> i64
  %a = CONST i64 5
  ASSERT %a == 10
  RET %a
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V7");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_assert = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        failed_assert,
        "V7 test failed: Verifier should have failed on violated ASSERT directive! Got: {:?}",
        results
    );
}

#[test]
fn test_v8_memory_bounds_load8_out_of_bounds_fails() {
    // V8: Accessing byte outside allocated buffer capacity must fail safety check
    let code = r#"
FUNC check_oob() -> i64
  %buf = ALLOC slice<u8> 16
  %val = LOAD8 %buf 20
  RET %val
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V8");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_bounds = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Memory 8-bit bounds check")
        }
        _ => false,
    });

    assert!(
        failed_bounds,
        "V8 test failed: Verifier should have caught out-of-bounds LOAD8 access! Got: {:?}",
        results
    );
}

#[test]
fn test_v9_div_zero_dynamic_context_fails() {
    // V9: Context-sensitive division by zero: divisor computed dynamically as 5 - 5 = 0
    let code = r#"
FUNC check_div() -> i64
  %a = CONST i64 5
  %b = CONST i64 5
  %denom = SUB i64 %a %b
  %res = DIV i64 100 %denom
  RET %res
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V9");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_div_zero = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Division-by-Zero safety")
        }
        _ => false,
    });

    assert!(
        failed_div_zero,
        "V9 test failed: Context-sensitive division by zero should have been caught! Got: {:?}",
        results
    );
}

#[test]
fn test_v10_negative_constants_work_without_syntax_error() {
    // V10: Negative integer constants formatted with bvneg in SMT without Z3 syntax errors
    let code = r#"
FUNC check_negative(x: i64) -> i64
  REQUIRE x <= -50 && x >= -1000
  %sub = SUB i64 x 100
  ENSURE %sub < -40
  RET %sub
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V10");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    // Ensure it verifies without syntax errors
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));

    assert!(
        all_passed,
        "V10 test failed: Negative constants in SMT query caused failure: {:?}",
        results
    );
}

#[test]
fn test_v11_ssa_reassignment_vacuous_truth_prevention() {
    // V11: Re-assigning variable %x in straightline code must NOT trigger vacuous truth (UNSAT)
    // %x = 1, then %x = %x + 1 -> %x is now 2. ENSURE %x == 999 MUST FAIL.
    // If vacuous truth bug was present, 1 = 2 would be UNSAT and ENSURE 999 would falsely PASS.
    let code = r#"
FUNC check_vacuous() -> i64
  %x = CONST i64 1
  %x = ADD i64 %x 1
  ENSURE %x == 999
  RET %x
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V11");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_ensure = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ENSURE postcondition")
        }
        _ => false,
    });

    assert!(
        failed_ensure,
        "V11 Vacuous Truth test failed: Verifier should have rejected ENSURE %x == 999 under SSA renaming! Got: {:?}",
        results
    );
}

#[test]
fn test_v12_in_loop_out_of_bounds_fails() {
    // V12: In-loop safety checks must havoc loop-modified variables at loop entry.
    // Buffer has size 8, but loop counter progresses up to 10.
    // Verifier must detect potential out-of-bounds access across loop iterations!
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

    let program = Parser::parse(code).expect("Parse V12");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_bounds = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Memory 8-bit bounds check on '%buf'")
        }
        _ => false,
    });

    assert!(
        failed_bounds,
        "V12 test failed: Verifier should have caught in-loop buffer overflow on %buf (capacity 8, offset up to 9)! Got: {:?}",
        results
    );
}

#[test]
fn test_v13_forward_jump_label_branching() {
    // V13: Forward JUMP skipping in emit_symbolic_prefix.
    // When BR_IF is not taken (false), fallthrough path jumps over the taken block.
    // %res must remain 100, not overwritten by 200 in the skipped branch.
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

    let program = Parser::parse(code).expect("Parse V13");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let passed_assert = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        passed_assert,
        "V13 test failed: Forward jump skipping failed; ASSERT %res == 100 should verify! Got: {:?}",
        results
    );
}

#[test]
fn test_v14_multibreak_loop_ite_merge() {
    // V14: Multi-break loop state merging using nested ite.
    // If loop has multiple BREAK_IF points, exit step merges states with ite.
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

    let program = Parser::parse(code).expect("Parse V14");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let passed_exit = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Step 3: Exit Step")
        }
        _ => false,
    });

    assert!(
        passed_exit,
        "V14 test failed: Multi-break merging should verify ENSURE %val >= 10 && %val <= 20! Got: {:?}",
        results
    );
}

#[test]
fn test_v15_loop_invariant_constant_preservation() {
    // V15: Pre-loop constants and slice lengths are preserved into Step 3 (Exit Step).
    // Constant %limit is defined before loop, used in loop invariant and ENSURE postcondition.
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

    let program = Parser::parse(code).expect("Parse V15");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let passed_exit = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Step 3: Exit Step")
        }
        _ => false,
    });

    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));

    assert!(
        passed_exit && all_passed,
        "V15 test failed: Pre-loop constant %limit should be preserved in Step 3 Exit Step! Got: {:?}",
        results
    );
}

#[test]
fn test_v16_early_return_violating_ensure_fails() {
    // V16: RET_IF path returning a negative value must fail ENSURE %res > 0
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

    let program = Parser::parse(code).expect("Parse V16");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_early_ret = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("early return (RET_IF)")
        }
        _ => false,
    });

    assert!(
        failed_early_ret,
        "V16 test failed: Early return with negative value should have failed ENSURE! Got: {:?}",
        results
    );
}

#[test]
fn test_v17_branching_join_phi_node_soundness() {
    // V17: If then branch sets %x = -999 and else branch sets %x = 10,
    // post-join ASSERT %x > 0 must FAIL because the condition can be true!
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

    let program = Parser::parse(code).expect("Parse V17");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_assert = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        failed_assert,
        "V17 test failed: Phi-node join should expose then-branch %x = -999 and fail ASSERT %x > 0! Got: {:?}",
        results
    );
}

#[test]
fn test_v18_loop_without_invariant_fails_exit_step() {
    // V18: Loop without INVARIANT cannot prove postcondition ENSURE %i == 10
    // Because without an invariant, %i at exit cannot be proven to equal 10.
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

    let program = Parser::parse(code).expect("Parse V18");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_exit = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Step 3: Exit Step")
        }
        _ => false,
    });

    assert!(
        failed_exit,
        "V18 test failed: Loop without INVARIANT should not be able to prove ENSURE %i == 10! Got: {:?}",
        results
    );
}

#[test]
fn test_v19_bool_sort_in_contracts() {
    // V19: Bare boolean/flag variables in ASSERT, REQUIRE, and !%var should work without Z3 sort errors
    let code = r#"
FUNC test_bool_contract(flag: bool) -> i64
  REQUIRE flag
  %res = CONST i64 1
  ASSERT flag
  ASSERT !false
  RET %res
END_FUNC
"#;

    let program = Parser::parse(code).expect("Parse V19");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));

    assert!(
        all_passed,
        "V19 test failed: Boolean sort in contracts caused solver failure! Got: {:?}",
        results
    );
}

#[test]
fn test_v20_parser_operator_precedence_and_unary_minus() {
    // V20: Expressions like %x - -5 and a - b + c and %x * %y
    let expr1 = Parser::parse_expr("%x - -5", 1).expect("parse expr1");
    let smt1 = Verifier::expr_to_smt(&expr1);
    assert_eq!(smt1, "(bvsub x (bvneg (_ bv5 64)))");

    let expr2 = Parser::parse_expr("10 - 5 + 2", 1).expect("parse expr2");
    let smt2 = Verifier::expr_to_smt(&expr2);
    // Left-associative: (10 - 5) + 2
    assert_eq!(smt2, "(bvadd (bvsub (_ bv10 64) (_ bv5 64)) (_ bv2 64))");

    let expr3 = Parser::parse_expr("%x * %y", 1).expect("parse expr3");
    let smt3 = Verifier::expr_to_smt(&expr3);
    assert_eq!(smt3, "(bvmul x y)");
}

#[test]
fn test_v21_post_loop_safety_out_of_bounds_fails() {
    // V21: Post-loop safety checks (find_loops_before).
    // Buffer has capacity 10, loop progresses %i to 15.
    // Memory access on %buf with %i AFTER END_LOOP must fail!
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

    let program = Parser::parse(code).expect("Parse V21");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_bounds = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Memory 8-bit bounds check on '%buf'")
        }
        _ => false,
    });

    assert!(
        failed_bounds,
        "V21 test failed: Post-loop out-of-bounds on %buf (capacity 10, %i == 15) must be caught! Got: {:?}",
        results
    );
}

#[test]
fn test_v22_mid_ret_violating_ensure_fails() {
    // V22: Mid-function RET must be verified against ENSURE postcondition.
    // If %cond is true, returning -1 violates ENSURE %res >= 0.
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

    let program = Parser::parse(code).expect("Parse V22");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_ret = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ENSURE on branch return (RET)")
        }
        _ => false,
    });

    assert!(
        failed_ret,
        "V22 test failed: Mid-function RET with bad postcondition (-1 >= 0) must fail! Got: {:?}",
        results
    );
}

#[test]
fn test_v23_branch_before_ret_does_not_pollute_later_labels() {
    // V23: Path terminated by RET must not merge dead state into following LABEL
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

    let program = Parser::parse(code).expect("Parse V23");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let passed_assert = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        passed_assert,
        "V23 test failed: Label .branch_true after RET should verify independently! Got: {:?}",
        results
    );
}

#[test]
fn test_v24_in_loop_branching_phi_node() {
    // V24: Loop transition with inner branching (BR_IF + JUMP + LABEL).
    // In each iteration, if %even is true, %acc is incremented by 2, else by 1.
    // Invariant %acc >= %i preserved inductively.
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

    let program = Parser::parse(code).expect("Parse V24");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let inductive_passed = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Inductive && goal_name.contains("Step 2: Inductive Step")
        }
        _ => false,
    });

    assert!(
        inductive_passed,
        "V24 test failed: In-loop branch Phi-node inductive step must PASS! Got: {:?}",
        results
    );
}

#[test]
fn test_v25_call_with_constant_args_propagates_ensure() {
    // V25: CALL with constant arguments (Operand::Const) substitutes callee params correctly in ENSURE
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

    let program = Parser::parse(code).expect("Parse V25");
    let results = Verifier::verify_function(&program.functions[1], Some(&program));

    let assert_passed = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        assert_passed,
        "V25 test failed: CALL with constant argument 5 must propagate ENSURE %sq >= 0 to ASSERT %val >= 0! Got: {:?}",
        results
    );
}

#[test]
fn test_v26_parenthesized_expressions_in_contracts() {
    // V26: Complex parenthesized expressions parsed with proper precedence
    let expr1 = Parser::parse_expr("(%a + %b) * 2 == %res", 1).expect("parse expr1");
    let smt1 = Verifier::expr_to_smt(&expr1);
    assert_eq!(smt1, "(= (bvmul (bvadd a b) (_ bv2 64)) res)");

    let expr2 = Parser::parse_expr("(%x > 0 && %y > 0) || %z == 0", 1).expect("parse expr2");
    let smt2_bool = Verifier::expr_to_smt_bool(&expr2);
    assert_eq!(smt2_bool, "(or (and (bvsgt x (_ bv0 64)) (bvsgt y (_ bv0 64))) (= z (_ bv0 64)))");
}

#[test]
fn test_v27_post_loop_break_state_restored_accurately() {
    // V27: Post-loop state must match the state at BREAK_IF, not the over-stepped state
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

    let program = Parser::parse(code).expect("Parse V27");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let assert_passed = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ASSERT directive")
        }
        _ => false,
    });

    assert!(
        assert_passed,
        "V27 test failed: ASSERT %i == 10 after loop must PASS! Got: {:?}",
        results
    );
}

#[test]
fn test_v28_loop_with_early_ret_if_verified_against_ensure() {
    // V28: A function with both LOOP and RET_IF must verify RET_IF against ENSURE
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

    let program = Parser::parse(code).expect("Parse V28");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let failed_early_ret = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ENSURE on early return (RET_IF)")
        }
        _ => false,
    });

    assert!(
        failed_early_ret,
        "V28 test failed: Early return RET_IF with -1 in a loop function must fail ENSURE %res >= 0! Got: {:?}",
        results
    );
}

#[test]
fn test_v29_early_ret_value_aliased_to_canonical_ret_var() {
    // V29: RET_IF returning %zero is aliased to canonical %ret in ENSURE %ret >= 0
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

    let program = Parser::parse(code).expect("Parse V29");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));

    assert!(
        all_passed,
        "V29 test failed: RET_IF returning %zero must satisfy ENSURE %ret >= 0! Got: {:?}",
        results
    );
}

#[test]
fn test_v30_pre_loop_binary_expression_preserved_in_contracts() {
    // V30: Pre-loop binary expressions (ADD, SUB) preserved into loop exit and inductive step
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

    let program = Parser::parse(code).expect("Parse V30");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let passed_exit = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Step 3: Exit Step")
        }
        _ => false,
    });

    assert!(
        passed_exit,
        "V30 test failed: Pre-loop %limit = ADD n 10 must be preserved into Exit Step! Got: {:?}",
        results
    );
}

#[test]
fn test_v31_unary_minus_expressions_parsed_as_subtraction() {
    // V31: Unary minus (-%a, -(%a + %b)) parsed as (0 - expr)
    let expr1 = Parser::parse_expr("-%a", 1).expect("parse -%a");
    let smt1 = Verifier::expr_to_smt(&expr1);
    assert_eq!(smt1, "(bvsub (_ bv0 64) a)");

    let expr2 = Parser::parse_expr("-(%a + %b)", 1).expect("parse -(%a + %b)");
    let smt2 = Verifier::expr_to_smt(&expr2);
    assert_eq!(smt2, "(bvsub (_ bv0 64) (bvadd a b))");
}

#[test]
fn test_v32_both_branches_end_in_ret() {
    // V32: Function where both if and else branches end in RET
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

    let program = Parser::parse(code).expect("Parse V32");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));

    let mid_ret_passed = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ENSURE on branch return (RET)")
        }
        _ => false,
    });
    let final_ret_passed = results.iter().any(|r| match r {
        VerificationResult::Verified { goal_name, category } => {
            *category == PropertyCategory::Functional && goal_name.contains("Verify ENSURE postcondition")
        }
        _ => false,
    });

    assert!(
        mid_ret_passed && final_ret_passed,
        "V32 test failed: Both branch RETs must verify against ENSURE! Got: {:?}",
        results
    );
}

#[test]
fn test_v33_pre_loop_intermediate_binary_chain() {
    // V33: Chained binary operations before loop with intermediate variables
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
    let program = Parser::parse(code).expect("Parse V33");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V33 test failed: Intermediate pre-loop binary chain must verify all loop steps! Got: {:?}", results);
}

#[test]
fn test_v34_loop_with_continue_if_verifies() {
    // V34: Loop containing CONTINUE_IF verified inductively without unsupported error
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
    let program = Parser::parse(code).expect("Parse V34");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V34 test failed: CONTINUE_IF in loop must be supported and verify! Got: {:?}", results);
}

#[test]
fn test_v35_subst_expr_vars_len_preserves_length() {
    // V35: subst_expr_vars directly maps Expr::Len to {arr}_len without fabricating invalid names
    let mut map = std::collections::HashMap::new();
    map.insert("buf_len".to_string(), "buf_length_val".to_string());
    map.insert("buf".to_string(), "buf_ptr_v0".to_string());

    let expr = Expr::Len("buf".to_string());
    let substituted = Verifier::subst_expr_vars(&expr, &map);
    assert_eq!(substituted, Expr::Var("buf_length_val".to_string()));

    let smt = Verifier::expr_to_smt(&substituted);
    assert_eq!(smt, "buf_length_val");
}

#[test]
fn test_v36_both_branches_different_ret_registers_straightline() {
    // V36: Both branches return different registers and ENSURE references canonical %ret
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
    let program = Parser::parse(code).expect("Parse V36");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V36 test failed: Branches with different RET registers must verify against ENSURE %ret! Got: {:?}", results);
}

#[test]
fn test_v37_post_loop_slicelen_and_load8() {
    // V37: SLICE_LEN and LOAD8 executed post-loop correctly tracked in Exit Step
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
    let program = Parser::parse(code).expect("Parse V37");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V37 test failed: Post-loop SLICE_LEN and LOAD8 must be tracked in Exit Step! Got: {:?}", results);
}

#[test]
fn test_v38_straightline_with_const_ret() {
    // V38: Straightline function returning immediate constant 0 satisfies ENSURE %ret == 0
    let code = r#"
FUNC returns_zero(x: i64) -> i64
  REQUIRE x >= 0
  ENSURE %ret == 0
  RET 0
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse V38");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V38 test failed: Function returning constant 0 must satisfy ENSURE %ret == 0! Got: {:?}", results);
}

#[test]
fn test_ivl_verify_function_end_to_end() {
    // Kiểm chứng end-to-end sử dụng kiến trúc mới: IvlLowerer + Universal VcGen (Boogie architecture)
    let code = r#"
FUNC abs_val(x: i64) -> i64
  REQUIRE x >= 0
  %two = CONST i64 2
  %half = DIV i64 x %two
  ENSURE %ret >= 0
  RET %half
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse IVL test");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    assert_eq!(results.len(), 2);
    // Goal 1: Division-by-zero on %two (2 != 0) -> Verified!
    assert!(matches!(results[0], VerificationResult::Verified { .. }));
    // Goal 2: ENSURE %ret >= 0 -> Verified!
    assert!(matches!(results[1], VerificationResult::Verified { .. }));
}

#[test]
fn test_ivl_on_real_memory_bounds_v8() {
    // Chạy trực tiếp V8 trên động cơ mới verify_function_ivl
    let code = r#"
FUNC check_oob() -> i64
  %buf = ALLOC slice<u8> 16
  %val = LOAD8 %buf 20
  RET %val
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse V8");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Memory 8-bit bounds check")
        }
        _ => false,
    });
    assert!(failed, "IVL Engine phải bắt được lỗi tràn bộ đệm LOAD8 ở offset 20! Got: {:?}", results);
}

#[test]
fn test_ivl_on_real_division_by_zero_v9() {
    // Chạy trực tiếp V9 (5 - 5 = 0) trên động cơ mới verify_function_ivl
    let code = r#"
FUNC check_div() -> i64
  %a = CONST i64 5
  %b = CONST i64 5
  %denom = SUB i64 %a %b
  %res = DIV i64 100 %denom
  RET %res
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse V9");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Division-by-Zero safety")
        }
        _ => false,
    });
    assert!(failed, "IVL Engine phải bắt được lỗi chia cho 0 ngữ cảnh động! Got: {:?}", results);
}

#[test]
fn test_ivl_on_real_early_return_violation_v16() {
    // Chạy trực tiếp V16 (RET_IF trả về số âm vi phạm ENSURE) trên động cơ mới verify_function_ivl
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
    let program = Parser::parse(code).expect("Parse V16");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Functional && goal_name.contains("early return (RET_IF)")
        }
        _ => false,
    });
    assert!(failed, "IVL Engine phải bắt được lỗi RET_IF trả về giá trị âm! Got: {:?}", results);
}

#[test]
fn test_ivl_on_real_early_return_success_v29() {
    // Chạy trực tiếp V29 (RET_IF trả về %zero thỏa mãn ENSURE %ret >= 0) trên động cơ mới verify_function_ivl
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
    let program = Parser::parse(code).expect("Parse V29");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "IVL Engine phải VERIFY thành công hàm check_nonneg với RET_IF! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse loop test");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    assert_eq!(results.len(), 7, "Cần có đủ 7 goals: 2 x Step 1, 2 x Step 2, Step 4a, Step 4b, Step 3. Got: {:?}", results);
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "IVL Engine phải kiểm chứng thành công cả 5 bước Hoare Logic của LOOP! Got: {:?}", results);
}

#[test]
fn test_ivl_on_real_in_loop_oob_v12() {
    // V12 chạy trên verify_function_ivl: bắt lỗi ghi ngoài biên bên trong vòng lặp!
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
    let program = Parser::parse(code).expect("Parse V12");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed_bounds = results.iter().any(|r| match r {
        VerificationResult::Failed { category, goal_name, .. } => {
            *category == PropertyCategory::Safety && goal_name.contains("Memory 8-bit bounds check")
        }
        _ => false,
    });
    assert!(failed_bounds, "IVL Engine phải bắt được lỗi tràn bộ nhớ STORE8 trong thân vòng lặp! Got: {:?}", results);
}

#[test]
fn test_ivl_on_real_unsupported_in_loop_v6() {
    // V6 chạy trên verify_function_ivl: lệnh không hỗ trợ trong vòng lặp phải trả về Unknown!
    let code = r#"
FUNC loop_with_unsupported(n: i64) -> i64
  REQUIRE n >= 0
  %i = CONST i64 0
  LOOP bad_loop
    INVARIANT %i >= 0
    %done = GTE i64 %i n
    BREAK_IF %done
    %r = SYSCALL 1 1 0 0
    %i = ADD i64 %i 1
  END_LOOP bad_loop
  RET %i
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse V6");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let has_unknown = results.iter().any(|r| matches!(r, VerificationResult::Unknown { .. }));
    assert!(has_unknown, "IVL Engine phải trả về Unknown khi có SYSCALL trong thân vòng lặp! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v13_branching() {
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
    let program = Parser::parse(code).expect("Parse V13");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V13 trên IVL phải PASS! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v17_join_phi() {
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
    let program = Parser::parse(code).expect("Parse V17");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed = results.iter().any(|r| matches!(r, VerificationResult::Failed { .. }));
    assert!(failed, "V17 trên IVL phải bắt được lỗi x=-999! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v22_mid_ret() {
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
    let program = Parser::parse(code).expect("Parse V22");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let failed = results.iter().any(|r| matches!(r, VerificationResult::Failed { .. }));
    assert!(failed, "V22 trên IVL phải bắt được lỗi RET -1! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v32_both_branches_end_in_ret() {
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
    let program = Parser::parse(code).expect("Parse V32");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V32 trên IVL phải PASS! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v36_both_branches_diff_ret() {
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
    let program = Parser::parse(code).expect("Parse V36");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V36 trên IVL phải PASS! Got: {:?}", results);
}

#[test]
fn test_ivl_on_v24_in_loop_branching() {
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
    let program = Parser::parse(code).expect("Parse V24");
    let results = Verifier::verify_function_ivl(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "V24 trên IVL phải PASS! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V39");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_div_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, category, .. } if *category == PropertyCategory::Safety && goal_name.contains("Division-by-Zero safety")));
    assert!(has_div_fail, "Phải phát hiện lỗi tràn số i64::MIN / -1! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V40");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_assert_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("ASSERT")));
    assert!(has_assert_fail, "ASSERT sai với biến tên '%is_unsat' phải BÁO LỖI (Failed), không được nhầm thành Verified! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V41");
    let results = Verifier::verify_function(&program.functions[1], Some(&program));
    let has_def_assign_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("SSA Definite Assignment")));
    assert!(has_def_assign_fail, "Tham số chưa khởi tạo truyền vào CALL phải bị bắt lỗi Definite Assignment! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V42");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("ASSERT")));
    assert!(has_fail, "Sau loop làm biến đổi %buf, ASSERT %val == 42 phải FAIL vì bộ nhớ đã bị havoc! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V43");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("ASSERT")));
    assert!(has_fail, "ASSERT sai sau điểm join không được pass do vacuous truth! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V44");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("ASSERT")));
    assert!(has_fail, "STORE8 -1 sau đó LOAD8 không được gây Vacuous Truth làm ASSERT %val == 0 bị pass! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V45");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("ASSERT")));
    assert!(has_fail, "ASSERT %val == 20 phải FAIL vì khi cond <= 0, %buf[0] == 10! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V46");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_fail = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("Step 1")));
    assert!(has_fail, "Vòng lặp thứ 2 có invariant sai (%j >= 100 khi %j == 0) phải bị phát hiện ở Step 1! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V47");
    let results = Verifier::verify_function(&program.functions[1], Some(&program));
    let has_mismatch = results.iter().any(|r| matches!(r, VerificationResult::Failed { goal_name, .. } if goal_name.contains("Call argument count mismatch")));
    assert!(has_mismatch, "Gọi hàm thừa tham số phải bị bắt lỗi Safety! Got: {:?}", results);
}

#[test]
fn test_v48_ensure_without_ret_fails() {
    let code = r#"
FUNC no_ret_func(x: i64) -> i64
  ENSURE %ret > 0
  %y = ADD i64 x 1
END_FUNC
"#;
    let program = Parser::parse(code).expect("Parse V48");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let has_no_ret = results.iter().any(|r| matches!(r, VerificationResult::Failed { reason, .. } if reason.contains("has no RET")));
    assert!(has_no_ret, "Hàm có ENSURE nhưng không có RET phải bị đánh dấu FAILED! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V49");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let no_z3_error = results.iter().all(|r| !matches!(r, VerificationResult::Failed { reason, .. } if reason.contains("Z3 solver error") || reason.contains("sort")));
    assert!(no_z3_error, "Z3 không được báo sort error khi chỉ 1 nhánh sửa đổi bộ nhớ! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V50");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "Vòng lặp lồng nhau phải verify thành công và không bị hút lẫn invariant! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V51");
    let results = Verifier::verify_function(&program.functions[1], Some(&program));
    let no_error = results.iter().all(|r| !matches!(r, VerificationResult::Failed { reason, .. } if reason.contains("Z3 solver error")));
    assert!(no_error, "Nhánh Diamond có CALL và STORE_STR phải verify trơn tru không lỗi solver! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V52");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "STORE_STR 'Hello' tại offset 0 phải đọc ra byte 72 ('H')! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V53");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "Đọc từ %ptr phải thấy giá trị 42 ghi vào %buf do cơ chế buffer aliasing! Got: {:?}", results);
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
    let program = Parser::parse(code).expect("Parse V54");
    let results = Verifier::verify_function(&program.functions[0], Some(&program));
    let all_passed = results.iter().all(|r| matches!(r, VerificationResult::Verified { .. }));
    assert!(all_passed, "Vòng lặp có 2 điểm BREAK_IF phân nhánh theo mode phải verify chính xác ENSURE postcondition! Got: {:?}", results);
}









