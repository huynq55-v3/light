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

