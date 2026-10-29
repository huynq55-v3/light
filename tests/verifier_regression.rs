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
