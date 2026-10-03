import ArenaCoreTests.InterpVectors

/-!
Regression pin for the NPAI v1 reference semantics: every vector's outcome
and fuel consumption.  (`#guard` evaluates with the compiler/interpreter;
these are tests, not proofs, and are never part of a certificate.)
Kernel-checked interpreter evaluation is exercised by `Toy` (`decide +kernel`).
-/

open ArenaCore InterpVectors

def expectedSummaries : List (String × String) :=
  [("arith_wrap_add_shl", "accept/7"),
   ("arith_sub_wrap", "accept/5"),
   ("arith_mul_overflow", "accept/4"),
   ("arith_shift_mod64", "accept/6"),
   ("arith_bitops", "accept/8"),
   ("ltu_and_shr", "accept/9"),
   ("loop_sum_1_to_10", "accept/75"),
   ("jz_taken", "accept/3"),
   ("halt_reject", "reject/1"),
   ("fall_off_end_traps", "trap/1"),
   ("jump_out_of_range_traps", "trap/1"),
   ("out_of_fuel_infinite_loop", "out_of_fuel/100"),
   ("zero_fuel", "out_of_fuel/0"),
   ("tlen_tload", "accept/9"),
   ("tload_oob_traps", "trap/2"),
   ("tcopy_oob_traps", "trap/4"),
   ("tcopy_mem_oob_traps", "trap/4"),
   ("st8_ld8_mod256", "accept/7"),
   ("ld8_oob_traps", "trap/2"),
   ("data_segment", "accept/9"),
   ("sha256_claim_matches_pub", "accept/8"),
   ("sha256_claim_mismatch_rejects", "reject/8"),
   ("sha256_empty_input", "accept/7"),
   ("sha256_overlapping_dst", "accept/5"),
   ("sha256_dst_oob_traps", "trap/3"),
   ("sha256_cost_large", "accept/69"),
   ("sha256_cost_large_oof", "out_of_fuel/68"),
   ("rohash_is_tagged_sha256", "accept/8"),
   ("rohash_differs_from_sha256", "reject/8"),
   ("rohash_cost_and_trap", "trap/3"),
   ("memeq_len0", "accept/2"),
   ("out_buffers", "accept/8"),
   ("decode_bad_magic", "decode_error"),
   ("decode_bad_version", "decode_error"),
   ("decode_empty_program_traps", "trap/0"),
   ("decode_trailing_byte", "decode_error"),
   ("decode_truncated", "decode_error"),
   ("decode_reg16", "decode_error"),
   ("decode_nonzero_unused_field", "decode_error"),
   ("decode_unknown_opcode", "decode_error"),
   ("decode_bad_tape_id", "decode_error"),
   ("decode_out_id_2", "decode_error"),
   ("decode_memsize_too_large", "decode_error"),
   ("decode_data_longer_than_mem", "decode_error"),
   ("decode_max_imm_const", "accept/7")]
  

#guard cases.length == expectedSummaries.length
#guard (cases.zip expectedSummaries).all fun (c, n, e) => c.name == n && (expect c).summary == e

/-- A kernel-checked interpreter run (no `native_decide`). -/
theorem loop_sum_kernel :
    (expect ((cases.find? (·.name == "loop_sum_1_to_10")).getD
      { name := "", image := [] })).summary = "accept/75" := by decide +kernel
