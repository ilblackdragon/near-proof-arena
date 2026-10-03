import ArenaCore.Interp

/-!
# NPAI v1 differential test vectors

Programs + inputs whose expected outcomes are computed by the Lean
reference semantics (`ArenaCore.Interp.runFull`).  `lake exe
arena-interp-ref vectors <out.json>` serialises them for the Rust
interpreter's differential test-suite.
-/

namespace ArenaCore.InterpVectors

open Interp

structure Case where
  name : String
  /-- Raw program image (may be deliberately malformed). -/
  image : Bytes
  pub : Bytes := []
  claim : Bytes := []
  proof : Bytes := []
  fuel : Nat := 1000

def prog (memSize : Nat) (code : List Instr) (data : Bytes := []) : Bytes :=
  encode { memSize, data, code }

def r (n : Nat) : Nat := n

def cases : List Case := [
  -- arithmetic & wrapping
  { name := "arith_wrap_add_shl",
    image := prog 0 [.const 1 0xFFFFFFFF, .const 6 32, .bin .shl 2 1 6, .bin .add 3 2 1,
                     .addi 4 3 1, .bin .eq 5 4 0, .halt 5] },
  { name := "arith_sub_wrap",
    image := prog 0 [.const 1 1, .bin .sub 2 0 1, .addi 3 2 1, .bin .eq 4 3 0, .halt 4] },
  { name := "arith_mul_overflow",
    image := prog 0 [.const 1 0xFFFFFFFF, .bin .mul 2 1 1, .bin .mul 3 2 2, .halt 3] },
  { name := "arith_shift_mod64",
    image := prog 0 [.const 1 1, .const 2 65, .bin .shl 3 1 2, .const 4 2, .bin .eq 5 3 4,
                     .halt 5] },
  { name := "arith_bitops",
    image := prog 0 [.const 1 0xF0F0, .const 2 0x0FF0, .bin .and 3 1 2, .bin .or 4 1 2,
                     .bin .xor 5 1 2, .bin .sub 6 4 3, .bin .eq 7 6 5, .halt 7] },
  { name := "ltu_and_shr",
    image := prog 0 [.const 1 5, .const 2 7, .bin .ltu 3 1 2, .bin .ltu 4 2 1, .const 5 2,
                     .bin .shr 6 2 5, .bin .eq 7 6 3, .bin .xor 8 7 4, .halt 8] },
  -- control flow
  { name := "loop_sum_1_to_10",
    image := prog 0 [.const 1 10, .const 2 0, .bin .add 2 2 1, .addi 1 1 0xFFFFFFFF,
                     .const 6 0xFFFFFFFF, .const 7 32, .bin .shl 6 6 7, .bin .add 1 1 6,
                     .jnz 1 2, .const 3 55, .bin .eq 4 2 3, .halt 4] },
  { name := "jz_taken",
    image := prog 0 [.jz 0 3, .const 1 0, .halt 1, .const 1 1, .halt 1] },
  { name := "halt_reject",
    image := prog 0 [.halt 0] },
  { name := "fall_off_end_traps",
    image := prog 0 [.const 1 1] },
  { name := "jump_out_of_range_traps",
    image := prog 0 [.jmp 100] },
  { name := "out_of_fuel_infinite_loop",
    image := prog 0 [.jmp 0], fuel := 100 },
  { name := "zero_fuel",
    image := prog 0 [.halt 0], fuel := 0 },
  -- tapes
  { name := "tlen_tload",
    image := prog 0 [.tlen 1 .claim, .const 2 3, .bin .eq 3 1 2, .const 4 2,
                     .tload 5 4 .claim, .const 6 0x63, .bin .eq 7 5 6, .bin .and 8 3 7, .halt 8],
    claim := [0x61, 0x62, 0x63] },
  { name := "tload_oob_traps",
    image := prog 0 [.const 1 3, .tload 2 1 .claim, .halt 2], claim := [1, 2, 3] },
  { name := "tcopy_oob_traps",
    image := prog 16 [.const 1 0, .const 2 1, .const 3 3, .tcopy 1 2 3 .proof, .halt 3],
    proof := [1, 2, 3] },
  { name := "tcopy_mem_oob_traps",
    image := prog 4 [.const 1 2, .const 2 0, .const 3 3, .tcopy 1 2 3 .proof, .halt 3],
    proof := [1, 2, 3] },
  -- memory
  { name := "st8_ld8_mod256",
    image := prog 8 [.const 1 0x1FF, .const 2 7, .st8 2 1, .ld8 3 2, .const 4 0xFF,
                     .bin .eq 5 3 4, .halt 5] },
  { name := "ld8_oob_traps",
    image := prog 8 [.const 1 8, .ld8 2 1, .halt 2] },
  { name := "data_segment",
    image := prog 4 [.const 1 1, .ld8 2 1, .const 3 0xBB, .bin .eq 4 2 3, .const 5 3, .ld8 6 5,
                     .bin .eq 7 6 0, .bin .and 8 4 7, .halt 8] (data := [0xAA, 0xBB]) },
  -- sha256 / memeq
  { name := "sha256_claim_matches_pub",
    image := prog 128 [.tlen 1 .claim, .const 2 64, .tcopy 2 0 1 .claim, .sha256 0 2 1,
                       .const 3 32, .tcopy 3 0 3 .pub, .memeq 4 0 3 3, .halt 4],
    claim := [0x61, 0x62, 0x63], pub := sha256 [0x61, 0x62, 0x63] },
  { name := "sha256_claim_mismatch_rejects",
    image := prog 128 [.tlen 1 .claim, .const 2 64, .tcopy 2 0 1 .claim, .sha256 0 2 1,
                       .const 3 32, .tcopy 3 0 3 .pub, .memeq 4 0 3 3, .halt 4],
    claim := [0x61, 0x62, 0x64], pub := sha256 [0x61, 0x62, 0x63] },
  { name := "sha256_empty_input",
    image := prog 64 [.const 1 0, .sha256 1 1 1, .const 2 32, .ld8 3 1, .const 4 0xe3,
                      .bin .eq 5 3 4, .halt 5] },
  { name := "sha256_overlapping_dst",
    image := prog 64 [.const 1 0, .const 2 40, .sha256 1 1 2, .ld8 3 1, .halt 3] },
  { name := "sha256_dst_oob_traps",
    image := prog 40 [.const 1 10, .const 2 0, .sha256 1 2 2, .halt 1] },
  { name := "sha256_cost_large",
    image := prog 4096 [.const 1 0, .const 2 4096, .sha256 1 1 2, .const 3 1, .halt 3],
    fuel := 69 },
  { name := "sha256_cost_large_oof",
    image := prog 4096 [.const 1 0, .const 2 4096, .sha256 1 1 2, .const 3 1, .halt 3],
    fuel := 68 },
  { name := "memeq_len0",
    image := prog 0 [.memeq 1 0 0 0, .halt 1] },
  -- outputs
  { name := "out_buffers",
    image := prog 8 [.const 1 0, .const 2 3, .out 0 1 2, .const 3 1, .out 1 3 2, .out 0 1 3,
                     .const 4 1, .halt 4] (data := [1, 2, 3, 4, 5]) },
  -- decoder
  { name := "decode_bad_magic", image := [0x4E, 0x50, 0x41, 0x48, 1, 0,0,0,0, 0,0,0,0, 0,0,0,0] },
  { name := "decode_bad_version", image := [0x4E, 0x50, 0x41, 0x49, 2, 0,0,0,0, 0,0,0,0, 0,0,0,0] },
  { name := "decode_empty_program_traps",
    image := [0x4E, 0x50, 0x41, 0x49, 1, 0,0,0,0, 0,0,0,0, 0,0,0,0] },
  { name := "decode_trailing_byte", image := prog 0 [.halt 0] ++ [0] },
  { name := "decode_truncated", image := (prog 0 [.halt 0]).take 20 },
  { name := "decode_reg16",
    image := magic ++ [version] ++ Bytes.leN 4 0 ++ Bytes.leN 4 0 ++ Bytes.leN 4 1 ++
             [0x00, 16, 0, 0, 0, 0, 0, 0] },
  { name := "decode_nonzero_unused_field",
    image := magic ++ [version] ++ Bytes.leN 4 0 ++ Bytes.leN 4 0 ++ Bytes.leN 4 1 ++
             [0x00, 1, 1, 0, 0, 0, 0, 0] },
  { name := "decode_unknown_opcode",
    image := magic ++ [version] ++ Bytes.leN 4 0 ++ Bytes.leN 4 0 ++ Bytes.leN 4 1 ++
             [0xFF, 0, 0, 0, 0, 0, 0, 0] },
  { name := "decode_bad_tape_id",
    image := magic ++ [version] ++ Bytes.leN 4 0 ++ Bytes.leN 4 0 ++ Bytes.leN 4 1 ++
             [0x20, 1, 0, 0, 3, 0, 0, 0] },
  { name := "decode_out_id_2",
    image := magic ++ [version] ++ Bytes.leN 4 0 ++ Bytes.leN 4 0 ++ Bytes.leN 4 1 ++
             [0x50, 1, 2, 0, 2, 0, 0, 0] },
  { name := "decode_memsize_too_large",
    image := magic ++ [version] ++ Bytes.leN 4 (maxMemSize + 1) ++ Bytes.leN 4 0 ++
             Bytes.leN 4 1 ++ [0x00, 0, 0, 0, 0, 0, 0, 0] },
  { name := "decode_data_longer_than_mem",
    image := magic ++ [version] ++ Bytes.leN 4 1 ++ Bytes.leN 4 2 ++ [7, 7] ++
             Bytes.leN 4 1 ++ [0x00, 0, 0, 0, 0, 0, 0, 0] },
  { name := "decode_max_imm_const",
    image := prog 0 [.const 1 0xFFFFFFFF, .addi 2 1 1, .const 3 32, .const 4 1, .bin .shl 4 4 3,
                     .bin .eq 5 2 4, .halt 5] }
]

/-- Expected result of a case under the reference semantics. -/
inductive Expect where
  | decodeError
  | ran (o : Outcome) (fuelUsed : Nat) (out0 out1 : Bytes)

def expect (c : Case) : Expect :=
  match decode c.image with
  | none => .decodeError
  | some p =>
    let (o, s) := runFull p { pub := c.pub, claim := c.claim, proof := c.proof } c.fuel
    .ran o (c.fuel - s.fuel) s.out0 s.out1

def Expect.summary : Expect → String
  | .decodeError => "decode_error"
  | .ran .accept f .. => s!"accept/{f}"
  | .ran .reject f .. => s!"reject/{f}"
  | .ran .trap f .. => s!"trap/{f}"
  | .ran .outOfFuel f .. => s!"out_of_fuel/{f}"

end ArenaCore.InterpVectors
