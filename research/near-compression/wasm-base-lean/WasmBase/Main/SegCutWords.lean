import WasmBase.Main.SegShaCut
import WasmBase.Main.SegLink

/-!
# WasmBase.Main.SegCutWords — CUTO's hashed words are `cutWords (cutoList tr)` (E2E M4b, S3)

Closes the open item of `Main/SegShaCut.lean`: the words `Ws` whose SHA-384 is the public `ctx_out`
(`cut_stream_digest`, sub-lane S2) are exactly `cutWords (cutoList tr)`, so

**`ctx_out_sha`**: under `HoldsX`, the chip hypothesis `ChipIf compressW …` and the limb bound
`CutoHiLimbs`, the public `ctx_out` limbs are `limbsF d` with `wbytes d = cutDigest (cutoList tr)` —
the form `seg_sound_cut_link` takes (`hsha`).

* `cuto_streamW_act`: an active row's 8 block words are `msgWords` of its 7 fields (`lo < 2^16`,
  `hi < 2^14`: `cuto_halves`; the mark on word 0);
* `cuto_streamW_filler`: the filler row (`kD = 1`, `act = 0`) hashes 8 zero words — this needs the
  filler fix (`Cut.rowWords` gates the limbs by `act`, `cuto_filler_fixed`);
* `cuto_ws`: with `2N` data rows, the active rows are the first `2N` or `2N − 1` (an inactive data
  row is followed by padding, `cuto_filler_next`), so the stream words are `cutWords (cutoList tr)`;
* `wordBytes_eq_beN`, `cutBytes_eq`: `cutBytes = wbytes ∘ cutWords`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg SegSha
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem wordBytes_eq_beN (w : Nat) : wordBytes w = ArenaCore.Bytes.beN 8 w := by
  simp only [wordBytes, ArenaCore.Bytes.beN, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, Nat.div_div_eq_div_mul]
  simp

theorem cutBytes_eq (L : List (List Nat)) : cutBytes L = wbytes (cutWords L) := by
  simp only [cutBytes, wbytes]
  congr 1; funext w; exact wordBytes_eq_beN w

theorem flatMap_congrS {α β : Type} {f g : α → List β} : ∀ l : List α, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congrS l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem kc_rowNat (tr : Trace) (t r i : Nat) : kc tr t r i = ((rowNat tr t r i : Nat) : F) := by
  simp only [kc, rowNat, Fp.cast_toNat]

theorem cutWord_split {lo hi mk : Nat} (hlo : lo < 2 ^ 16) :
    cutWord (lo + 65536 * hi) mk = lo + 2 ^ 21 * hi + 2 ^ 42 * mk := by
  unfold cutWord; omega

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **An active CUTO row hashes `msgWords` of its fields.** -/
theorem cuto_streamW_act (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    streamW tr pub 31 Cut.Out.cols r = msgWords (cutoRow tr r) := by
  have hP := P_val
  obtain ⟨-, -, -, -, -, hs, -, -⟩ := cuto_bits H hr
  have hD := (cuto_bits H hr).2.2.2.2.2.2.1 ha
  have hP0 : rowNat tr 31 r 3 = 0 := by omega
  have hw : ∀ w, w < 7 → decW (bwF tr pub 31 Cut.Out.cols r w) = cutWord (cutoF tr r w) (if w = 0 then 1 else 0) := by
    intro w hw7
    obtain ⟨hlo, hhi⟩ := cuto_halves H hl hr ha hw7
    rw [bwF_eq (Or.inr rfl) r (by omega), if_pos hw7]
    simp only [decW, kc_rowNat, ha, hP0, List.getD_cons_zero, List.getD_cons_succ]
    unfold cutoF
    rw [cutWord_split hlo]
    have e1 : (((1 : Nat) : F) * ((rowNat tr 31 r (5 + w) : Nat) : F)).toNat = rowNat tr 31 r (5 + w) := by
      rw [show ((1 : Nat) : F) = 1 from rfl, Lean.Grind.Semiring.one_mul, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]
    have e2 : (((1 : Nat) : F) * ((rowNat tr 31 r (12 + w) : Nat) : F)).toNat = rowNat tr 31 r (12 + w) := by
      rw [show ((1 : Nat) : F) = 1 from rfl, Lean.Grind.Semiring.one_mul, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]
    rw [e1, e2]
    by_cases h0 : w = 0
    · subst h0; simp only [if_true]
      have : (((1 : Nat) : F) + ((0 : Nat) : F) * (1 - ((rowNat tr 31 r 1 : Nat) : F)) * ((2 ^ 21 : Nat) : F)).toNat = 1 := by
        have z : ((0 : Nat) : F) = 0 := rfl
        rw [z]; simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]; rfl
      rw [this]
    · simp only [h0, if_false]; rfl
  have h7 : decW (bwF tr pub 31 Cut.Out.cols r 7) = 0 := by
    rw [bwF_eq (Or.inr rfl) r (by omega), if_neg (by omega)]
    simp only [decW, kc_rowNat, hP0, List.getD_cons_zero, List.getD_cons_succ]
    have z : ((0 : Nat) : F) = 0 := rfl
    simp only [z, Lean.Grind.Semiring.zero_mul]; rfl
  simp only [streamW, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, cutoRow_eq, msgWords, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega),
    hw 3 (by omega), hw 4 (by omega), hw 5 (by omega), hw 6 (by omega), h7]
  rfl

/-- **The filler row hashes zero words** (`kD = 1`, `act = 0`; needs the `act`-gated `rowWords`). -/
theorem cuto_streamW_filler {r : Nat} (hr : r < tr.height 31) (hd : rowNat tr 31 r 2 = 1)
    (ha : rowNat tr 31 r 0 = 0) : streamW tr pub 31 Cut.Out.cols r = List.replicate 8 0 := by
  obtain ⟨-, -, -, -, -, hs, -, -⟩ := cuto_bits H hr
  have hP0 : rowNat tr 31 r 3 = 0 := by omega
  have z : ((0 : Nat) : F) = 0 := rfl
  have hw : ∀ w, w < 8 → decW (bwF tr pub 31 Cut.Out.cols r w) = 0 := by
    intro w hw8
    rw [bwF_eq (Or.inr rfl) r hw8]
    split
    · simp only [decW, kc_rowNat, ha, hP0, z, List.getD_cons_zero, List.getD_cons_succ, Lean.Grind.Semiring.zero_mul,
        Lean.Grind.Semiring.add_zero]
      split <;> rfl
    · simp only [decW, kc_rowNat, hP0, z, List.getD_cons_zero, List.getD_cons_succ, Lean.Grind.Semiring.zero_mul]; rfl
  simp only [streamW, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega),
    hw 4 (by omega), hw 5 (by omega), hw 6 (by omega), hw 7 (by omega)]
  rfl

/-- An inactive data row is followed by the padding group. -/
theorem cuto_filler_next {r : Nat} (hr : r + 1 < tr.height 31) (hd : rowNat tr 31 r 2 = 1)
    (ha : rowNat tr 31 r 0 = 0) : rowNat tr 31 (r + 1) 3 = 1 := by
  obtain ⟨i0, -, i2, i3, -⟩ := cuto_ix
  have e := cuto_constr H (r := r) (by omega) (e := Expr.trans * Cut.c Cut.Out.cols "kD" * (1 - Cut.c Cut.Out.cols "act") *
    (1 - Cut.n Cut.Out.cols "kP")) (cuto_stream_mem (by simp [Cut.streamConstraints]))
  simp only [Cut.c, Cut.n, i0, i2, i3, v, nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_nxt,
    Expr.eval_ofNat', row_cur, row_nxt tr pub hr, row_trans tr pub hr, hd, ha] at e
  have g : (1 : F) - ((rowNat tr 31 (r + 1) 3 : Nat) : F) = 0 := by
    have o : ((1 : Nat) : F) = 1 := rfl
    have z : ((0 : Nat) : F) = 0 := rfl
    rw [o, z] at e; grind
  obtain ⟨-, -, -, b3, -⟩ := cuto_bits H (r := r + 1) hr
  rcases (by omega : rowNat tr 31 (r + 1) 3 = 0 ∨ rowNat tr 31 (r + 1) 3 = 1) with h | h
  · rw [h] at g; exact absurd g (by decide)
  · exact h

omit H in
theorem range_filter_lt' : ∀ h M, M ≤ h → (List.range h).filter (fun r => decide (r < M)) = List.range M
  | 0, M, hM => by simp at hM; subst hM; rfl
  | h + 1, M, hM => by
    rcases Nat.lt_or_eq_of_le hM with hlt | rfl
    · rw [List.range_succ, List.filter_append, range_filter_lt' h M (by omega)]
      simp [show ¬ h < M by omega]
    · rw [List.filter_eq_self.mpr (fun a ha => by simpa using List.mem_range.mp ha)]

omit H in
/-- `cutoList` is the fields of the first `M` rows when exactly those are active. -/
theorem cutoList_prefix {M : Nat} (hM : M ≤ tr.height 31)
    (hact : ∀ r, r < tr.height 31 → (rowNat tr 31 r 0 = 1 ↔ r < M)) :
    cutoList tr = (List.range M).map (cutoRow tr) := by
  unfold cutoList
  congr 1
  rw [← range_filter_lt' _ M hM]
  exact List.filter_congr fun r hr => by
    have := hact r (List.mem_range.mp hr); simp [this]

/-- **The stream words are `cutWords (cutoList tr)`.** -/
theorem cuto_ws (hl : CutoHiLimbs tr) {N : Nat} (hN : 2 * N + 2 ≤ tr.height 31)
    (hd : ∀ r, r < 2 * N → kc tr 31 r 2 = 1) (hp : kc tr 31 (2 * N) 3 = 1) :
    (List.range (2 * N)).flatMap (streamW tr pub 31 Cut.Out.cols) = cutWords (cutoList tr) := by
  have hd' : ∀ r, r < 2 * N → rowNat tr 31 r 2 = 1 := fun r hr => by
    have := hd r hr; rw [kc_rowNat] at this; exact natEq (R := 1) this (rowNat_lt _ _ _ _) (by decide)
  have hp' : rowNat tr 31 (2 * N) 3 = 1 := by
    rw [kc_rowNat] at hp; exact natEq (R := 1) hp (rowNat_lt _ _ _ _) (by decide)
  -- rows from `2N` on are inactive
  have hlate : ∀ r, r < tr.height 31 → 2 * N ≤ r → rowNat tr 31 r 0 = 0 := by
    intro r hr hle
    refine Classical.byContradiction fun hne => ?_
    have hb := (cuto_bits H hr).1
    have ha : rowNat tr 31 r 0 = 1 := by omega
    have h2N := cuto_prefix_le H hr hle ha
    obtain ⟨-, -, -, -, -, hs, hact, -⟩ := cuto_bits H (r := 2 * N) (by omega)
    have := hact h2N; omega
  -- an inactive data row is the last one
  have hfill : ∀ r, r < 2 * N → rowNat tr 31 r 0 = 0 → r + 1 = 2 * N := by
    intro r hr ha
    refine Classical.byContradiction fun hne => ?_
    have := cuto_filler_next H (r := r) (by omega) (hd' r hr) ha
    have h2 := hd' (r + 1) (by omega)
    obtain ⟨-, -, -, -, -, hs, -⟩ := cuto_bits H (r := r + 1) (by omega)
    omega
  have hbit : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 0 ∨ rowNat tr 31 r 0 = 1 := fun r hr => by
    have := (cuto_bits H hr).1; omega
  by_cases hlast : N = 0 ∨ rowNat tr 31 (2 * N - 1) 0 = 1
  · -- all `2N` data rows active
    have hact : ∀ r, r < tr.height 31 → (rowNat tr 31 r 0 = 1 ↔ r < 2 * N) := by
      intro r hr
      constructor
      · intro ha; refine Classical.byContradiction fun h => ?_; have := hlate r hr (by omega); omega
      · intro hlt
        rcases hlast with h0 | h1
        · omega
        · exact cuto_prefix_le H (b := 2 * N - 1) (by omega) (by omega) h1
    rw [cutoList_prefix (by omega) hact, cutWords]
    have hev : ((List.range (2 * N)).map (cutoRow tr)).length % 2 = 0 := by simp
    simp only [hev, show ¬ (0 = 1) by omega, if_false, List.append_nil, List.flatMap_map]
    refine flatMap_congrS _ fun r hr => ?_
    have hr' := List.mem_range.mp hr
    exact cuto_streamW_act H hl (by omega) ((hact r (by omega)).mpr hr')
  · -- the last data row is the filler
    simp only [not_or] at hlast
    obtain ⟨hN0, hl0⟩ := hlast
    have hl0' : rowNat tr 31 (2 * N - 1) 0 = 0 := by have := hbit (2 * N - 1) (by omega); omega
    have hact : ∀ r, r < tr.height 31 → (rowNat tr 31 r 0 = 1 ↔ r < 2 * N - 1) := by
      intro r hr
      constructor
      · intro ha
        refine Classical.byContradiction fun h => ?_
        by_cases h2 : r < 2 * N
        · have : r = 2 * N - 1 := by omega
          subst this; omega
        · have := hlate r hr (by omega); omega
      · intro hlt
        rcases hbit r hr with h0 | h1
        · have := hfill r (by omega) h0; omega
        · exact h1
    rw [cutoList_prefix (by omega) hact, cutWords]
    have hodd : ((List.range (2 * N - 1)).map (cutoRow tr)).length % 2 = 1 := by simp; omega
    simp only [hodd, if_true, List.flatMap_map]
    rw [show 2 * N = (2 * N - 1) + 1 by omega, List.range_succ, List.flatMap_append,
      show 2 * N - 1 + 1 - 1 = 2 * N - 1 by omega]
    congr 1
    · refine flatMap_congrS _ fun r hr => ?_
      have hr' := List.mem_range.mp hr
      exact cuto_streamW_act H hl (by omega) ((hact r (by omega)).mpr hr')
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact cuto_streamW_filler H (by omega) (hd' _ (by omega)) hl0'

/-- **`ctx_out` is the SHA-384 of CUTO's hashed list.**  The public `ctx_out` limbs are those of a
digest `d` with `wbytes d = cutDigest (cutoList tr)` (S2's `cut_stream_digest` + `cuto_ws`). -/
theorem ctx_out_sha {chip : List StateM5a.Sha512If.IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    (hl : CutoHiLimbs tr) :
    ∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = limbsF d ∧
      wbytes d = cutDigest (cutoList tr) := by
  obtain ⟨N, hN, hd, hp, -, d, h6, hW, hpub, hsha⟩ :=
    cut_stream_digest (t := 31) (cs := Cut.Out.cols) (base := pubCtxOut) H hC (Or.inr ⟨rfl, rfl, rfl⟩)
  refine ⟨d, h6, hW, hpub, ?_⟩
  rw [hsha, cuto_ws H hl hN hd hp, cutDigest, cutBytes_eq]

end

#print axioms wordBytes_eq_beN
#print axioms cuto_streamW_act
#print axioms cuto_streamW_filler
#print axioms cuto_ws
#print axioms ctx_out_sha

end WasmBase
