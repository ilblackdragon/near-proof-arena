import M5T1.ShSem6

/-!
# M5T1.ShSem7 — `SE`'s side of the hashes: its bytes, limbs, and the run facts (F-7)

* `se_msg_lt`, `se_dig_lt`: every byte expression of a fixed hash's padded message and of every
  hash's digest is `< 256` on `SE` row 0 (an `RNG`-checked column, `tag_in` (`RNG [tag_in + 1]`), a
  public value (F-6's `pubBytes`), or a constant);
* `limb3_inj`, `ev_limb3`: limbs of bytes determine the bytes;
* `run_fx`, `run_bi`: `fx` is constant along a run and `bi` counts its blocks from `0`;
* `walk`: an active row's hash starts at a first row above it.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq bool_le)

/-! ## Limbs of bytes -/

theorem limb3_inj {a b c a' b' c' : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (ha' : a' < 256)
    (hb' : b' < 256) (hc' : c' < 256) (h : 65536 * a + 256 * b + c = 65536 * a' + 256 * b' + c') :
    a = a' ∧ b = b' ∧ c = c' := by omega

theorem limb2_inj {a b a' b' : Nat} (ha : a < 256) (hb : b < 256) (ha' : a' < 256) (hb' : b' < 256)
    (h : 256 * a + b = 256 * a' + b') : a = a' ∧ b = b' := by omega

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem ev_limb3 {a b c : Expr} (ha : ev tr t r pub a < 256) (hb : ev tr t r pub b < 256)
    (hc : ev tr t r pub c < 256) :
    ev tr t r pub (K 65536 * a + K 256 * b + c) = 65536 * ev tr t r pub a + 256 * ev tr t r pub b + ev tr t r pub c := by
  simp only [evAdd, evMul, evK]
  omega

theorem ev_limb2 {a b : Expr} (ha : ev tr t r pub a < 256) (hb : ev tr t r pub b < 256) :
    ev tr t r pub (K 256 * a + b) = 256 * ev tr t r pub a + ev tr t r pub b := by
  simp only [evAdd, evMul, evK]
  omega
end

theorem map_range_eq {α : Type} {n : Nat} {f g : Nat → α} (h : (List.range n).map f = (List.range n).map g) :
    ∀ j < n, f j = g j := by
  intro j hj
  have := congrArg (fun l => l[j]?) h
  simpa [List.getElem?_map, List.getElem?_range hj] using this

/-! ## `SE`'s bytes -/

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape)
include H hr2

theorem h0pos : 0 < tr.height 0 := by unfold Trace.height; exact Nat.two_pow_pos _

theorem se_rng {e : Expr} (hi : rcv B_RNG .isFirst [e] ∈ Se.table.interactions) : ev tr 0 0 pub e < 256 :=
  rngT H hr2 (t := 0) se_lt (h0pos H hr2) hi rfl

theorem se_col_lt {g : String} {w j : Nat} (hg : (g, w) ∈ Se.byteGroups) (hj : j < w) :
    ev tr 0 0 pub (Se.c g j) < 256 := by
  refine se_rng H hr2 ?_
  show _ ∈ Se.interactions5 ++ Se.interactions7
  refine List.mem_append_right _ ?_
  rw [ix7_eq]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_flatMap.2 ⟨(g, w), hg, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩

theorem se_rsi_lt {j : Nat} (hj : j < 42) : ev tr 0 0 pub (Se.c "rsi" j) < 256 := by
  refine se_rng H hr2 ?_
  show _ ∈ Se.interactions5 ++ Se.interactions7
  refine List.mem_append_left _ ?_
  simp only [Se.interactions5, List.mem_append]
  exact .inl (.inr (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))

theorem se_rso_lt {j : Nat} (hj : j < 42) : ev tr 0 0 pub (Se.c "rso" j) < 256 := by
  refine se_rng H hr2 ?_
  show _ ∈ Se.interactions5 ++ Se.interactions7
  refine List.mem_append_left _ ?_
  simp only [Se.interactions5, List.mem_append]
  exact .inl (.inl (.inr (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))

theorem se_tgi_lt : ev tr 0 0 pub (Se.c "tgi") < 255 := by
  have mem7 : ∀ i ∈ rngPart, i ∈ Se.table.interactions := fun i hi => by
    show _ ∈ Se.interactions5 ++ Se.interactions7
    rw [ix7_eq]; exact List.mem_append_right _ (List.mem_append_left _ hi)
  have h := se_rng H hr2 (e := Se.c "tgi" + 1) (mem7 _ (List.mem_append_left _ (List.mem_cons_self ..)))
  have h' := se_rng H hr2 (e := Se.c "tgi")
    (mem7 _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  simp only [evAdd, evOne] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem cols_lt {g : String} {w : Nat} (hg : (g, w) ∈ Se.byteGroups) :
    ∀ e ∈ Se.cols g w, ev tr 0 0 pub e < 256 := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
  exact se_col_lt H hr2 hg (List.mem_range.1 hj)

theorem rsi_cols_lt : ∀ e ∈ Se.cols "rsi" 42, ev tr 0 0 pub e < 256 := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
  exact se_rsi_lt H hr2 (List.mem_range.1 hj)

/-- **Every byte of a fixed hash's message is a byte on `SE` row 0.** -/
theorem se_msg_lt : ∀ s ∈ Se.hashes, ∀ e ∈ s.msg, ev tr 0 0 pub e < 256 := by
  intro s hs e he
  have bg : ∀ g w, (g, w) ∈ Se.byteGroups → ∀ e ∈ Se.cols g w, ev tr 0 0 pub e < 256 :=
    fun g w hg => cols_lt H hr2 hg
  simp only [Se.hashes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Se.hS0, Se.hS1, Se.hS2, Se.hS3, Se.hS4, Se.hS5, Se.hS6, Se.hS7, Se.hS8, Se.serIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
  · rcases he with ((((rfl | he) | he) | he) | he) | he
    · have := se_tgi_lt H hr2; omega
    · exact bg _ _ (by decide) e he
    · exact bg _ _ (by decide) e he
    · exact bg _ _ (by decide) e he
    · exact bg _ _ (by decide) e he
    · exact rsi_cols_lt H hr2 e he
  · rcases he with (he | he) | he <;> exact bg _ _ (by decide) e he
  · rcases he with (he | he) | he <;> exact bg _ _ (by decide) e he
  · rcases he with he | he <;> exact bg _ _ (by decide) e he
  · rcases he with he | he <;> exact bg _ _ (by decide) e he
  · subst he; simp
  all_goals exact absurd he (by simp)

/-- **Every padded byte of a fixed hash is a byte on `SE` row 0.** -/
theorem se_pad_lt : ∀ s ∈ Se.hashes, ∀ e ∈ Se.padE s.msg, ev tr 0 0 pub e < 256 := by
  intro s hs e he
  simp only [Se.padE, List.mem_append, List.mem_singleton, List.mem_replicate, List.mem_map,
    List.mem_range] at he
  rcases he with ((he | rfl) | ⟨-, rfl⟩) | ⟨i, -, rfl⟩
  · exact se_msg_lt H hr2 s hs e he
  · simp
  · simp
  · simp only [evK]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

/-- **Every digest byte of a hash is a byte on `SE` row 0.** -/
theorem se_dig_lt : ∀ s ∈ Se.hashes, ∀ j < 42, ev tr 0 0 pub (s.dig j) < 256 := by
  intro s hs j hj
  have pb := PubBytes.se_bytes H hr2
  simp only [Se.hashes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show ev tr 0 0 pub (Se.SI.b "stRoot" j) < 256
    simp only [Se.SI, BndLay.Side.b, evPub]
    exact pb _ (by have : BndLay.engF.off "stRoot" = 83 := by decide
                   omega)
  · exact se_rsi_lt H hr2 hj
  · exact se_rso_lt H hr2 hj
  · exact se_col_lt H hr2 (g := "dS") (w := 42) (by decide) hj
  · exact se_col_lt H hr2 (g := "dSo") (w := 42) (by decide) hj
  · exact se_col_lt H hr2 (g := "dShN") (w := 42) (by decide) hj
  · exact se_col_lt H hr2 (g := "dM") (w := 42) (by decide) hj
  · exact se_col_lt H hr2 (g := "dMo") (w := 42) (by decide) hj
  · show ev tr 0 0 pub (Se.SI.b "ctxRoot" j) < 256
    simp only [Se.SI, BndLay.Side.b, evPub]
    exact pb _ (by have : BndLay.engF.off "ctxRoot" = 125 := by decide
                   omega)

end

/-! ## Runs -/

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
include H

theorem sh_height : tr.height 2 ≤ 2 ^ 16 := by
  have h := (H.logBound 2 sh_lt).2
  have h16 : ((Se.fullSe xtape).tables[2]'sh_lt).maxLog = 16 := rfl
  rw [h16] at h
  unfold Trace.height
  exact Nat.pow_le_pow_right (by decide) h

/-- `fx` is constant along a run. -/
theorem run_fx {f ℓ : Nat} (hR : ShRun tr f ℓ) : ∀ k, f + k ≤ ℓ → shC tr (f + k) "fx" = shC tr f "fx"
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := run_fx hR k (by omega)
    obtain ⟨-, hℓ, -, -, -, hin⟩ := hR
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨-, -, -, e, -, -⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    rw [show f + (k + 1) = f + k + 1 by omega, e]
    exact ih

/-- `bi` counts a run's blocks from `0`. -/
theorem run_bi {f ℓ : Nat} (hR : ShRun tr f ℓ) : ∀ k, f + k ≤ ℓ → shC tr (f + k) "bi" = k
  | 0, _ => by
    obtain ⟨-, hℓ, hff, -, -, -⟩ := hR
    exact fst_bi H (by omega) hff
  | k + 1, hk => by
    have ih := run_bi hR k (by omega)
    have hh := sh_height H
    obtain ⟨-, hℓ, -, -, -, hin⟩ := hR
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨-, -, -, -, e, -⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    rw [show f + (k + 1) = f + k + 1 by omega, e, ih]
    exact Nat.mod_eq_of_lt (by omega)

/-- **The backward walk** from an active row to its hash's first row. -/
theorem walk : ∀ i, i < tr.height 2 → shC tr i "act" = 1 →
    ∃ f ≤ i, shC tr f "fst" = 1 ∧ ∀ j, f < j → j ≤ i → shC tr j "act" = 1 ∧ shC tr j "fst" = 0
  | 0, hr, ha => ⟨0, Nat.le_refl _, row0_fst H hr ha, fun j h1 h2 => absurd h2 (by omega)⟩
  | i + 1, hr, ha => by
    have hb := (bools H hr).2.1
    by_cases hf : shC tr (i + 1) "fst" = 1
    · exact ⟨i + 1, Nat.le_refl _, hf, fun j h1 h2 => absurd h2 (by omega)⟩
    · have hf0 : shC tr (i + 1) "fst" = 0 := by omega
      obtain ⟨ha', -, -, -, -, -⟩ := trans_facts H hr ha hf0
      obtain ⟨f, hfi, hff, hin⟩ := walk i (by omega) ha'
      refine ⟨f, by omega, hff, fun j h1 h2 => ?_⟩
      by_cases hj : j = i + 1
      · subst hj; exact ⟨ha, hf0⟩
      · exact hin j h1 (by omega)
end

end M5T1.ShSem
