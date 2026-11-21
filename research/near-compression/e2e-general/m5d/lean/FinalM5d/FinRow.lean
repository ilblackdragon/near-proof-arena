import FinalM5d.HeaderLink
import FinalM5d.Final
import ZkFormal.Sha.Sound.Bridge

/-!
# FinalM5d.FinRow — the `FIN` table's constraints give `RowOK`, hence `headerOk`

On any row of any trace on which the exported `Fin.table`'s constraints vanish over BabyBear and
`act = 1`, with the statement-stream cells bytes (`HbBytes`: they are hashed by `S384`, whose
lookups range-check them — a premise here), the cells read as naturals (`ev`, lane B's / the SHA
table's bridge) satisfy `RowOK` (`rowOK_of_constraints`), and therefore (`fin_headerOk`) the
spec's decoder accepts the chunk-inner window of the row and `headerOk` holds against the outputs
`outputsOf` built from the row's `FinIn` cells, received roots and the public body length.
-/

namespace FinalM5d.FinRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound NearSpec NearSpecV3 NearSpecV3.E2E
open FinalM5d FinalM5d.Link

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "PR" => 2013265921

theorem ci_off : CI_OFF = 114 := by decide

theorem ev_hadd (a b : Expr) : ev tr t r pub (a + b) = (ev tr t r pub a + ev tr t r pub b) % PR :=
  ev_add a b
theorem ev_hmul (a b : Expr) : ev tr t r pub (a * b) = ev tr t r pub a * ev tr t r pub b % PR :=
  ev_mul a b
theorem ev_K (v : Nat) : ev tr t r pub (K v) = v % PR := ev_const v

theorem mem_rng {n : Nat} {f : Nat → Expr} {j : Nat} (hj : j < n) : Fin.act * f j ∈ Fin.rng n f :=
  List.mem_map.2 ⟨f j, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, rfl⟩

theorem mem_hdr {e : Expr} (h : e ∈ Fin.headerEqs) : e ∈ Fin.constraints := by
  unfold Fin.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

section
variable (hc : ∀ e ∈ Fin.constraints, e.eval tr t r pub = 0) (hact : ev tr t r pub Fin.act = 1)
include hc hact

theorem gate {x : Expr} (hm : Fin.act * x ∈ Fin.constraints) : ev tr t r pub x = 0 := by
  have h0 := ev_of_eval (hc _ hm)
  rcases ev_mul_eq_zero h0 with h | h
  · omega
  · exact h

theorem gate_eq {a b : Expr} (hm : Fin.act * (a - b) ∈ Fin.constraints) :
    ev tr t r pub a = ev tr t r pub b :=
  ev_sub_eq (gate hc hact hm)

/-- A family `rng n (fun j => a j - b j)` of `headerEqs`. -/
theorem fam_eq {n : Nat} {a b : Nat → Expr}
    (hf : Fin.rng n (fun j => a j - b j) ⊆ Fin.headerEqs) {j : Nat} (hj : j < n) :
    ev tr t r pub (a j) = ev tr t r pub (b j) :=
  gate_eq hc hact (mem_hdr (hf (mem_rng (f := fun j => a j - b j) hj)))

theorem fam_zero {n : Nat} {a : Nat → Expr} (hf : Fin.rng n a ⊆ Fin.headerEqs) {j : Nat} (hj : j < n) :
    ev tr t r pub (a j) = 0 :=
  gate hc hact (mem_hdr (hf (mem_rng hj)))

end

/-- The cells as naturals. -/
def hbN (tr : Trace Fp) (t r : Nat) (pub : List Fp) (k : Nat) : Nat := ev tr t r pub (Fin.hb k)
def fiN (tr : Trace Fp) (t r : Nat) (pub : List Fp) (j : Nat) : Nat := ev tr t r pub (Fin.fi j)
def colN (s : String) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (j : Nat) : Nat :=
  ev tr t r pub (Fin.T.c s j)

theorem ci_hb (k : Nat) : Fin.ci k = Fin.hb (114 + k) := by
  simp only [Fin.ci, ci_off]

/-- The statement-stream cells are bytes (a premise: `S384`'s lookups range-check them). -/
def HbBytes (tr : Trace Fp) (t r : Nat) (pub : List Fp) : Prop :=
  ∀ k, k < 424 → hbN tr t r pub k < 256

macro "sub_fam" : tactic =>
  `(tactic| (intro e he; unfold Fin.headerEqs; simp only [List.mem_append]; simp_all))

theorem rowOK_of_constraints (hc : ∀ e ∈ Fin.constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub Fin.act = 1) (hb : HbBytes tr t r pub) :
    RowOK (hbN tr t r pub) (fiN tr t r pub) (colN "ro" tr t r pub) (colN "rs" tr t r pub)
      (colN "rsh" tr t r pub) (ev tr t r pub (.pub PV_N)) := by
  have E (a b : Nat → Expr) (n : Nat) (hf : Fin.rng n (fun j => a j - b j) ⊆ Fin.headerEqs) :=
    fun j (hj : j < n) => fam_eq hc hact hf hj
  have Z (a : Nat → Expr) (n : Nat) (hf : Fin.rng n a ⊆ Fin.headerEqs) :=
    fun j (hj : j < n) => fam_zero hc hact hf hj
  have pe : Fin.eqPsr ⊆ Fin.headerEqs := by sub_fam
  have po : Fin.eqPor ⊆ Fin.headerEqs := by sub_fam
  have pm : Fin.eqEmr ⊆ Fin.headerEqs := by sub_fam
  have pl0 : Fin.eqEl0 ⊆ Fin.headerEqs := by sub_fam
  have pgu : Fin.eqGu ⊆ Fin.headerEqs := by sub_fam
  have pgl : Fin.eqGl ⊆ Fin.headerEqs := by sub_fam
  have pbb : Fin.eqBb ⊆ Fin.headerEqs := by sub_fam
  have por' : Fin.eqOrr ⊆ Fin.headerEqs := by sub_fam
  have ptx : Fin.eqTxr ⊆ Fin.headerEqs := by sub_fam
  have ppr : Fin.eqProps ⊆ Fin.headerEqs := by sub_fam
  have ppr0 : Fin.eqProps0 ⊆ Fin.headerEqs := by sub_fam
  have pcg : Fin.eqCong ⊆ Fin.headerEqs := by sub_fam
  have pbw : Fin.eqBw ⊆ Fin.headerEqs := by sub_fam
  have pbw1 : Fin.eqBw1 ⊆ Fin.headerEqs := by sub_fam
  have pel : Fin.eqEl ⊆ Fin.headerEqs := by sub_fam
  have pcg0 : Fin.eqCong0 ⊆ Fin.headerEqs := by sub_fam
  have pbw0 : Fin.eqBw0 ⊆ Fin.headerEqs := by sub_fam
  have psp : Fin.eqSplit ⊆ Fin.headerEqs := by sub_fam
  have pfx : Fin.eqFixed ⊆ Fin.headerEqs := by sub_fam
  have G (x : Expr) (hx : Fin.act * x ∈ Fin.headerEqs) := gate hc hact (mem_hdr hx)
  have GE (a b : Expr) (hx : Fin.act * (a - b) ∈ Fin.headerEqs) := gate_eq hc hact (mem_hdr hx)
  have hcik (k : Nat) : ev tr t r pub (Fin.ci k) = hbN tr t r pub (114 + k) := by
    rw [ci_hb]; rfl
  refine
    { tag := ?_, psr := ?_, por := ?_, emr := ?_, el := ?_, el0 := ?_, gu := ?_, gl := ?_, bb := ?_,
      orr := ?_, txr := ?_, props := ?_, cong := ?_, congTag := ?_, bw := ?_, split := ?_,
      bytes := hb }
  · -- the header tag is a fixed stream byte
    have hf : (CI_OFF, 4) ∈ streamFixed := by decide
    have hm : Fin.act * (Fin.hb CI_OFF - K 4) ∈ Fin.eqFixed :=
      List.mem_map.2 ⟨(CI_OFF, 4), hf, rfl⟩
    have := GE _ _ (pfx hm)
    rw [ci_off] at this
    simpa [hbN, K] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_PSR + j)) (fun j => Fin.fi (FI_ROOT + j)) 32 pe j hj
    rw [hcik] at this; simpa [H_PSR, FI_ROOT, fiN, show 114 + (33 + j) = 147 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_POR + j)) (fun j => Fin.T.c "ro" j) 32 po j hj
    rw [hcik] at this; simpa [H_POR, colN, show 114 + (65 + j) = 179 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_EMR + j)) (fun j => Fin.T.c "rs" j) 32 pm j hj
    rw [hcik] at this; simpa [H_EMR, colN, show 114 + (97 + j) = 211 + j by omega] using this
  · have := GE _ _ (pel (List.mem_singleton.2 rfl))
    have b0 := hb 243 (by omega); have b1 := hb 244 (by omega); have b2 := hb 245 (by omega)
    simp only [ev_hadd, ev_hmul, ev_K, hcik, H_EL, Nat.reduceAdd, Nat.reduceMod] at this
    simp only [hbN] at b0 b1 b2 this ⊢
    change ev tr t r pub (Expr.pub PV_N) = _ at this
    omega
  · intro j hj
    have := Z (fun j => Fin.ci (H_EL + 3 + j)) 5 pl0 j hj
    rw [hcik] at this; simpa [H_EL, show 114 + (129 + 3 + j) = 246 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_GU + j)) (fun j => Fin.fi (FI_GAS + j)) 8 pgu j hj
    rw [hcik] at this; simpa [H_GU, FI_GAS, fiN, show 114 + (153 + j) = 267 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_GL + j)) (fun j => Fin.fi (FI_GL + j)) 8 pgl j hj
    rw [hcik] at this; simpa [H_GL, FI_GL, fiN, show 114 + (161 + j) = 275 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_BB + j)) (fun j => Fin.fi (FI_BAL + j)) 16 pbb j hj
    rw [hcik] at this; simpa [H_BB, FI_BAL, fiN, show 114 + (169 + j) = 283 + j by omega] using this
  · intro j hj
    have := E (fun j => Fin.ci (H_ORR + j)) (fun j => Fin.T.c "rsh" j) 32 por' j hj
    rw [hcik] at this; simpa [H_ORR, colN, show 114 + (185 + j) = 299 + j by omega] using this
  · intro j hj
    have := Z (fun j => Fin.ci (H_TXR + j)) 32 ptx j hj
    rw [hcik] at this; simpa [H_TXR, show 114 + (217 + j) = 331 + j by omega] using this
  · intro j hj
    have h1 := E (fun j => Fin.ci (H_PROPS + j)) (fun j => Fin.fi (FI_PROPS + j)) 4 ppr j hj
    have h2 := Z (fun j => Fin.fi (FI_PROPS + j)) 4 ppr0 j hj
    rw [hcik, h2] at h1; simpa [H_PROPS, show 114 + (249 + j) = 363 + j by omega] using h1
  · intro j hj
    have := E (fun j => Fin.ci (H_CONG + j)) (fun j => Fin.fi (FI_CONG + j)) 43 pcg j hj
    rw [hcik] at this; simpa [H_CONG, FI_CONG, fiN, show 114 + (253 + j) = 367 + j by omega] using this
  · have := G _ (pcg0 (List.mem_singleton.2 rfl))
    simpa [fiN, FI_CONG] using this
  · intro j hj
    rcases j with _ | j
    · have := G _ (pbw0 (List.mem_singleton.2 rfl))
      rw [hcik] at this; simpa [H_BW] using this
    · have h1 := E (fun j => Fin.ci (H_BW + 1 + j)) (fun j => Fin.fi (FI_BW + j)) 4 pbw j (by omega)
      have h2 := Z (fun j => Fin.fi (FI_BW + j)) 4 pbw1 j (by omega)
      rw [hcik, h2] at h1; simpa [H_BW, show 114 + (296 + 1 + j) = 410 + (j + 1) by omega] using h1
  · have h1 := GE (Fin.ci H_SPLIT) (Fin.fi FI_SPLIT) (psp (by simp [Fin.eqSplit]))
    have h2 := G (Fin.fi FI_SPLIT) (psp (by simp [Fin.eqSplit]))
    rw [hcik, h2] at h1; simpa [H_SPLIT] using h1

/-- **`FIN`'s constraints give `FinalOut`**: the decoded chunk inner of the row's statement window
and the row's outputs satisfy `headerOk`. -/
theorem fin_headerOk (hc : ∀ e ∈ Fin.constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub Fin.act = 1) (hb : HbBytes tr t r pub) :
    decodeChunkInner (win (hbN tr t r pub)) = .ok (hdrOf (hbN tr t r pub)) ∧
      headerOk (hdrOf (hbN tr t r pub))
        (outputsOf (fiN tr t r pub) (colN "ro" tr t r pub) (colN "rs" tr t r pub)
          (colN "rsh" tr t r pub) (ev tr t r pub (.pub PV_N))) = true :=
  row_headerOk (rowOK_of_constraints hc hact hb)

end FinalM5d.FinRow
