import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSound
import ZkFormal.NearV3.Extract.ValProof

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Near.Dsl

def recordPrefix (mark : Nat → Bool) : Nat → Nat
  | 0 => 0
  | r+1 => recordPrefix mark r + if mark r then 1 else 0

theorem recordPrefix_le (mark : Nat → Bool) (r : Nat) : recordPrefix mark r≤r := by
  induction r with
  | zero => exact Nat.le_refl _
  | succ r ih => simp only [recordPrefix]; split <;> omega

/-- Local count constraints fix every physical prefix, not just honest renderer
rows. The count is a natural count and cannot wrap below the current height cap. -/
theorem count_prefix {tr : Trace Fp} {t : Nat} {pub : List Fp} (col : Nat) (inc : Expr)
    (mark : Nat → Bool)
    (hc : ∀ r,r<tr.height t → ∀ e∈countConstraints col inc,e.eval tr t r pub=0)
    (hi : ∀ r,r<tr.height t → inc.eval tr t r pub=((if mark r then 1 else 0:Nat):Fp))
    (hh : tr.height t≤2^22) {r : Nat} (hr : r<tr.height t) :
    (tr.cell t r col).toNat=recordPrefix mark r := by
  have hf : ∀ r,r<tr.height t → tr.cell t r col=(recordPrefix mark r:Nat) := by
    intro r hr
    induction r with
    | zero =>
      have he := hc 0 hr (.mul .isFirst (c col)) (by simp [countConstraints])
      change tr.cell t 0 col=0
      simp only [eval_mul,eval_isFirst,eval_c,ite_true] at he
      grind
    | succ r ih =>
      have hr' : r<tr.height t := by omega
      have he := hc r hr' (.mul .isTransition (sub (n col) (.add (c col) inc)))
        (by simp [countConstraints])
      have hn : r+1≠tr.height t := by omega
      simp only [eval_mul,eval_isTransition,if_neg hn,eval_sub,eval_n,eval_add,eval_c,
        Nat.mod_eq_of_lt hr,hi r hr',ih hr'] at he
      simp only [recordPrefix]
      push_cast
      grind
  have hp := recordPrefix_le mark r
  exact ofNat_inj (tr.cell t r col).toNat_lt (by unfold P;omega) (by
    exact (Fp.ofNat_toNat _).trans (hf r hr))

private theorem local_base (T : ZkFormal.Air.Table) (col : Nat) (inc : Expr)
    {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal {T with
      width := T.width+1
      constraints := T.constraints++countConstraints col inc
      interactions := T.interactions.map (withCount (c col))} tr t pub) : TableLocal T tr t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    exact h.constr r hr e (List.mem_append_left _ he)
  · intro r hr i hi b hb
    have hm : b∈(withCount (c col) i).mult := by
      unfold withCount
      split <;> exact hb
    exact h.bits r hr _ (List.mem_map.mpr ⟨i,hi,rfl⟩) b hm

theorem node_local_base {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal nodeTable tr t pub) : TableLocal NodeV3.tableU tr t pub :=
  local_base _ _ _ h

theorem val_local_base {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) : TableLocal ValV3.table tr t pub :=
  local_base _ _ _ h

def recordMark (tr : Trace Fp) (t start dup r : Nat) : Bool :=
  decide (tr.cell t r start=1 ∧ tr.cell t r dup=0)

private theorem increment_mark (tr : Trace Fp) (t start dup r : Nat) (pub : List Fp)
    (hs : tr.cell t r start=0 ∨ tr.cell t r start=1)
    (hd : tr.cell t r dup=0 ∨ tr.cell t r dup=1) :
    (Expr.mul (c start) (not (c dup))).eval tr t r pub=
      ((if recordMark tr t start dup r then 1 else 0:Nat):Fp) := by
  rcases hs with hs|hs <;> rcases hd with hd|hd <;>
    simp [recordMark,eval_mul,eval_c,eval_not,hs,hd] <;> grind

theorem node_count_prefix {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal nodeTable tr t pub) {r : Nat} (hr : r<tr.height t) :
    (tr.cell t r nodeCount).toNat=recordPrefix (recordMark tr t NodeV3.nf NodeV3.dup) r := by
  apply count_prefix (pub := pub) nodeCount nodeIncrement (recordMark tr t NodeV3.nf NodeV3.dup) ?_ ?_ ?_ hr
  · intro q hq e he
    exact h.constr q hq e (List.mem_append_right _ he)
  · intro q hq
    have hb (x : Nat) (hx : x∈NodeV3.boolCols) : tr.cell t q x=0 ∨ tr.cell t q x=1 := by
      have he := (node_local_base h).constr q hq (Dsl.bool (c x)) (by
        unfold NodeV3.tableU NodeV3.table NodeV3.constraints
        simp only [List.mem_append]
        left; left; left; left; left; left
        exact List.mem_map.mpr ⟨x,hx,rfl⟩)
      simp only [eval_bool,eval_c] at he
      exact bool_cases he
    exact increment_mark tr t NodeV3.nf NodeV3.dup q pub (hb NodeV3.nf (by simp [NodeV3.boolCols]))
      (hb NodeV3.dup (by simp [NodeV3.boolCols]))
  · exact Nat.pow_le_pow_right (by decide : 0<2) h.log_le

theorem val_count_prefix {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) {r : Nat} (hr : r<tr.height t) :
    (tr.cell t r valCount).toNat=recordPrefix (recordMark tr t ValV3.vf ValV3.dup) r := by
  apply count_prefix (pub := pub) valCount valIncrement (recordMark tr t ValV3.vf ValV3.dup) ?_ ?_ ?_ hr
  · intro q hq e he
    exact h.constr q hq e (List.mem_append_right _ he)
  · intro q hq
    exact increment_mark tr t ValV3.vf ValV3.dup q pub
      (ValProof.isBool (val_local_base h) hq (by simp [ValProof.bools]))
      (ValProof.isBool (val_local_base h) hq (by simp [ValProof.bools]))
  · exact Nat.pow_le_pow_right (by decide : 0<2) h.log_le

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
