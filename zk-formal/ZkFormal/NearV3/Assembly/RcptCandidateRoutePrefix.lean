import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic
-- Source RoutePrefix.lean SHA256: e4c86ccb819e5581d3a05ba4386b537905335efa428ee89b84dc71d14cc58198.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.RouteRows

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
variable (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
include hL lay

/-- A closed lookup gate stays closed through the final end-marker row. -/
theorem route_zero_after (k : Nat) (hk : k≤y.Lv) (hg : tr.cell tt (lkRow y k) gBd=0) :
    ∀ n,k+n≤y.Lv → tr.cell tt (lkRow y (k+n)) gBd=0 := by
  intro n
  induction n with
  | zero => intro _; simpa using hg
  | succ n ih =>
    intro hn
    have hh := route_no_reopen hL lay (k+n) (by omega) (ih (by omega))
    simpa [Nat.add_assoc] using hh

/-- Selected boundary lookups form an initial prefix. -/
theorem route_prefix {i j : Nat} (hij : i≤j) (hj : j≤y.Lv)
    (hg : tr.cell tt (lkRow y j) gBd=1) : tr.cell tt (lkRow y i) gBd=1 := by
  rcases isBool hL (route_height hL lay i (by omega)) (x:=gBd) (by simp [boolCols]) with hi|hi
  · have hh := route_zero_after hL lay i (by omega) hi (j-i) (by omega)
    rw [show i+(j-i)=j by omega,hg] at hh
    exact False.elim ((by decide : (1:Fp)≠0) hh)
  · exact hi

omit hL lay in
/-- Filtering an initial range by a downward-closed predicate keeps an initial range. -/
theorem filter_range_prefix (p : Nat→Bool) (n : Nat)
    (hp : ∀ i j,i≤j → j<n → p j=true → p i=true) :
    (List.range n).filter p=List.range ((List.range n).filter p).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun i j hij hj hjp => hp i j hij (by omega) hjp)
    by_cases he : p n=true
    · have ha : (List.range n).filter p=List.range n := by
        apply List.filter_eq_self.mpr
        intro i hi
        exact hp i n (by have := List.mem_range.mp hi; omega) (by omega) he
      simp [List.range_succ,List.filter_append,he,ha]
    · simp only [List.range_succ,List.filter_append,List.filter_cons,he,ite_false,List.filter_nil,List.append_nil]
      simpa using hn

omit hL lay in
/-- Position projection commutes with optional emission of indexed records. -/
theorem selected_positions {α : Type} (xs : List Nat) (p : Nat→Bool) (f : Nat→α) :
    ((xs.filterMap fun k => if p k then some (k,f k) else none).map Prod.fst)=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons k ks ih =>
    cases hk : p k <;> simp [hk,ih]

/-- The concrete routing records have consecutive positions beginning at zero. -/
theorem route_positions : (rcptOf tr tt y).rlk.map (·.1)=List.range (rcptOf tr tt y).rlk.length := by
  let p : Nat→Bool := fun k => decide (tr.cell tt (lkRow y k) gBd=1)
  let f := fun k => (cv tr tt (lkRow y k) loB,cv tr tt (lkRow y k) hiB,cv tr tt (lkRow y k) hnB,cv tr tt (lkRow y k) uB)
  have he : (rcptOf tr tt y).rlk.map (·.1)=(List.range (y.Lv+1)).filter p := by
    simpa only [rcptOf,p,f,decide_eq_true_eq] using selected_positions (List.range (y.Lv+1)) p f
  have hp : ∀ i j,i≤j → j<y.Lv+1 → p j=true → p i=true := by
    intro i j hij hj hgj
    simp only [p,decide_eq_true_eq] at hgj ⊢
    exact route_prefix hL lay hij (by omega) hgj
  have hf := filter_range_prefix p (y.Lv+1) hp
  have hl := congrArg List.length he
  simp only [List.length_map] at hl
  rw [he,hf,←hl]

/-- At least one and at most receiver-length-plus-one boundary records are selected. -/
theorem route_length : 1≤(rcptOf tr tt y).rlk.length ∧
    (rcptOf tr tt y).rlk.length≤(rcptOf tr tt y).v.length+1 := by
  have hg := (route_start hL lay).2.2
  have hm : (0,cv tr tt (lkRow y 0) loB,cv tr tt (lkRow y 0) hiB,cv tr tt (lkRow y 0) hnB,cv tr tt (lkRow y 0) uB)∈(rcptOf tr tt y).rlk := by
    apply List.mem_filterMap.mpr
    exact ⟨0,List.mem_range.mpr (by omega),by simp [hg]⟩
  constructor
  · cases he : (rcptOf tr tt y).rlk with
    | nil => rw [he] at hm; simp at hm
    | cons a as => simp
  · have hh := List.length_filterMap_le (fun k => if tr.cell tt (lkRow y k) gBd=1 then
        some (k,cv tr tt (lkRow y k) loB,cv tr tt (lkRow y k) hiB,cv tr tt (lkRow y k) hnB,cv tr tt (lkRow y k) uB) else none)
        (List.range (y.Lv+1))
    simpa only [rcptOf,colAt_len,List.length_range] using hh

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
