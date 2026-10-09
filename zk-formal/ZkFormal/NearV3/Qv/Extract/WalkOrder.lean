import ZkFormal.NearV3.Qv.Extract.WalkBytes

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (tau count)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem gate_eq {r : Nat} (hr : r<tr.height tt) {g a b : Expr}
    (he : eqG g a b∈constraints) (hg : g.eval tr tt r pub=1) :
    a.eval tr tt r pub=b.eval tr tt r pub := by
  have hh := con hL hr he
  simp only [eval_eqG,hg] at hh
  grind

theorem order_start : tr.cell tt 0 main=1 ∧ tr.cell tt 0 tau=0 ∧
    tr.cell tt 0 slot=0 ∧ tr.cell tt 0 lo=0 ∧ tr.cell tt 0 hi=0 := by
  have hr := height_pos hL
  have hm := con hL hr (e:=.mul .isFirst (Dsl.not (c main))) (by simp [constraints])
  have ht := con hL hr (e:=.mul .isFirst (c tau)) (by simp [constraints])
  have hs := con hL hr (e:=.mul .isFirst (c slot)) (by simp [constraints])
  have hl := con hL hr (e:=.mul .isFirst (c lo)) (by simp [constraints])
  have hh := con hL hr (e:=.mul .isFirst (c hi)) (by simp [constraints])
  simp only [eval_mul,eval_isFirst,ite_true,eval_not,eval_c] at hm ht hs hl hh
  grind

theorem order_main_next {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r wl=1) (he : tr.cell tt r wend=0)
    (hm : tr.cell tt r main=1) (hf : tr.cell tt r lastMain=0) :
    tr.cell tt (r+1) main=1 ∧
    tr.cell tt (r+1) slot=tr.cell tt r slot+1 ∧
    tr.cell tt (r+1) lo=1-tr.cell tt r lo*(1-tr.cell tt r hi) ∧
    tr.cell tt (r+1) hi=tr.cell tt r lo+tr.cell tt r hi-tr.cell tt r lo*tr.cell tt r hi ∧
    tr.cell tt (r+1) count=tr.cell tt r count := by
  have hg : advanceMain.eval tr tt r pub=1 := by
    simp only [advanceMain,more,eval_mul3,eval_sub,eval_c,eval_not,hl,he,hm,hf]
    grind
  have h1 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceMain) (a:=n main) (b:=k 1) (by simp [constraints]) hg
  have h2 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceMain) (a:=n slot) (b:=.add (c slot) (k 1)) (by simp [constraints]) hg
  have h3 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceMain) (a:=n lo) (b:=Dsl.not (.mul (c lo) (Dsl.not (c hi)))) (by simp [constraints]) hg
  have h4 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceMain) (a:=n hi) (b:=sub (.add (c lo) (c hi)) group) (by simp [constraints]) hg
  have h5 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceMain) (a:=n count) (b:=c count) (by simp [constraints]) hg
  simpa only [Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,eval_n,eval_c,eval_k,eval_add,eval_not,eval_mul,eval_sub,group,
    Nat.mod_eq_of_lt hr] using And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 h5)))

theorem order_leave_main {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r wl=1) (he : tr.cell tt r wend=0)
    (hf : tr.cell tt r lastMain=1) :
    tr.cell tt (r+1) main=0 ∧ tr.cell tt (r+1) tau=1 := by
  have hg : leaveMain.eval tr tt r pub=1 := by
    simp only [leaveMain,more,eval_mul,eval_sub,eval_c,hl,he,hf]
    grind
  have h1 := gate_eq hL (show r<tr.height tt by omega)
    (g:=leaveMain) (a:=n main) (b:=k 0) (by simp [constraints]) hg
  have h2 := gate_eq hL (show r<tr.height tt by omega)
    (g:=leaveMain) (a:=n tau) (b:=k 1) (by simp [constraints]) hg
  simpa only [Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,eval_n,eval_k,Nat.mod_eq_of_lt hr] using And.intro h1 h2

theorem order_implicit_next {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r wl=1) (he : tr.cell tt r wend=0)
    (hm : tr.cell tt r main=0) :
    tr.cell tt (r+1) main=0 ∧ tr.cell tt (r+1) tau=tr.cell tt r tau+1 := by
  have hg : advanceImplicit.eval tr tt r pub=1 := by
    simp only [advanceImplicit,more,eval_mul,eval_sub,eval_not,eval_c,hl,he,hm]
    grind
  have h1 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceImplicit) (a:=n main) (b:=k 0) (by simp [constraints]) hg
  have h2 := gate_eq hL (show r<tr.height tt by omega)
    (g:=advanceImplicit) (a:=n tau) (b:=.add (c tau) (k 1)) (by simp [constraints]) hg
  simpa only [Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,eval_n,eval_c,eval_k,eval_add,Nat.mod_eq_of_lt hr] using And.intro h1 h2

theorem order_termination {r : Nat} (hr : r<tr.height tt) (he : tr.cell tt r wend=1) :
    tr.cell tt r tau=kPublic.eval tr tt r pub ∧
    (tr.cell tt r main=1 → tr.cell tt r lastMain=1) := by
  have ht := gate_eq hL hr (g:=c wend) (a:=c tau) (b:=kPublic) (by simp [constraints]) he
  have hh := con hL hr (e:=mul3 (c wend) (c main) (Dsl.not (c lastMain))) (by simp [constraints])
  simp only [eval_mul3,eval_c,eval_not,he] at hh
  exact ⟨ht,fun hm => by rw [hm] at hh; grind⟩

/-- The terminal flag is exactly where the walk prefix ends, including a
walk ending on the final physical row. -/
theorem order_end_iff {r : Nat} (hr : r<tr.height tt) (hl : tr.cell tt r wl=1) :
    tr.cell tt r wend=1 ↔ r+1=tr.height tt ∨ tr.cell tt (r+1) walk=0 := by
  have ha := flag_walk hL hr (x:=wl) (by simp) hl
  by_cases hlast : r+1=tr.height tt
  · have hh := con hL hr (e:=mul3 .isLast (c walk) (Dsl.not (c wend))) (by simp [constraints])
    simp only [eval_mul3,eval_isLast,if_pos hlast,eval_c,eval_not,ha] at hh
    constructor
    · intro _; exact Or.inl hlast
    · intro _; grind
  · have hn : r+1<tr.height tt := by omega
    have hz := con hL hr (e:=mul3 .isTransition (c wend) (n walk)) (by simp [constraints])
    have hc := con hL hr (e:=eqG more (n walk) (k 1)) (by simp [constraints])
    simp only [eval_mul3,eval_isTransition,if_neg hlast,eval_c,eval_n,Nat.mod_eq_of_lt hn] at hz
    simp only [more,eval_eqG,eval_sub,eval_c,eval_n,eval_k,Nat.mod_eq_of_lt hn,hl] at hc
    constructor
    · intro he
      rw [he] at hz
      exact Or.inr (by grind)
    · rintro (he | he)
      · exact False.elim (hlast he)
      · rw [he] at hc
        grind

theorem order_implicit_shape {r : Nat} (hr : r<tr.height tt)
    (ha : tr.cell tt r walk=1) (hm : tr.cell tt r main=0) :
    tr.cell tt r lo=0 ∧ tr.cell tt r hi=0 ∧ tr.cell tt r slot=0 := by
  have h1 := con hL hr (e:=mul3 (c walk) (Dsl.not (c main)) (c lo)) (by simp [constraints])
  have h2 := con hL hr (e:=mul3 (c walk) (Dsl.not (c main)) (c hi)) (by simp [constraints])
  have h3 := con hL hr (e:=mul3 (c walk) (Dsl.not (c main)) (c slot)) (by simp [constraints])
  simp only [eval_mul3,eval_c,eval_not,ha,hm] at h1 h2 h3
  grind

end ZkFormal.NearV3.Qv.Extract
