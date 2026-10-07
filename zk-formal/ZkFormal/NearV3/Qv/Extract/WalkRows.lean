import ZkFormal.Near.Extract.Segments
import ZkFormal.NearV3.Qv.Candidates.CombinedTable

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}

def isOne (tr : Trace Fp) (tt x r : Nat) : Bool := decide (tr.cell tt r x = 1)
def walkBools : List Nat := [walk,lo,hi,wf,wl,wend,absent,groupByte,countRead,main,lastMain,present]

variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r<tr.height tt) {e : Expr} (he : e ∈ constraints) :
    e.eval tr tt r pub=0 := hL.constr r hr e he

theorem isBool {r x : Nat} (hr : r<tr.height tt) (hx : x∈walkBools) :
    tr.cell tt r x=0 ∨ tr.cell tt r x=1 := by
  have he : Dsl.bool (c x) ∈ constraints := by
    have hm := List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx
    unfold walkBools at hm
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have h := con hL hr he
  simp only [eval_bool,eval_c] at h
  exact bool_cases h

theorem zero_of_false {r x : Nat} (hr : r<tr.height tt) (hx : x∈walkBools)
    (h : isOne tr tt x r=false) : tr.cell tt r x=0 := by
  rcases isBool hL hr hx with hz | ho
  · exact hz
  · simp [isOne,ho] at h

theorem flag_walk {r x : Nat} (hr : r<tr.height tt)
    (hx : x∈[wf,wl,wend,groupByte,countRead,main,lastMain,present])
    (h : tr.cell tt r x=1) : tr.cell tt r walk=1 := by
  have he : Expr.mul (c x) (Dsl.not (c walk)) ∈ constraints := by
    have hm := List.mem_map_of_mem (f := fun x => Expr.mul (c x) (Dsl.not (c walk))) hx
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have hh := con hL hr he
  simp only [eval_mul,eval_c,eval_not,h] at hh
  grind

theorem end_last {r : Nat} (hr : r<tr.height tt) (h : tr.cell tt r wend=1) :
    tr.cell tt r wl=1 := by
  have hh := con hL hr (e := .mul (c wend) (Dsl.not (c wl))) (by simp [constraints])
  simp only [eval_mul,eval_c,eval_not,h] at hh
  grind

theorem walk_cont {r : Nat} (hr : r+1<tr.height tt)
    (ha : tr.cell tt r walk=1) (hl : tr.cell tt r wl=0) :
    tr.cell tt (r+1) walk=1 ∧ tr.cell tt (r+1) wf=0 := by
  have h1 := con hL (r:=r) (by omega) (e := eqG inside (n walk) (k 1)) (by simp [constraints])
  have h2 := con hL (r:=r) (by omega) (e := .mul inside (n wf)) (by simp [constraints])
  simp only [inside,eval_eqG,eval_mul,eval_c,eval_not,eval_n,eval_k,ha,hl,
    Nat.mod_eq_of_lt hr] at h1 h2
  constructor <;> grind

theorem walk_next {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r wl=1) (hn : tr.cell tt (r+1) walk=1) :
    tr.cell tt (r+1) wf=1 := by
  have hs := con hL (r:=r) (by omega) (e := mul3 .isTransition (c wend) (n walk)) (by simp [constraints])
  have hh := con hL (r:=r) (by omega) (e := eqG more (n wf) (k 1)) (by simp [constraints])
  simp only [eval_mul3,eval_isTransition,if_neg (show ¬r+1=tr.height tt by omega),
    eval_c,eval_n,Nat.mod_eq_of_lt hr,hn] at hs
  have he : tr.cell tt r wend=0 := by grind
  simp only [more,eval_eqG,eval_sub,eval_c,eval_n,eval_k,Nat.mod_eq_of_lt hr,hl,he] at hh
  grind

theorem walk_pad {r : Nat} (hr : r+1<tr.height tt) (ha : tr.cell tt r walk=0) :
    tr.cell tt (r+1) walk=0 := by
  have hh := con hL (r:=r) (by omega) (e := mul3 .isTransition (Dsl.not (c walk)) (n walk)) (by simp [constraints])
  simp only [eval_mul3,eval_isTransition,if_neg (show ¬r+1=tr.height tt by omega),
    eval_not,eval_c,eval_n,Nat.mod_eq_of_lt hr,ha] at hh
  grind

theorem walk_start (hH : 0<tr.height tt) : tr.cell tt 0 wf=1 := by
  have hh := con hL hH (e := .mul .isFirst (Dsl.not (c wf))) (by simp [constraints])
  simp only [eval_mul,eval_isFirst,if_pos rfl,eval_not,eval_c] at hh
  grind

theorem walk_stop (hH : 0<tr.height tt) (ha : tr.cell tt (tr.height tt-1) walk=1) :
    tr.cell tt (tr.height tt-1) wl=1 := by
  have hh := con hL (show tr.height tt-1<tr.height tt by omega)
    (e := mul3 .isLast (c walk) (Dsl.not (c wend))) (by simp [constraints])
  simp only [eval_mul3,eval_isLast,if_pos (show tr.height tt-1+1=tr.height tt by omega),
    eval_c,eval_not,ha] at hh
  exact end_last hL (by omega) (by grind)

/-- Arbitrary locally accepted traces split into a prefix of complete queue
walk segments. No generated-trace or canonical-row premise is used. -/
theorem walk_segFacts : SegFacts (tr.height tt)
    (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) := by
  constructor
  · intro r hr hf
    simp only [isOne,decide_eq_true_eq] at hf ⊢
    exact flag_walk hL hr (by simp) hf
  · intro r hr hl
    simp only [isOne,decide_eq_true_eq] at hl ⊢
    exact flag_walk hL hr (by simp) hl
  · intro r hr ha hl
    have hz := zero_of_false hL (by omega) (x:=wl) (by simp [walkBools]) hl
    have hc := walk_cont hL hr (by simpa only [isOne,decide_eq_true_eq] using ha) hz
    simp [isOne,hc.1,hc.2]
  · intro r hr hl hn
    simp only [isOne,decide_eq_true_eq] at hl hn ⊢
    exact walk_next hL hr hl hn
  · intro r hr ha
    have hz := zero_of_false hL (by omega) (x:=walk) (by simp [walkBools]) ha
    simp [isOne,walk_pad hL hr hz]
  · intro hH
    simp [isOne,walk_start hL hH]
  · intro hH ha
    simp only [isOne,decide_eq_true_eq] at ha ⊢
    exact walk_stop hL hH ha

theorem height_le : tr.height tt ≤ 2^22 := by
  have h := hL.log_le
  exact Nat.pow_le_pow_right (by decide) h

theorem height_pos : 0<tr.height tt := Nat.two_pow_pos _

theorem walk_segments : ∃ segs : List (Nat × Nat), Consec 0 segs ∧
    segEnd 0 segs ≤ tr.height tt ∧
    (∀ p ∈ segs, IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) p.1 p.2) ∧
    (∀ r, segEnd 0 segs ≤ r → r<tr.height tt → isOne tr tt walk r=false) :=
  segments_of (walk_segFacts hL) (height_pos hL)

end ZkFormal.NearV3.Qv.Extract
