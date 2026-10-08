import ZkFormal.NearV3.Assembly.RcptSkeletonFields

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Control-only row assignment. Other row groups will extend this assignment
on disjoint columns and provide the per-receipt/list constants. -/
def controlCell (row : Coord) (col : Nat) : Fp :=
  if col=idx then Fp.ofNat row.index else
  if col=act then 1 else
  if col=fs then (if row.index=0 then 1 else 0) else
  if col=fe then (if row.index+1=row.length then 1 else 0) else
  if 4≤col ∧ col≤26 then (if col=row.state then 1 else 0) else 0

def controlPair (row next : Coord) : Trace Fp :=
  ⟨fun _=>1,fun _ r=>controlCell (if r=0 then row else next)⟩

theorem control_state (row : Coord) {s : Nat} (hs : s∈states) :
    controlCell row s=if s=row.state then 1 else 0 := by
  obtain ⟨hlo,hhi⟩ := states_limits hs
  have hi : s≠idx := by unfold idx;omega
  have ha : s≠act := by unfold act;omega
  have hf : s≠fs := by unfold fs;omega
  have he : s≠fe := by unfold fe;omega
  simp only [controlCell,if_neg hi,if_neg ha,if_neg hf,if_neg he,if_pos (show 4≤s ∧ s≤26 from ⟨hlo,hhi⟩)]

private theorem sum_cells_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    ∀cs : List Nat,(∀c∈cs,tr.cell t r c=0)→(sum (cs.map Dsl.c)).eval tr t r pub=0
  | [],_=>rfl
  | c::cs,h=>by
    simp only [List.map_cons,eval_sum_cons,eval_c,h c (by simp)]
    rw [sum_cells_zero tr t r pub cs (fun x hx=>h x (by simp [hx]))]
    grind only

/-- Generic one-hot sum argument, also used in the legacy receipt renderer;
this version consumes actual trace cells and has no legacy Good assumptions. -/
private theorem sum_cells_one (tr : Trace Fp) (t r : Nat) (pub : List Fp) (s : Nat) :
    ∀cs : List Nat,cs.Nodup→s∈cs→tr.cell t r s=1→
      (∀c∈cs,c≠s→tr.cell t r c=0)→(sum (cs.map Dsl.c)).eval tr t r pub=1
  | [],_,h,_,_=>by cases h
  | c::cs,hnd,hm,hone,hzero=>by
    have hd := List.nodup_cons.mp hnd
    simp only [List.map_cons,eval_sum_cons,eval_c]
    by_cases hc : c=s
    · subst c
      rw [hone,sum_cells_zero tr t r pub cs (by
        intro x hx
        apply hzero x (by simp [hx])
        intro he; subst x; exact hd.1 hx)]
      grind only
    · rw [hzero c (by simp) hc,sum_cells_one tr t r pub s cs hd.2
        (by simpa [Ne.symm hc] using hm) hone (fun x hx hxs=>hzero x (by simp [hx]) hxs)]
      grind only

theorem control_onehot (row next : Coord) (hs : row.state∈states) (pub : List Fp) :
    (sum (states.map Dsl.c)).eval (controlPair row next) 0 0 pub=1 := by
  apply sum_cells_one _ _ _ _ row.state states (by decide) hs
  · change controlCell row row.state=1
    rw [control_state row hs]; simp
  · intro c hc hne
    change controlCell row c=0
    rw [control_state row hc,if_neg hne]

theorem control_boolean (row : Coord) (col : Nat) (hc : col≠idx) :
    controlCell row col=0 ∨ controlCell row col=1 := by
  simp only [controlCell,if_neg hc]
  grind only

/-- These are literally the row-local one-hot and nonterminal bookkeeping
polynomials of the active V3 cStates family. -/
def continuationConstraints : List Expr :=
  [sub (sum (states.map Dsl.c)) (c act),
   mul3 (c act) (Dsl.not (c fe)) (sub (n idx) (.add (c idx) (k 1))),
   mul3 (c act) (Dsl.not (c fe)) (n fs)] ++
    states.map (fun s=>mul3 (c act) (Dsl.not (c fe)) (sub (n s) (c s)))

theorem continuation_in_states : ∀e∈continuationConstraints,e∈cStates := by
  intro e he
  simp only [continuationConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
