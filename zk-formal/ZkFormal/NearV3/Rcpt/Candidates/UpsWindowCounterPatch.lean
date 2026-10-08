import ZkFormal.NearV3.Candidates.CompactHeight

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsGen UpsRows

def counterFree : Expr→Bool
  | .col k _ => k != UpsV3.u
  | .add a b | .mul a b => counterFree a && counterFree b
  | .neg a => counterFree a
  | _ => true

/-- Only the counter cell of actual UPB read rows changes. Other buses retain
exactly their previously assigned walk counters. -/
def patchWindowCounters (tr : Trace Fp) (t : Nat) (rank : Nat→Nat) : Trace Fp where
  log:=tr.log
  cell:=fun tt r c=>if tt=t ∧ tr.cell t r UpsV3.rd=1 ∧ c=UpsV3.u then Fp.ofNat (rank r) else tr.cell tt r c

theorem patchWindowCounters_eval (tr : Trace Fp) (t r : Nat) (rank : Nat→Nat)
    (pub : List Fp) : ∀e,counterFree e=true→
    e.eval (patchWindowCounters tr t rank) t r pub=e.eval tr t r pub
  | .const _,_ => rfl
  | .col c nx,h => by
    have hc : c≠UpsV3.u := by simpa [counterFree] using h
    simp [Expr.eval,Expr.evalWith,rowEnv,patchWindowCounters,hc,Trace.height]
  | .pub _,_ => rfl
  | .isFirst,_ => rfl
  | .isLast,_ => rfl
  | .isTransition,_ => rfl
  | .add a b,h => by
    simp only [counterFree,Bool.and_eq_true] at h
    change a.eval _ _ _ _+b.eval _ _ _ _=_
    rw [patchWindowCounters_eval tr t r rank pub a h.1,patchWindowCounters_eval tr t r rank pub b h.2]
    rfl
  | .mul a b,h => by
    simp only [counterFree,Bool.and_eq_true] at h
    change a.eval _ _ _ _*b.eval _ _ _ _=_
    rw [patchWindowCounters_eval tr t r rank pub a h.1,patchWindowCounters_eval tr t r rank pub b h.2]
    rfl
  | .neg a,h => by
    change -(a.eval _ _ _ _)=_
    rw [patchWindowCounters_eval tr t r rank pub a h]
    rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem compact_constraints_counterFree :
    Render.UpsRelay.compactConstraints.all counterFree=true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem compact_gates_counterFree :
    Render.UpsRelay.compactTable.interactions.all (fun i=>i.mult.all counterFree)=true := by decide

theorem patchWindowCounters_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal Render.UpsRelay.compactTable tr t pub) (rank : Nat→Nat) :
    TableLocal Render.UpsRelay.compactTable (patchWindowCounters tr t rank) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rw [patchWindowCounters_eval tr t r rank pub e (List.all_eq_true.mp compact_constraints_counterFree e he)]
    exact h.constr r hr e he
  · intro r hr i hi g hg
    have hc:=List.all_eq_true.mp compact_gates_counterFree i hi
    rw [patchWindowCounters_eval tr t r rank pub g (List.all_eq_true.mp hc g hg)]
    exact h.bits r hr i hi g hg

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
