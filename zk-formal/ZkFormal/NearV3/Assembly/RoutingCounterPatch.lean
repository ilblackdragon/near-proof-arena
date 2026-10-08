import ZkFormal.NearV3.Assembly.RoutingQPredecessor
import ZkFormal.NearV3.Assembly.RoutingCounterRanks

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def usesCounter : Expr→Bool
  | .col k _=>k==uB
  | .add a b | .mul a b=>usesCounter a || usesCounter b
  | .neg a=>usesCounter a
  | _=>false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem constraints_counter_free : candidateTable.constraints.all (fun e=>!(usesCounter e))=true := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem multiplicities_counter_free :
    (RcptV3.interactions.flatMap (·.mult)).all (fun e=>!(usesCounter e))=true := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem other_messages_counter_free :
    ((RcptV3.interactions.filter (fun i=>i.bus != B_BND)).flatMap (·.msg)).all
      (fun e=>!(usesCounter e))=true := by decide

def counterPatch (tr : Trace Fp) (t : Nat) (users : Nat→Nat) : Trace Fp where
  log := tr.log
  cell := fun tt r k=>if tt=t ∧ k=uB then Fp.ofNat (users r) else tr.cell tt r k

theorem counterPatch_eval {tr : Trace Fp} {t r : Nat} {pub : List Fp} (users : Nat→Nat)
    (e : Expr) (he : usesCounter e=false) :
    e.eval (counterPatch tr t users) t r pub=e.eval tr t r pub := by
  induction e with
  | col k nx =>
    have hk : k≠uB := by simpa [usesCounter] using he
    simp [Expr.eval,Expr.evalWith,rowEnv,counterPatch,hk,Trace.height]
  | add a b ia ib =>
    simp only [usesCounter,Bool.or_eq_false_iff] at he
    rw [eval_add,eval_add,ia he.1,ib he.2]
  | mul a b ia ib =>
    simp only [usesCounter,Bool.or_eq_false_iff] at he
    rw [eval_mul,eval_mul,ia he.1,ib he.2]
  | neg a ia => rw [eval_neg,eval_neg,ia he]
  | const => rfl
  | pub => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl

/-- Receipt-side counter assignment does not affect any original or repaired
local polynomial or multiplicity bit. No unproved counter-range premise is used. -/
theorem counterPatch_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal candidateTable tr t pub) (users : Nat→Nat) :
    TableLocal candidateTable (counterPatch tr t users) t pub := by
  refine ⟨hL.log_ge,hL.log_le,?_,?_⟩
  · intro r hr e he
    have hf : usesCounter e=false := by
      have := List.all_eq_true.mp constraints_counter_free e he
      simpa using this
    rw [counterPatch_eval users e hf]
    exact hL.constr r hr e he
  · intro r hr i hi e he
    have hf : usesCounter e=false := by
      have hm := List.mem_flatMap.mpr ⟨i,hi,he⟩
      have := List.all_eq_true.mp multiplicities_counter_free e hm
      simpa using this
    rw [counterPatch_eval users e hf]
    exact hL.bits r hr i hi e he

theorem counterPatch_other_message {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (users : Nat→Nat) {i : Interaction} (hi : i∈RcptV3.interactions) (hb : i.bus≠B_BND) :
    i.msgVal (counterPatch tr t users) t r pub=i.msgVal tr t r pub := by
  apply List.map_congr_left
  intro e he
  have hm : e∈(RcptV3.interactions.filter (fun i=>i.bus != B_BND)).flatMap (·.msg) :=
    List.mem_flatMap.mpr ⟨i,List.mem_filter.mpr ⟨hi,by simpa⟩,he⟩
  have hf := List.all_eq_true.mp other_messages_counter_free e hm
  exact counterPatch_eval users e (by simpa using hf)

end ZkFormal.NearV3.Assembly.RoutingQCandidate
