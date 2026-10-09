import ZkFormal.NearV3.Assembly.SchedulerChildDigests
import ZkFormal.NearV3.Render.Ups.TreePlan

namespace ZkFormal.NearV3.Assembly
open NearSpec ZkFormal.Near UpsRows Render.UpsGen

/-- Canonical dependency order for a native part. Branch-window physical order
may permute these uses; this definition does not assert that byte linkage. -/
def partDigestUses (cs : UCase) (k : Nat) : UKind→List Nat
  | .RLP | .RBR | .RBV | .NLF => [0]
  | .RDB | .RDE | .PT | .RBI | .WEX => [k]
  | .MVL | .MVE => []
  | .SPB => match cs with
    | .LSa | .ESn1 => [k]
    | .LSb | .ESl0 => [0,1]
    | .LSc | .ESn0 => [1,k]
    | .ESl1 => [0]
    | _ => []

def planDigestUses (cs : UCase) : Nat→List UKind→List Nat
  | _,[]=>[]
  | k,p::ps=>partDigestUses cs k p++planDigestUses cs (k+1) ps

private theorem uses_append (cs : UCase) (start : Nat) (xs ys : List UKind) :
    planDigestUses cs start (xs++ys)=
      planDigestUses cs start xs++planDigestUses cs (start+xs.length) ys := by
  induction xs generalizing start with
  | nil=>simp [planDigestUses]
  | cons x xs ih=>simp [planDigestUses,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Every terminal case uses fresh value 0 and each previous node exactly once
in canonical dependency order, including moved-node and inserted-leaf cases. -/
theorem terminal_digest_uses (cs : UCase) (matched : Nat) :
    planDigestUses cs 0 (termPlan cs matched)=List.range (termPlan cs matched).length := by
  by_cases h:1≤matched
  · cases cs <;> simp [termPlan,UCase.split,h,planDigestUses,partDigestUses] <;> rfl
  · cases cs <;> simp [termPlan,UCase.split,h,planDigestUses,partDigestUses] <;> rfl

private theorem upper_uses (cs : UCase) (start : Nat) (xs : List UKind)
    (h : ∀k∈xs,k.upper=true) :
    planDigestUses cs start xs=(List.range xs.length).map (start+·) := by
  induction xs generalizing start with
  | nil=>rfl
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (start+1) (fun k hk=>h k (by simp [hk]))
    have he : partDigestUses cs start x=[start] := by cases x <;> simp_all [UKind.upper,partDigestUses]
    simp only [planDigestUses,he,List.singleton_append,ht,List.length_cons,List.range_succ_eq_map,
      List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    dsimp
    omega

/-- The native plan consumes every value/output job below its final root once.
This includes arbitrary ancestor depth, not just a fixed terminal fixture. -/
theorem planned_digest_uses {run : TreeRun} (hp : run.Planned) :
    planDigestUses run.terminal 0 (run.parts.map TreePart.kind)=List.range run.parts.length := by
  obtain ⟨upper,he,hu⟩:=hp
  have hl:=congrArg List.length he
  simp only [List.length_map,List.length_append] at hl
  rw [he,uses_append,terminal_digest_uses,upper_uses _ _ _ hu,Nat.zero_add,hl,List.range_add]

/-- Actual runtime execution supplies the plan; adding its final W3 root use
accounts for all job indices, retaining the global transition tag separately. -/
theorem traceUpsert_digest_uses {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) :
    planDigestUses run.terminal 0 (run.parts.map TreePart.kind)++[run.parts.length]=
      List.range (run.parts.length+1) := by
  rw [planned_digest_uses (traceUpsert_plan root key value run hr),List.range_succ]

end ZkFormal.NearV3.Assembly
