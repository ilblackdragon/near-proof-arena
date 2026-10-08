import ZkFormal.NearV3.Candidates.InteractionTriplesSum
namespace ZkFormal.NearV3.Candidates.InteractionTriples
open ZkFormal.Air ZkFormal.Algebra

theorem forall_iff (xs : List Interaction) (Q : Interaction→Prop)
    (ht:Q (dummy true)) (hf:Q (dummy false)) :
    (∀i∈reorder xs,Q i) ↔ (∀i∈xs,Q i) := by
  classical
  let f:Interaction→Nat:=fun i=>if Q i then 0 else 1
  have hz (ys : List Interaction) : (ys.map f).sum=0 ↔ ∀i∈ys,Q i := by
    induction ys with
    | nil=>simp
    | cons y ys ih=>
      by_cases hy:Q y <;> simp [f,hy,ih] at *
  rw [←hz,←hz,reorder_sum xs f (by simp [f,ht]) (by simp [f,hf])]

theorem local_iff (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal (table T) tr t pub ↔ ZkFormal.Near.TableLocal T tr t pub := by
  constructor
  · intro h
    refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
    intro r hr
    exact (forall_iff T.interactions
      (fun i=>∀e∈i.mult,e.eval tr t r pub=0 ∨ e.eval tr t r pub=1)
      (by simp [dummy]) (by simp [dummy])).mp (h.bits r hr)
  · intro h
    refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
    intro r hr
    exact (forall_iff T.interactions
      (fun i=>∀e∈i.mult,e.eval tr t r pub=0 ∨ e.eval tr t r pub=1)
      (by simp [dummy]) (by simp [dummy])).mpr (h.bits r hr)

theorem dummy_multNat (s : Bool) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (dummy s).multNat tr t r pub=0 := rfl

private theorem fold_sum {α : Type} (xs : List α) (f : α→Nat) (n : Nat) :
    xs.foldr (fun x z=>f x+z) n=(xs.map f).sum+n := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp [ih,Nat.add_assoc]

theorem count (xs : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (reorder xs) tr t pub bus send msg=tableBusCount xs tr t pub bus send msg := by
  unfold tableBusCount
  congr 1
  funext r z
  simp only [fold_sum]
  congr 1
  apply reorder_sum
  all_goals split <;> simp [dummy_multNat]

theorem table_traffic (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (table T).interactions tr t pub bus send msg=
      tableBusCount T.interactions tr t pub bus send msg := count _ tr t pub bus send msg

end ZkFormal.NearV3.Candidates.InteractionTriples
