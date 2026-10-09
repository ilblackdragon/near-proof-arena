import ZkFormal.NearV3.Candidates.HorizontalProfile
import ZkFormal.Near.Extract.BusCount
namespace ZkFormal.NearV3.Candidates.InteractionPairing
open ZkFormal.Air ZkFormal.Algebra

def interleave {α : Type} : List α→List α→List α
  | [],ys=>ys
  | xs,[]=>xs
  | x::xs,y::ys=>x::y::interleave xs ys

theorem interleave_perm {α : Type} (xs ys : List α) : (interleave xs ys).Perm (xs++ys) := by
  induction xs generalizing ys with
  | nil=>simp [interleave]
  | cons x xs ih=>
    cases ys with
    | nil=>simp [interleave]
    | cons y ys=>
      exact ((ih ys).cons y |>.cons x).trans (List.perm_middle.symm.cons x)

def paired (xs : List Interaction) : List Interaction:=
  interleave (xs.filter (fun i=>2<i.phiDegree)) (xs.filter (fun i=>!(2<i.phiDegree)))

def reorder (xs : List Interaction) : List Interaction:=
  paired (xs.filter (·.send))++paired (xs.filter (fun i=>!i.send))

theorem paired_perm (xs : List Interaction) : (paired xs).Perm xs :=
  (interleave_perm _ _).trans (List.filter_append_perm _ _)

theorem reorder_perm (xs : List Interaction) : (reorder xs).Perm xs :=
  ((paired_perm _).append (paired_perm _)).trans (List.filter_append_perm _ _)

private theorem fold_sum {α : Type} (xs : List α) (f : α→Nat) (n : Nat) :
    xs.foldr (fun x z=>f x+z) n=(xs.map f).sum+n := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp [ih,Nat.add_assoc]

theorem count_perm (xs ys : List Interaction) (h : xs.Perm ys)
    (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount xs tr t pub b send msg=tableBusCount ys tr t pub b send msg := by
  unfold tableBusCount
  congr 1
  funext r z
  simp only [fold_sum]
  exact congrArg (·+z) (h.map _).sum_nat

theorem count (xs : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (reorder xs) tr t pub b send msg=tableBusCount xs tr t pub b send msg :=
  count_perm _ _ (reorder_perm xs) tr t pub b send msg

theorem local_iff (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal {T with interactions:=reorder T.interactions} tr t pub ↔
      ZkFormal.Near.TableLocal T tr t pub := by
  constructor
  · intro h
    refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
    intro r hr i hi b hb
    exact h.bits r hr i ((reorder_perm T.interactions).mem_iff.mpr hi) b hb
  · intro h
    refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
    intro r hr i hi b hb
    exact h.bits r hr i ((reorder_perm T.interactions).mem_iff.mp hi) b hb

end ZkFormal.NearV3.Candidates.InteractionPairing
