import ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonRows
namespace ZkFormal.NearV3.Candidates.ProcPriorComparisonEnumeration
open ProcPriorComparisonRequests

def atRow {α : Type} (f : α→α→List Request) (xs : List α) (r : Nat) : List Request :=
  match xs[r]?,xs[r+1]? with
  | some a,some b=>f a b
  | _,_=>[]

theorem indexed {α : Type} (f : α→α→List Request) (xs : List α) :
    (List.range xs.length).flatMap (atRow f xs)=adjacent f xs := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    rw [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
    have ht:(List.range xs.length).flatMap (fun r=>atRow f (a::xs) (r+1))=
        (List.range xs.length).flatMap (atRow f xs):=by
      apply ZkFormal.Near.flatMap_congr'
      intro r hr
      simp [atRow,List.getElem?_cons_succ]
    rw [ht,ih]
    cases xs with
    | nil=>rfl
    | cons b xs=>rfl

theorem padding {α : Type} (f : α→α→List Request) (xs : List α) (r : Nat) (hr:xs.length≤r) :
    atRow f xs r=[] := by simp [atRow,List.getElem?_eq_none hr]

theorem physical {α : Type} (f : α→α→List Request) (xs : List α) (n : Nat) (hn:xs.length≤n) :
    (List.range n).flatMap (atRow f xs)=adjacent f xs := by
  rw [show n=xs.length+(n-xs.length) by omega,List.range_add,List.flatMap_append,List.flatMap_map,indexed]
  have hz:(List.range (n-xs.length)).flatMap (fun j=>atRow f xs (xs.length+j))=[]:=by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    exact padding f xs _ (by omega)
  rw [hz,List.append_nil]
end ZkFormal.NearV3.Candidates.ProcPriorComparisonEnumeration
