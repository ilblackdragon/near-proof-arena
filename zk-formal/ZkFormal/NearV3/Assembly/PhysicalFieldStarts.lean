import ZkFormal.NearV3.Assembly.CompactDigestWindows

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open Render.UpsGen

def fieldBytes (sh : List (Nat×Nat)) : Nat := (sh.map Prod.snd).sum

/-- Execute the requests at actual nonempty field starts, preserving both byte
positions and the number of preceding child-hash fields. -/
def fieldStarts {α : Type} (F : Nat→Nat→Nat→List α) : List (Nat×Nat)→Nat→Nat→List α
  | [],_,_=>[]
  | (s,n)::rest,base,wi=>
    (if n=0 then [] else F base s wi)++fieldStarts F rest (base+n) (wi+if s=7 then 1 else 0)

private theorem flat_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

private theorem range_first {α : Type} (n : Nat) (F : Nat→List α) :
    (List.range n).flatMap (fun i=>if i=0 then F i else [])=if n=0 then [] else F 0 := by
  cases n with
  | zero=>rfl
  | succ n=>simp [List.range_succ_eq_map,List.flatMap_map]

/-- The complete physical scan contributes precisely its field-start requests.
Zero-length fields are handled explicitly; no fixed header size is assumed. -/
theorem field_start_scan {α : Type} (F : Nat→Nat→Nat→List α) (sh : List (Nat×Nat)) (base wi : Nat) :
    (List.range (fieldBytes sh)).flatMap (fun p=>
      let a:=fieldAt sh p
      if a.2.1=0 then F (base+p) a.1 (wi+a.2.2.2) else [])=fieldStarts F sh base wi := by
  induction sh generalizing base wi with
  | nil=>rfl
  | cons h rest ih=>
    rcases h with ⟨s,n⟩
    simp only [fieldBytes,List.map_cons,List.sum_cons,List.range_add,List.flatMap_append,List.flatMap_map]
    have hfirst : (List.range n).flatMap (fun p=>
        let a:=fieldAt ((s,n)::rest) p
        if a.2.1=0 then F (base+p) a.1 (wi+a.2.2.2) else [])=
        if n=0 then [] else F base s wi := by
      apply Eq.trans (b := (List.range n).flatMap (fun p=>if p=0 then F (base+p) s wi else []))
      · apply flat_congr
        intro p hp
        simp only [fieldAt,show p<n from List.mem_range.mp hp,ite_true,Nat.add_zero]
      · rw [range_first]
        simp only [Nat.add_zero]
    rw [hfirst]
    unfold fieldStarts
    congr 1
    rw [←ih (base+n) (wi+if s=7 then 1 else 0)]
    apply flat_congr
    intro p hp
    simp only [Function.comp_def,fieldAt,show ¬n+p<n by omega,ite_false,Nat.add_sub_cancel_left]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
