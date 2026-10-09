import ZkFormal.NearV3.Candidates.SortGeneralRows
namespace ZkFormal.NearV3.Candidates.SortGeneral
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra ZkFormal.Near.Render

def trace (S : List (Nat×List Nat)) : Trace Fp :=
  {log:=fun _=>18,cell:=fun _ r c=>Fp.ofNat (SortGen.cell S (2^18) r c)}

theorem local_base (S : List (Nat×List Nat)) (ok:IdsOk S) (hn:S.length≤8192)
    (t : Nat) (pub : List Fp) : TableLocal {Sort.table with maxLog:=18} (trace S) t pub := by
  refine ⟨by change 1≤18;decide,by change 18≤18;decide,?_,?_⟩
  · intro r hr e he
    exact SortLocal.constr ok (tr:=trace S) (pub:=pub) (H:=2^18) rfl (by omega)
      (fun _ _ _ _=>rfl) hr he
  · intro r hr i hi b hb
    simp only [Sort.table,Sort.interactions,recv,List.mem_cons,List.not_mem_nil,or_false] at hi
    subst i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    subst b
    change Fp.ofNat (SortGen.cell S (2^18) r Sort.act)=0 ∨ Fp.ofNat (SortGen.cell S (2^18) r Sort.act)=1
    simp only [SortGen.cell,Sort.act,show ¬17≤0 by decide,ite_false]
    split
    · right;rfl
    · left;rfl

theorem complete (S : List (Nat×List Nat)) (ok:IdsOk S) (hn:S.length≤8192)
    (t : Nat) (pub : List Fp) : TableLocal SortEmpty.table (trace S) t pub :=
  SortEmpty.old_local _ _ _ (local_base S ok hn t pub)
end ZkFormal.NearV3.Candidates.SortGeneral
