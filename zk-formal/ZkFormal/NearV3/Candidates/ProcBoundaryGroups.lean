import ZkFormal.NearV3.Candidates.ProcBoundaryEntries
namespace ZkFormal.NearV3.Candidates.ProcBoundaryGroups
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcBoundaryRepair

theorem key_groups (R S : Run) (ht : S.tau=R.tau+1)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀e∈cKey++Proc.cHdr++Proc.cEnt,e.eval tr t r pub=0 := by
  simp only [List.forall_mem_append]
  exact ⟨⟨ProcBoundaryKeys.key_to_key R S ht tr t r pub hc hn,
    ProcBoundaryEntries.header_key_to_key R S tr t r pub hc hn⟩,
    ProcNonEntry.constraints R (keyV R 15) (Or.inl ⟨15,rfl⟩) tr t r pub hc⟩

theorem entry_groups (R S : Run) (rd : RoundD) (es : Array Entry) (i : Nat)
    (hi : i+1=es.size) (ht : S.tau=R.tau+1)
    (hok : ProcEntryScalar.EntryOk rd.z es[i]!) (hlen : rd.Lr=es.size) (hx : es[i]!.x=i)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((entV R rd es i).cell c))
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV S 0).cell c)) :
    ∀e∈cKey++Proc.cHdr++Proc.cEnt,e.eval tr t r pub=0 := by
  simp only [List.forall_mem_append]
  refine ⟨⟨ProcBoundaryEntries.entry_to_key R S rd es i hi ht tr t r pub hc hn,
    ProcBoundaryEntries.header_entry_to_key R S rd es i hi tr t r pub hc hn⟩,?_⟩
  exact ProcEntryAdjacent.entry_constraints R rd es i hok hlen hx tr t r pub hc
    (fun h=>False.elim (h hi)) (fun h=>False.elim (h hi))
end ZkFormal.NearV3.Candidates.ProcBoundaryGroups
