import ZkFormal.NearV3.Qv.Extract.ParserAggregate
import ZkFormal.NearV3.Link.Walk3Chain

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

/-- Counter balance cannot support a provider-free cycle when fewer than P
requests are present. Duplicate requests are counted, not deduplicated. -/
theorem counter_provider_exists (providers requests : List (Msg × Nat))
    (hp : ∀ p∈providers, p.1.length=3 ∧ Canon p.1)
    (hr : ∀ r∈requests, r.1.length=3 ∧ Canon r.1 ∧ r.2<P)
    (hbound : requests.length<P)
    (hbalance : ((providers.map (fun p => p.1++[0]) ++ requests.map (fun r => r.1++[r.2+1])).map Msg.toFp).Perm
      ((providers.map (fun p => p.1++[p.2]) ++ requests.map (fun r => r.1++[r.2])).map Msg.toFp)) :
    ∀ r∈requests, ∃ p∈providers, p.1=r.1 := by
  intro r hmem
  by_cases hex : ∃ p∈providers, p.1=r.1
  · exact hex
  · exfalso
    apply ZkFormal.NearV3.Walk3.chain_provided
      (providers.map (fun p => p.1++[0])) (providers.map (fun p => p.1++[p.2])) requests r.1
      _ hr hbound (hr r hmem).1 (hr r hmem).2.1 hmem hbalance
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hm
      exact ⟨p.1,0,rfl,(hp p hp').1,(hp p hp').2,fun he => hex ⟨p,hp',he⟩⟩
    · obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hm
      exact ⟨p.1,p.2,rfl,(hp p hp').1,(hp p hp').2,fun he => hex ⟨p,hp',he⟩⟩

def requestKey (tr : Trace Fp) (tt r : Nat) : Msg :=
  [cv tr tt r Candidates.ValueTable.vid,cv tr tt r Candidates.ValueTable.tau,
    cv tr tt r Candidates.ValueTable.len]

def providerKey (tr : Trace Fp) (tt r : Nat) (pub : List Fp) : Msg :=
  [cv tr tt r Candidates.ValueTable.vid,cv tr tt r Candidates.ValueTable.tau,
    (Candidates.ValueTable.mode.eval tr tt r pub).toNat]

theorem requestKey_canon (tr : Trace Fp) (tt r : Nat) :
    (requestKey tr tt r).length=3 ∧ Canon (requestKey tr tt r) := by
  constructor
  · rfl
  · intro x hx
    simp only [requestKey,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact cv_lt _ _ _ _

theorem providerKey_canon (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    (providerKey tr tt r pub).length=3 ∧ Canon (providerKey tr tt r pub) := by
  constructor
  · rfl
  · intro x hx
    simp only [providerKey,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact cv_lt _ _ _ _
    · exact cv_lt _ _ _ _
    · exact Fp.toNat_lt _

theorem endpoint_natural (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) :
    (providerKey tr tt r pub ++ [if sd then 0 else cv tr tt r Candidates.ValueTable.users]).toFp=
      Parser.endpointMessage tr tt r pub sd := by
  cases sd <;> simp [providerKey,Msg.toFp,Parser.endpointMessage,ofNat_cv,Fp.ofNat_toNat,show Fp.ofNat 0 = 0 from rfl]

theorem request_natural (tr : Trace Fp) (tt r : Nat) (sd : Bool) :
    (requestKey tr tt r ++ [if sd then cv tr tt r Candidates.ValueTable.users+1 else cv tr tt r Candidates.ValueTable.users]).toFp=
      counterMessage tr tt r sd := by
  cases sd
  · simp [requestKey,Msg.toFp,counterMessage,ofNat_cv]
  · simp only [requestKey,Msg.toFp,List.map_append,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,ofNat_cv,counterMessage,ite_true]
    have hh := natCast_add (cv tr tt r Candidates.ValueTable.users) 1
    change Fp.ofNat (cv tr tt r Candidates.ValueTable.users+1)=
      Fp.ofNat (cv tr tt r Candidates.ValueTable.users)+(1:Fp) at hh
    rw [hh,ofNat_cv]

end ZkFormal.NearV3.Qv.Extract
