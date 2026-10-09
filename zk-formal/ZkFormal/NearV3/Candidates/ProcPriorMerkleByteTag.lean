import ZkFormal.NearV3.Candidates.ProcPriorMerkleView
namespace ZkFormal.NearV3.Candidates.ProcPriorMerkleByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ProcPriorMerkleView

theorem semantic (pub:List Fp) (v:MrkV) (hv:v.nodes.length≤2^19)
    {m:Msg} (hm:m∈mrkSends pub v B_BYTES) :
    m.headD 0<P ∧ m.headD 0%16=K_MRK := by
  simp only [mrkSends,ite_true] at hm
  obtain ⟨⟨nd,q⟩,_,hm⟩:=List.mem_flatMap.mp hm
  cases nd with
  | promoted _ _=>cases hm
  | hashed a b l c d r=>
    obtain ⟨p,_,rfl⟩:=List.mem_map.mp hm
    have hf:hashedBefore v.nodes q≤v.nodes.length := by
      exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_take];omega)
    change msgId K_MRK (hashedBefore v.nodes q)<P ∧ msgId K_MRK (hashedBefore v.nodes q)%16=K_MRK
    unfold msgId K_MRK P
    omega

theorem tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {msg:List Fp}
    (hm:0<tableBusCount (AP.tables[10]!).interactions tr 10 pub B_BYTES true msg) :
    (msg.headD 0).toNat%16=K_MRK := by
  rw [htables,count] at hm
  have hl:=local_empty hH htables
  have hnon:MerkleEmpty.countE.eval (mirror tr) T_MRK 0 pub≠0 := by
    intro hz
    have hzero:=(MerkleEmpty.empty_view hl hz).2 B_BYTES true msg
    omega
  obtain ⟨v,hw,hT⟩:=MerkleEmpty.nonempty_view hl hnon
  have hv:=node_bound hl.log_le hT
  rw [(hT B_BYTES msg).1] at hm
  obtain ⟨m,hm,heq⟩:=List.mem_map.mp (List.count_pos_iff.mp hm)
  have hsafe:=semantic (MerklePublic.aliasPublic pub) v hv hm
  have hhead:msg.headD 0=Fp.ofNat (m.headD 0) := by
    rw [←heq]
    cases m <;> rfl
  rw [hhead,Fp.toNat_ofNat,Nat.mod_eq_of_lt hsafe.1]
  exact hsafe.2
end ZkFormal.NearV3.Candidates.ProcPriorMerkleByteTag
