import ZkFormal.NearV3.Candidates.ProcessRepairQueueKey
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Extract

theorem flat_lookup (ls:RcptV3Vs) {j:Nat} (hj:j<ls.length) (k:Nat) (hk:k<ls[j].rs.length):
    (flatR ls).getD (baseR ls j+k) default=ls[j].rs.getD k default:=by
  induction ls generalizing j with
  | nil=>simp at hj
  | cons L ls ih=>
    cases j with
    | zero=>
      simp only [baseR,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,
        flatR,List.flatMap_cons,List.getElem_cons_zero]
      have hk0:k<L.rs.length:=hk
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,hk0]
    | succ j=>
      have hj':j<ls.length:=by simpa using hj
      have hk':k<ls[j].rs.length:=hk
      have h:=ih hj' hk'
      simp only [baseR,List.take_succ_cons,List.map_cons,List.sum_cons,
        flatR,List.flatMap_cons,List.getElem_cons_succ]
      simpa only [flatR,baseR,List.getD_eq_getElem?_getD,List.getElem?_append,
        Nat.add_assoc,Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left] using h

theorem message_id (r:Nat) (ss:List Nat) {m:Msg} (hm:m∈RcptE.keyMsgs r ss):m.getD 0 0=r:=by
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
  rfl

theorem account_owner {pub:List Fp} {ls:RcptV3Vs}
    (hn:(flatR ls).length≤W_AK) {r:Nat} (hr:r<(flatR ls).length)
    {m:Msg} (hm:m∈rcptSends3 pub ls B_KEYNIB) (hid:m.getD 0 0=r):
    m∈RcptE.keyMsgs r ((flatR ls).getD r default).keySyms:=by
  simp only [rcptSends3,show B_KEYNIB≠B_BYTES by decide,show B_KEYNIB≠B_RCL by decide,
    ite_false,List.nil_append] at hm
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hj:=List.mem_range.mp hj
  obtain ⟨⟨r',off,x⟩,hp,hm⟩:=List.mem_flatMap.mp hm
  have hget:ls.getD j default=ls[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  simp only [located,hget,List.mem_map,List.mem_range] at hp
  obtain ⟨k,hk,hp⟩:=hp
  cases hp
  simp only [rSends,show B_KEYNIB≠B_BYTES by decide,ite_false,ite_true,List.mem_append] at hm
  rcases hm with hm|hm
  · have he:baseR ls j+k=r:=(message_id _ _ hm).symm.trans hid
    rw [←he,flat_lookup ls hj k hk]
    exact hm
  · split at hm
    · have he:W_AK+(baseR ls j+k)=r:=(message_id _ _ hm).symm.trans hid
      omega
    · simp at hm

theorem walk_messages {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {bs:List RcptV3Proof.ListBlock} {e:Nat}
    (hc:RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (hn:(flatR (bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length≤W_AK)
    {ws:List WalkR} (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {w:WalkR} (hw:w∈ws)
    (hr:w.w<(flatR (bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    ∀j,1≤j→j<w.steps.length→
      (Msg.toFp [w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0])∈
      (RcptE.keyMsgs w.w ((flatR (bs.map (RcptV3Proof.ListBlock.view
        (ProcPriorRoutedReceiptView.receipt tr) 0))).getD w.w default).keySyms).map Msg.toFp:=by
  intro j hj hj'
  let ls:=bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)
  let m:Msg:=[w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0]
  have hm:m∈walkRecvs3 ws B_KEYNIB:=by
    unfold walkRecvs3
    rw [if_neg (by decide),if_neg (by decide),if_pos rfl,List.mem_flatMap]
    refine ⟨w,hw,List.mem_map.mpr ⟨j-1,List.mem_range.mpr (by omega),?_⟩⟩
    simp only [m,show j-1+1=j by omega,show j-1+2=j+1 by omega]
  have hbal:=ProcessRepairKeyBalance.balance view hpub hc hWT
  have hsend:=hbal.mem_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  rcases List.mem_append.mp hsend with hq|hs
  · have hL:=ProcessRepairKeyView.local_key view
    obtain ⟨q⟩:=walk_chain_exists (Qv.Candidates.KeyTrafficRepair.local_to_base hL)
    have hphysical:(List.range (tr.height 0)).flatMap (fun r=>rowTraffic
        Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_KEYNIB true)=
        q.segs.flatMap (fun p=>repairedKeyTraffic (Qv.Candidates.CombinedTable.wid.eval
          (ProcPriorRoutedKeyView.key tr) 0 p.1 pub) (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 p)):=
      repaired_key_physical hL q
    rw [hphysical] at hq
    obtain ⟨p,hp,hpmsg⟩:=List.mem_flatMap.mp hq
    obtain ⟨i,hi,hpi⟩:=List.getElem_of_mem hp
    subst p
    have hid:=repaired_key_owner _ _ hpmsg
    obtain ⟨n,hn0,hnP,he⟩:=queue_walk_id_range (Qv.Candidates.KeyTrafficRepair.local_to_base hL) q i hi
    rw [he] at hid
    change Fp.ofNat w.w=Fp.ofNat n at hid
    have hwP:w.w<P:=by unfold W_AK P at *;omega
    have hh:=Link.ofNat_inj hwP hnP hid
    unfold W_AK W_QV at *
    omega
  · obtain ⟨mr,hmr,he⟩:=List.mem_map.mp hs
    have hrange:=receipt_key_id_range hn hmr
    have hid:=congrArg (fun xs:List Fp=>xs.getD 0 0) he
    change (mr.map Fp.ofNat).getD 0 (Fp.ofNat 0)=Fp.ofNat w.w at hid
    rw [Link3.getD_map'] at hid
    have hidNat:mr.getD 0 0=w.w:=Link.ofNat_inj (by unfold W_QV P at *;omega)
      (by unfold W_AK P at *;omega) hid
    exact List.mem_map.mpr ⟨mr,account_owner hn hr hmr hidNat,he⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner

