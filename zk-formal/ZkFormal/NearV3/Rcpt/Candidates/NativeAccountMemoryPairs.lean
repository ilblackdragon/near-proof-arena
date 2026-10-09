import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountSlotVersions
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem nativeAccountSlot_mem {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) (j : Nat) (hj:j<rs.length) :
    accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) j∈as.map AcctV.k := by
  let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
  have hjk:j<keys.length:=by simpa [keys] using hj
  obtain ⟨i,hi⟩:=nativeAccountViews_keys_defined h keys[j] (List.getElem_mem hjk)
  have hg:keys.getD j []=keys[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hjk]
  change (valueIndex pre (keys.getD j [])).getD 0∈_
  rw [hg,hi]
  rw [closingAccountViews_ids h]
  exact List.mem_filterMap.mpr ⟨keys[j],(distinctTouched_mem _ _).mpr (List.getElem_mem hjk),hi⟩

theorem nativeAccount_last_lb {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) (a : AcctV) (ha:a∈as) :
    a.tlast=NativeMemChain.lb (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId))) a.k rs.length := by
  obtain ⟨key,hkey,hview⟩:=closingAccountViews_member h a ha
  have hid:=closingAccountView_id hview
  have ht:=nativeAccountViews_keys_defined h
  have he:=closingKeyVersion_prefix_lb _ _ key a.k
    (accountSlot_key_iff pre _ ht hid) rs.length (by simp)
  have htaken:(rs.map (fun r=>accountKeyPath r.receiverId)).take rs.length=rs.map (fun r=>accountKeyPath r.receiverId):=by
    exact List.take_of_length_le (by simp)
  rw [htaken] at he
  exact (closingAccountView_version hview).trans he

/-- Full timestamp conservation for the actual native closing account list.
The receipt count has no legacy 512-receipt bound; every repeated receiver is
represented at its own occurrence time. Payload byte agreement is separate. -/
theorem nativeAccount_memory_pairs {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) :
    let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
    let slot:=accountSlot pre keys
    ((List.range rs.length).map (fun r=>(slot r,r+1))++as.map (fun (a : AcctV)=>(a.k,0))).Perm
      ((List.range rs.length).map (fun r=>(slot r,closingKeyVersion (keys.getD r []) 0 (keys.take r)))++
        as.map (fun (a : AcctV)=>(a.k,a.tlast))) := by
  dsimp only
  have hp:=NativeMemChain.pairs_perm (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)))
    rs.length (nativeAccountViews_ids_nodup h) (nativeAccountSlot_mem h)
  simp only [NativeMemChain.pairsW,NativeMemChain.pairsR,List.map_map,Function.comp_def] at hp
  have hlast:as.map (fun (a : AcctV)=>(a.k,NativeMemChain.lb (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId))) a.k rs.length))=
      as.map (fun (a : AcctV)=>(a.k,a.tlast)):=by
    apply List.map_congr_left
    intro a ha
    rw [nativeAccount_last_lb h a ha]
  rw [hlast] at hp
  have hprev:(List.range rs.length).map (fun r=>(accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) r,
      NativeMemChain.lb (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)))
        (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) r) r))=
      (List.range rs.length).map (fun r=>(accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) r,
        closingKeyVersion ((rs.map (fun r=>accountKeyPath r.receiverId)).getD r []) 0
          ((rs.map (fun r=>accountKeyPath r.receiverId)).take r))) := by
    apply List.map_congr_left
    intro r hr
    have hb:r<(rs.map (fun r=>accountKeyPath r.receiverId)).length:=by simpa using List.mem_range.mp hr
    rw [show (rs.map (fun r=>accountKeyPath r.receiverId)).getD r []=(rs.map (fun r=>accountKeyPath r.receiverId))[r] from by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb]]
    rw [accountSlot_previous pre _ (nativeAccountViews_keys_defined h) r hb]
  rw [hprev] at hp
  exact hp

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
