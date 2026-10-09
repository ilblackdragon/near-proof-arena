import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryLanes
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton Render

theorem closingAccountView_pre {pre post : PTrie} {keys : List (List Nat)} {key : List Nat} {a : AcctV}
    (h:closingAccountView pre post keys key=some a) :
    a.pre=((NearSpecV3.valsOf pre).getD a.k []).map UInt8.toNat := by
  simp only [closingAccountView,bind,Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all [nativeAccountView]
  subst a
  simp_all [List.getD_eq_getElem?_getD]

theorem nativeAccountViews_initial_mem {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) (steps : List NativeDepositStep) :
    acctV3Sends as B_MEM=(as.map (fun (a : AcctV)=>(a.k,0))).flatMap (ledgerMemoryLanes pre steps) := by
  simp only [acctV3Sends,B_MEM,B_VBYTES,B_BYTES,Nat.reduceEqDiff,if_false,if_true,List.flatMap_map]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro a ha
  obtain ⟨key,_,hview⟩:=closingAccountViews_member h a ha
  have hb:=closingAccountView_pre hview
  simp only [Function.comp_apply,ledgerMemoryLanes,ledgerSlotBytes,if_true,Option.getD_some]
  apply List.map_congr_left
  intro lane hl
  simp only [nativeMemoryPacket,←hb,acctLane,List.cons_append,List.nil_append]

/-- The account closing packet uses its reconstructed full post payload;
locked/storage bytes are authenticated original suffix bytes. -/
theorem nativeMemoryPacket_closing (a : AcctV) (bs : Bytes)
    (hpayload:bs.map UInt8.toNat=a.post++a.pre.drop 16)
    (hpost:a.post.length=16) (lane : Nat) (hl:lane<16) :
    nativeMemoryPacket a.k a.tlast lane bs=[a.k,a.tlast,lane]++acctLane a a.post lane := by
  simp only [nativeMemoryPacket,hpayload,acctLane,List.cons_append,List.nil_append,
    List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_drop,hpost]
  simp [hl,show ¬16+lane<16 by omega,show ¬64+lane<16 by omega,
    show 16+(16+lane-16)=16+lane by omega,
    show 16+(64+lane-16)=64+lane by omega]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
