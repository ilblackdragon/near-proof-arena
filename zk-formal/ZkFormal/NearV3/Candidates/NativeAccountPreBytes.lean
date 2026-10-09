import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountJobPermutation
import ZkFormal.NearV3.Candidates.NativeAccountTrace

namespace ZkFormal.NearV3.Candidates.NativeAccountPreBytes
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem closing_pre {pre post : PTrie} {keys : List (List Nat)} {key : List Nat} {a : AcctV}
    (h : closingAccountView pre post keys key=some a) :
    a.pre=((NearSpecV3.valsOf pre).getD a.k []).map UInt8.toNat := by
  unfold closingAccountView at h
  cases hi : valueIndex pre key with
  | none => simp [hi] at h
  | some i =>
    simp only [hi,bind,Option.bind] at h
    cases hb : (NearSpecV3.valsOf pre)[i]? with
    | none => simp [hb] at h
    | some before =>
      simp only [hb] at h
      cases hc : (NearSpecV3.valsOf post)[i]? with
      | none => simp [hc] at h
      | some after =>
        simp only [hc] at h
        cases hd : Account.decode after with
        | none => simp [hd] at h
        | some account =>
          simp only [hd,pure,Option.some.injEq] at h
          subst a
          simp [nativeAccountView,List.getD_eq_getElem?_getD,hb]

theorem account_pre {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h : nativeAccountViews pre post rs=some as) (a : AcctV) (ha : a∈as) :
    a.pre=((NearSpecV3.valsOf pre).getD a.k []).map UInt8.toNat := by
  obtain ⟨key,_,hv⟩:=closingAccountViews_member h a ha
  exact closing_pre hv

/-- Exactly the account-owned portion of original value-byte requests, with
one occurrence per activated original ID. Untouched values need other providers. -/
theorem bytes_perm {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    {writes : List (List Nat×Bytes)}
    (hkeys : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (h : nativeAccountViews pre post rs=some as) :
    (acctV3Sends as B_VBYTES).Perm
      (((List.range (NearSpecV3.valsOf pre).length).filter
        (fun i=>decide (i∈writtenValueIds pre writes))).flatMap
          (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) := by
  have he : acctV3Sends as B_VBYTES=(as.map AcctV.k).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat)) := by
    simp only [acctV3Sends,ite_true,List.flatMap_map]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro a ha
    rw [account_pre h a ha]
  rw [he]
  exact List.Perm.flatMap_right _ (nativeAccountViews_ids_perm hkeys h)

/-- Honest account traffic plus the explicitly untouched remainder partitions
all original pre-value byte requests. This does not assume providers for the
remainder, nor omit implicit-state values. -/
theorem physical_partition {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    {writes : List (List Nat×Bytes)}
    (hkeys : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (h : nativeAccountViews pre post rs=some as)
    (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (t : Nat) (pub msg : List ZkFormal.Algebra.Fp)
    (ht : TableTraffic AccountEmpty.table.interactions tr t pub (acctV3Traffic as)) :
    ZkFormal.Air.tableBusCount AccountEmpty.table.interactions tr t pub B_VBYTES true msg+
      cnt (((List.range (NearSpecV3.valsOf pre).length).filter
        (fun i=>!(decide (i∈writtenValueIds pre writes)))).flatMap
          (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg=
      cnt ((List.range (NearSpecV3.valsOf pre).length).flatMap
          (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg := by
  have hp:=List.Perm.flatMap_right
    (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))
    (List.filter_append_perm (fun i=>decide (i∈writtenValueIds pre writes))
      (List.range (NearSpecV3.valsOf pre).length))
  simp only [List.flatMap_append] at hp
  have ha:=((bytes_perm hkeys h).map Msg.toFp).count_eq msg
  have hc:=(hp.map Msg.toFp).count_eq msg
  rw [(ht B_VBYTES msg).1]
  simp only [acctV3Traffic,cnt,List.map_append,List.count_append] at ha hc ⊢
  omega

end ZkFormal.NearV3.Candidates.NativeAccountPreBytes
