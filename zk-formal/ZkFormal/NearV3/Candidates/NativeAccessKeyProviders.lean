import ZkFormal.NearV3.Candidates.NativeAccessKeyValidation
import ZkFormal.NearV3.Render.Padded

namespace ZkFormal.NearV3.Candidates.NativeAccessKeyProviders
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Rcpt.Candidates.NodePostUpdate

def selected (pre : PTrie) (rs : List Receipt) : List Nat :=
  (rs.filter (fun r=>r.predecessorId==AccountId.system && r.signerId==r.receiverId)).filterMap
    (fun r=>valueIndex pre (keyAccessKey r.receiverId r.signerPk))

def providers (pre : PTrie) (rs : List Receipt) : List AkeyE :=
  ((selected pre rs).eraseDups).map (fun i=>
    ⟨i,(selected pre rs).count i,((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat⟩)

theorem selected_length (pre : PTrie) (rs : List Receipt) : (selected pre rs).length≤rs.length :=
  Nat.le_trans (List.length_filterMap_le ..) (List.length_filter_le ..)

theorem selected_receipt {pre : PTrie} {rs : List Receipt} {i : Nat}
    (hi:i∈selected pre rs) :
    ∃r∈rs,r.predecessorId=AccountId.system ∧ r.signerId=r.receiverId ∧
      valueIndex pre (keyAccessKey r.receiverId r.signerPk)=some i := by
  obtain ⟨r,hr,hv⟩:=List.mem_filterMap.mp hi
  obtain ⟨hr,hp⟩:=List.mem_filter.mp hr
  simp only [Bool.and_eq_true,beq_iff_eq] at hp
  exact ⟨r,hr,hp.1,hp.2,hv⟩

theorem provider_bytes {pre : PTrie} {rs : List Receipt}
    (hvalid:∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (e : AkeyE) (he:e∈providers pre rs) : e.bytes.length=9 ∧ e.bytes.getD 8 0=1 ∧
      ∀b∈e.bytes,b<256 := by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
  have hi:i∈selected pre rs:=by simpa only [List.mem_eraseDups] using hi
  obtain ⟨r,hr,hs,he,hidx⟩:=selected_receipt hi
  obtain ⟨bytes,hb,hbytes⟩:=NativeReceiptAccessIds.bytes_at hidx
  have hv:=hvalid r hr hs he bytes hb
  simp only [List.getD_eq_getElem?_getD,hbytes,Option.getD_some]
  refine ⟨by simpa using hv.1,?_,?_⟩
  · change (bytes.map UInt8.toNat).getD 8 0=1
    have hh : bytes[8]?=some 1 := by
      have hi8 : 8<bytes.length := by omega
      have hget := hv.2
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi8,Option.getD_some] at hget
      simp [List.getElem?_eq_getElem hi8,hget]
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,hh]
  · intro b hb
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hb
    exact UInt8.toNat_lt x

private theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  match xs with
  | []=>simp
  | a::xs=>
    rw [List.eraseDups_cons,List.nodup_cons]
    refine ⟨?_,eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem provider_rows (pre : PTrie) (rs : List Receipt) (hr:rs.length≤4481) :
    9*(providers pre rs).length≤2^AkeyV3.maxLog := by
  have h1:=(eraseDups_nodup (selected pre rs)).length_le_of_subset
    (fun x hx=>List.mem_eraseDups.mp hx)
  have h2:=selected_length pre rs
  simp only [providers,List.length_map]
  change 9*(selected pre rs).eraseDups.length≤65536
  omega

theorem provider_wf {pre : PTrie} {rs : List Receipt}
    (hvalid:∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (hr:rs.length≤4481) (hv:(NearSpecV3.valsOf pre).length<Algebra.P) :
    AkeyWf (providers pre rs) := by
  refine ⟨fun e he=>(provider_bytes hvalid e he).1,
    fun e he=>(provider_bytes hvalid e he).2.1,?_,provider_rows pre rs hr⟩
  intro e he
  have hb:∀b∈e.bytes,b<256:=(provider_bytes hvalid e he).2.2
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
  have hi:i∈selected pre rs:=List.mem_eraseDups.mp hi
  obtain ⟨r,_,_,_,hidx⟩:=selected_receipt hi
  obtain ⟨bytes,_,hbytes⟩:=NativeReceiptAccessIds.bytes_at hidx
  have hlt:=(List.getElem?_eq_some_iff.mp hbytes).choose
  have hcount:(selected pre rs).count i≤(selected pre rs).length:=List.count_le_length
  have hlen:=selected_length pre rs
  refine ⟨by change i<Algebra.P; omega,?_,fun b hm=>Nat.lt_trans (hb b hm) (by decide)⟩
  change (selected pre rs).count i<2013265921
  omega

theorem byte_inventory {pre : PTrie} {rs : List Receipt}
    (hvalid:∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1) :
    akeySends (providers pre rs) B_VBYTES=
      (selected pre rs).eraseDups.flatMap
        (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat)) := by
  simp only [akeySends,ite_true,providers,List.flatMap_map]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro i hi
  have hm:(⟨i,(selected pre rs).count i,((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat⟩ : AkeyE)
      ∈providers pre rs:=List.mem_map.mpr ⟨i,hi,rfl⟩
  have hn:=(provider_bytes hvalid _ hm).1
  simp only [emitAt,hn,Nat.zero_add]

end ZkFormal.NearV3.Candidates.NativeAccessKeyProviders
