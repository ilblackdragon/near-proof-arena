import ZkFormal.NearV3.Assembly.RcptCandidateRepairedSound
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges
import ZkFormal.NearV3.Assembly.RoutingBoundedPrep

namespace ZkFormal.NearV3.Assembly.ReceiptPublicAdmission
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3

/-- Full little-endian decoding always returns the low bytes, without an
unjustified natural-size premise. -/
theorem leNat_leN_mod (w n : Nat) : NearSpec.leNat (NearSpec.leN w n)=n%256^w := by
  induction w generalizing n with
  | zero => simp [NearSpec.leN,NearSpec.leNat,Nat.mod_one]
  | succ w ih =>
    have h8 : (UInt8.ofNat (n%256)).toNat=n%256%256 := rfl
    rw [NearSpec.leN,NearSpec.leNat,ih,h8,Nat.mod_mod,Nat.pow_succ,
      Nat.mul_comm (256^w),Nat.mod_mul]

theorem read4_u32_mod (read : Nat→Fp) (n : Nat)
    (hr : ∀ k,k<4→read k=Public.byteF ((NearSpec.u32 n).getD k 0)) :
    V2.leNat ((List.range 4).map (fun k=>PubVal.val (read k)))=n%256^4 := by
  have he : (List.range 4).map (fun k=>PubVal.val (read k))=(NearSpec.u32 n).map UInt8.toNat := by
    apply List.ext_getElem (by simp [NearSpec.u32,NearSpec.leN_length])
    intro k hk hk'
    have h4 : k<4 := by simpa using hk
    simp only [List.getElem_map,List.getElem_range]
    rw [hr k h4,Public.byteF_val,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [NearSpec.u32,NearSpec.leN_length] using h4),Option.getD_some]
  rw [he,Public.leNat_bytes]
  exact leNat_leN_mod 4 n

theorem public_u32_mod (pub : List Fp) (off n : Nat)
    (hr : ∀ k,k<4→pub.getD (off+k) 0=Public.byteF ((NearSpec.u32 n).getD k 0)) :
    leN' (pubBytes pub off 4)=n%256^4 := by
  have he : pubBytes pub off 4=(NearSpec.u32 n).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes,NearSpec.u32,NearSpec.leN_length])
    intro k hk hk'
    have h4 : k<4 := by simpa [pubBytes] using hk
    simp only [pubBytes,List.getElem_map,List.getElem_range,pubNat]
    rw [hr k h4]
    change PubVal.val (Public.byteF ((NearSpec.u32 n).getD k 0))=_
    rw [Public.byteF_val,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [NearSpec.u32,NearSpec.leN_length] using h4),Option.getD_some]
  rw [he]
  simp only [leN',List.map_map,Function.comp_def,UInt8.ofNat_toNat,List.map_id_fun]
  exact leNat_leN_mod 4 n

def bodySegment : PubSeg := Public.descriptor Public.bodyPlan 202 2

theorem body_segment_member : bodySegment∈Public.preparedSegments := by
  exact List.mem_of_getElem? (show Public.preparedSegments[2]?=some bodySegment from rfl)

theorem body_segment_count (p : Prep) (overhead : Nat) (hr : Public.RootsSized p) :
    bodySegment.count (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))=
      (p.body.length-8)%256^4 := by
  unfold PubSeg.count
  apply read4_u32_mod
  intro k hk
  rw [Public.pub_getD]
  change Public.byteF ((Public.preparedBytes p overhead).getD (202+8*2+k) 0)=_
  rw [←Public.headerBytes_length p overhead hr]
  unfold Public.preparedBytes
  rw [Public.encode_count _ _ (by rw [Public.preparedBlocks_length];decide) hk]
  change Public.byteF ((NearSpec.u32 (Public.bodyPayload p.body).length).getD k 0)=_
  rw [Public.bodyPayload_length]

/-- Actual public segment admission bounds the decoded body length. This does
not mistake pubFit for a bound on the entire public byte array. -/
theorem body_range_of_fit {AP : AirP} (hs : AP.pubSegs=Public.preparedSegments)
    (hmax : AP.maxPub+8<Algebra.P) (p : Prep) (overhead : Nat) (hr : Public.RootsSized p)
    (hf : pubFit AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))=true) :
    leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_BLEN 4)<Algebra.P := by
  have fit := List.all_eq_true.mp hf bodySegment (hs.symm ▸ body_segment_member)
  simp only [PubSeg.fits,Bool.and_eq_true,decide_eq_true_eq] at fit
  have hc := body_segment_count p overhead hr
  have hw : bodySegment.width=1 := rfl
  rw [hw,Nat.mul_one,hc] at fit
  have hd : leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_BLEN 4)=
      p.body.length%256^4 := by
    apply public_u32_mod
    intro k hk
    rw [Public.pub_getD,Public.prepared_header p overhead hr (by unfold PH_BLEN;omega),
      Public.header_body_length p overhead hr hk]
  rw [hd]
  by_cases hb : p.body.length<8
  · rw [Nat.mod_eq_of_lt (by omega)];unfold Algebra.P;omega
  · have hsub : p.body.length=p.body.length-8+8 := by omega
    rw [hsub,Nat.add_mod]
    have hm : 8%256^4=8 := by decide
    rw [hm,Nat.mod_eq_of_lt (by unfold Algebra.P at hmax;omega)]
    omega

/-- Canonical native receipt count suffices for its exact packed header field. -/
theorem count_range (p : Prep) (overhead : Nat) (hr : Public.RootsSized p)
    (hn : p.hdr.n<Algebra.P) :
    leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_N 4)<Algebra.P := by
  have he : leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_N 4)=
      p.hdr.n%256^4 := by
    apply public_u32_mod
    intro k hk
    rw [Public.pub_getD,Public.prepared_header p overhead hr (by unfold PH_N;omega),
      RcptV3Proof.header_receipt_count p overhead hk]
  rw [he]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn

/-- Both public ranges from native preparation and actual public-segment
admission; no extra total-public-byte or body-size hypothesis is required. -/
theorem prepared_ranges {AP : AirP} (hs : AP.pubSegs=Public.preparedSegments)
    (hmax : AP.maxPub+8<Algebra.P) {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat)
    (hf : pubFit AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))=true) :
    ReceiptCandidateProof.ReceiptPublicRanges
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) := by
  have hr := prepD0_roots hp
  exact ⟨count_range p overhead hr (RcptV3Proof.prepD0_count_bound hp).2,
    body_range_of_fit hs hmax p overhead hr hf⟩

/-- The bounded routing representation changes neither native count nor header
roots. Its own admitted public body descriptor yields the same range proof. -/
theorem bounded_prepared_ranges {AP : AirP} (hs : AP.pubSegs=Public.preparedSegments)
    (hmax : AP.maxPub+8<Algebra.P) {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (l : Layout) (own overhead : Nat)
    (hf : pubFit AP (ZkFormal.Udr.pubOf Fp
      (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p l own) overhead))=true) :
    ReceiptCandidateProof.ReceiptPublicRanges (ZkFormal.Udr.pubOf Fp
      (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p l own) overhead)) := by
  have hr : Public.RootsSized (RoutingBoundedLayout.boundedPrep p l own) := by
    simpa only [Public.RootsSized,RoutingBoundedLayout.boundedPrep] using prepD0_roots hp
  exact ⟨count_range _ overhead hr (RcptV3Proof.prepD0_count_bound hp).2,
    body_range_of_fit hs hmax _ overhead hr hf⟩

/-- Preserve interoperability with the unchanged receipt/source link interface. -/
theorem ranges_original {pub : List Fp} (h : ReceiptCandidateProof.ReceiptPublicRanges pub) :
    RcptV3Proof.ReceiptPublicRanges pub := ⟨h.count,h.body⟩

theorem ranges_candidate {pub : List Fp} (h : RcptV3Proof.ReceiptPublicRanges pub) :
    ReceiptCandidateProof.ReceiptPublicRanges pub := ⟨h.count,h.body⟩

end ZkFormal.NearV3.Assembly.ReceiptPublicAdmission
