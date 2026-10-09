import ZkFormal.NearV3.Rcpt.Extract.V.PrepCount
import ZkFormal.NearV3.Rcpt.Extract.V.TableWellformed
import ZkFormal.NearV3.Public.ImplicitCount

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3

/-- Receipt count occupies the second u32 of the actual prepared header. -/
theorem header_receipt_count (p : Prep) (overhead : Nat) {k : Nat} (hk : k<4) :
    (Public.headerBytes p overhead).getD (PH_N+k) 0=(NearSpec.u32 p.hdr.n).getD k 0 := by
  simp only [Public.headerBytes,PrepHdr.encode,List.append_assoc]
  rw [show PH_N+k=(NearSpec.borshBytes prepTag).length+(4+k) by
    rw [Public.prep_tag_prefix_length]; unfold PH_N; omega]
  rw [Public.getD_right]
  rw [show 4+k=(NearSpec.u32 p.hdr.K).length+k by simp [NearSpec.u32,NearSpec.leN_length]]
  rw [Public.getD_right]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa [NearSpec.u32,NearSpec.leN_length] using hk)]

/-- Exact receipt-view decoding of an actual four-byte public u32 field. -/
theorem public_u32_native (pub : List Fp) (off n : Nat) (hn : n<256^4)
    (hr : ∀ k,k<4 → pub.getD (off+k) 0=Public.byteF ((NearSpec.u32 n).getD k 0)) :
    leN' (pubBytes pub off 4)=n := by
  have hm : pubBytes pub off 4=(NearSpec.u32 n).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes,NearSpec.u32,NearSpec.leN_length])
    intro k hk hk'
    have hk4 : k<4 := by simpa [pubBytes] using hk
    simp only [pubBytes,List.getElem_map,List.getElem_range,pubNat]
    rw [hr k hk4]
    change ZkFormal.V2.PubVal.val (Public.byteF ((NearSpec.u32 n).getD k 0))=_
    rw [Public.byteF_val]
    simp only [List.getD,List.getElem?_eq_getElem (by simpa only [List.length_map] using hk'),Option.getD_some]
  rw [hm]
  simp only [leN',List.map_map,Function.comp_def,UInt8.ofNat_toNat,List.map_id_fun]
  exact NearSpec.leNat_leN 4 n hn

/-- Exact packed count binding uses the real native successful-prep bound. -/
theorem prepared_receipt_count {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat) (hr : Public.RootsSized p) :
    leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_N 4)=p.hdr.n := by
  apply public_u32_native
  · have := (prepD0_count_bound hp).1; omega
  · intro k hk
    rw [Public.pub_getD,Public.prepared_header p overhead hr (by unfold PH_N; omega),
      header_receipt_count p overhead hk]

/-- Both necessary public ranges follow from real native preparation and the
actual packed-statement size bound. No extra native receipt-count restriction. -/
theorem prepared_receipt_ranges {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat) (hr : Public.RootsSized p)
    (hsize : (Public.preparedBytes p overhead).length<Algebra.P) :
    ReceiptPublicRanges (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) := by
  constructor
  · rw [prepared_receipt_count hp overhead hr]
    exact (prepD0_count_bound hp).2
  · have hb := Public.prepared_body_size_le p overhead hr
    have hv : leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_BLEN 4)=p.body.length := by
      apply public_u32_native
      · unfold Algebra.P at hsize; omega
      · intro k hk
        rw [Public.pub_getD,Public.prepared_header p overhead hr (by unfold PH_BLEN; omega),
          Public.header_body_length p overhead hr hk]
    rw [hv]
    omega

/-- Complete receipt wellformedness from actual local AIR bound to a successful
native prepared public statement. Its real encoded size, not a new native
restriction, discharges field-total admissibility. -/
theorem extract_prepared_wellformed {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat)
    (hsize : (Public.preparedBytes p overhead).length<Algebra.P)
    (tr : Trace Fp) (tt : Nat)
    (hL : TableLocal RcptV3.table tr tt (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))) :
    ∃ ls,RcptV3Wf (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) ls :=
  extract_wellformed hL (prepared_receipt_ranges hp overhead (Assembly.prepD0_roots hp) hsize)

end ZkFormal.NearV3.RcptV3Proof
