import ZkFormal.NearV3.Candidates.UniqueSourceSoundBlockTraffic
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNoWrap
namespace ZkFormal.NearV3.Candidates.UniqueSourceNoWrap
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates
open UniqueSourceSoundShadow

theorem charge_le (bs : List SrcpB) :
    UniqueSourceCharge.size bs≤(bs.map fun B=>B.L+33*B.path.length).sum+44*bs.length := by
  induction bs with
  | nil => exact Nat.le_refl _
  | cons B bs ih =>
    cases hd : B.dup <;>
      simp only [UniqueSourceCharge.size,UniqueSourceCharge.sizeStep,List.map_cons,List.sum_cons,
        List.length_cons,hd,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

/-- Physical row caps and actual RCL multiplicity rule out source wraparound;
this bound does not assume the final SIZE inequality. -/
theorem source_cap {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (UniqueSourceCharge.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : DedupProof.BlockChain (shadow src) ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q=>rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q=>rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m) :
    UniqueSourceCharge.size bs≤45*2^24+2^22 := by
  have hb:=SizeCount.source_charge_cap (old_local hsrc) hrcpt hs hr (by
    intro m
    rw [UniqueSourceSoundSemantic.messages src ts pub B_RCL false (by decide)]
    exact hbalance m)
  have hh : src.height ts≤2^24 := Nat.pow_le_pow_right (by decide) hsrc.log_le
  have hrows:=hs.rows
  have hend : 0<se ∧ se≤src.height ts := hs.bound
  have hn:=DedupRender.R_accounting bs
  have hc:=charge_le bs
  omega

theorem source_cast (bs : List SrcpB) (h : UniqueSourceCharge.size bs≤45*2^24+2^22) :
    (Fp.ofNat (UniqueSourceCharge.size bs)).toNat=UniqueSourceCharge.size bs := by
  have hp : UniqueSourceCharge.size bs<P := by unfold P;omega
  simpa only [Fp.toNat_ofNat] using Nat.mod_eq_of_lt hp

/-- Node/value payloads, all record headers, corrected source and public overhead
fit below the field modulus using unchanged physical row caps alone. -/
theorem totals_no_wrap {vs : List NodeS3} {es : List ValE}
    (hn : NodeWf3 vs) (hv : ValWf es) (sourceSize overhead : Nat)
    (hs : sourceSize≤45*2^24+2^22) (ho : overhead≤8388608) :
    overhead+SizeCount.nodePayload vs+SizeCount.valPayload es+sourceSize+
      4*((vs.filter fun v=>!v.dup).length+(es.filter fun v=>!v.dup).length)+2^24≤P := by
  obtain ⟨hnp,hnc⟩:=SizeCount.node_charge_bounds hn
  obtain ⟨hvp,hvc⟩:=SizeCount.val_charge_bounds hv
  unfold P
  omega
end ZkFormal.NearV3.Candidates.UniqueSourceNoWrap
