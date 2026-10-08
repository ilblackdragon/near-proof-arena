import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTraffic
import ZkFormal.NearV3.Rcpt.Candidates.NativeWitnessCharge

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Near.Dsl
open NearSpec NearSpecV3

/-- Actual candidate final constraint charges record prefixes in addition to
payloads. Range/no-wrap obligations are explicit, not inferred from field casts. -/
theorem final_total_bound {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) (hr : r<tr.height t)
    (hlast : tr.cell t r SizeV3.la=1)
    (slack overhead total records : Nat)
    (hbits : SizeV3.bitsE.eval tr t r pub=(slack:Fp))
    (hovh : SizeV3.ovhE.eval tr t r pub=(overhead:Fp))
    (htot : tr.cell t r SizeV3.tot=(total:Fp))
    (hcount : tr.cell t r countTotal=(records:Fp))
    (hwrap : slack+overhead+total+4*records<ZkFormal.Algebra.P) :
    overhead+total+4*records≤8388608 := by
  have he := h.constr r hr newTotalBound (by
    apply List.mem_append_right
    simp)
  simp only [newTotalBound,eval_mul,eval_c,eval_sub,eval_k,eval_smul,
    hlast,hbits,hovh,htot,hcount] at he
  have hfield : ((slack+overhead+total+4*records:Nat):Fp)=(8388608:Nat) := by
    push_cast
    grind
  have heq := ofNat_inj hwrap (by decide) hfield
  omega

/-- Exact witness charge closes the 8 MiB bound with separately authenticated
counts while retaining the original payload-only base cap. -/
theorem counted_witness_paid (w : StateWitness) (N sourceSize payload count : Nat)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*N+4)
    (hp : witnessPayload w≤payload) (hc : witnessRecordCount w≤count)
    (hpaid : (224+w.innerBytes.length+44*N+69*w.implicit.length)+
      (payload+sourceSize)+4*count≤8388608) :
    (ZkFormal.V3.encodeSW w).length≤8388608 := by
  have hh := witness_source_charge w N sourceSize he ha ht hd
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
