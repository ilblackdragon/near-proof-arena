import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNoWrap
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountAccumulator

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3

/-- Claim/preparation-determined overhead; private stored-record prefixes are
charged separately by authenticated SIZE counts. -/
def fixedOverhead (p : Prep) (chunkInner : Bytes) : Nat :=
  224+chunkInner.length+44*p.lists.length+69*p.hdr.K

/-- Isolated candidate public constructor. Its bound prevents a large fixed
header from being accepted through a field alias. Native completeness is below. -/
def countedPreparedBytes (p : Prep) (chunkInner : Bytes) : Option Bytes :=
  if fixedOverhead p chunkInner≤8388608 then
    some (Public.preparedBytes p (fixedOverhead p chunkInner)) else none

theorem counted_prepared_bound {p : Prep} {inner bytes : Bytes}
    (h : countedPreparedBytes p inner=some bytes) :
    fixedOverhead p inner≤8388608 ∧ bytes=Public.preparedBytes p (fixedOverhead p inner) := by
  unfold countedPreparedBytes at h
  split at h
  · exact ⟨by assumption,(Option.some.inj h).symm⟩
  · cases h

/-- Any already-valid constructed witness with the exact dictionary accounting
passes the candidate overhead check. This check does not consume payload budget. -/
theorem counted_prepared_complete (p : Prep) (inner : Bytes) (w : StateWitness)
    (sourceSize : Nat) (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*p.lists.length+4)
    (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K)
    (hw : (ZkFormal.V3.encodeSW w).length≤8388608) :
    countedPreparedBytes p inner=some (Public.preparedBytes p (fixedOverhead p inner)) := by
  have hc := witness_source_charge w p.lists.length sourceSize he ha ht hd
  have ho : fixedOverhead p inner≤8388608 := by
    unfold fixedOverhead
    rw [hi,hk] at hc
    omega
  simp [countedPreparedBytes,ho]

/-- Successful candidate public construction binds the AIR overhead to its exact
natural value, with no external u32 or no-wrap assumption. -/
theorem counted_prepared_ovh {p : Prep} {inner bytes : Bytes}
    (h : countedPreparedBytes p inner=some bytes) (hr : Public.RootsSized p)
    (tr : Trace Fp) (t r : Nat) :
    SizeV3.ovhE.eval tr t r (ZkFormal.Udr.pubOf Fp bytes)=(fixedOverhead p inner:Fp) := by
  obtain ⟨hb,rfl⟩ := counted_prepared_bound h
  rw [SizeProof.eval_ovh,Public.prepared_ovhNat p _ hr (by omega)]

theorem counted_prepared_no_wrap {p : Prep} {inner bytes : Bytes}
    (h : countedPreparedBytes p inner=some bytes)
    {vs : List NodeS3} {es : List ValE} (hn : NodeWf3 vs) (hv : ValWf es)
    (sourceSize : Nat) (hs : sourceSize≤2^24+2^22) :
    fixedOverhead p inner+nodePayload vs+valPayload es+sourceSize+
      4*((vs.filter fun v => !v.dup).length+(es.filter fun v => !v.dup).length)+2^24≤ZkFormal.Algebra.P :=
  totals_no_wrap hn hv sourceSize _ hs (counted_prepared_bound h).1

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
