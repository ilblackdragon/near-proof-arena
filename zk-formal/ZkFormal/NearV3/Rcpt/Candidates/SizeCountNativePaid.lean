import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPreparedPaid
import ZkFormal.NearV3.Rcpt.Candidates.NativePayloadOwnership

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 Assembly Link3

/-- The prepared candidate pays the executable witness stores through actual
uniqueness and SHA ownership, with no separate payload or record-count bound. -/
theorem prepared_native_witness_paid {p : Prep} {inner bytes : Bytes}
    (hpub : countedPreparedBytes p inner=some bytes) (hroots : Public.RootsSized p)
    {tr : Trace Fp} {t : Nat}
    (hsize : TableLocal sizeTable tr t (ZkFormal.Udr.pubOf Fp bytes))
    (k : WalkD0) (x : ExtV3)
    {us : List UniqE} {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (hn : NodeWf3 x.nodes) (hh : HeadWf x.heads) (hv : ValWf x.values)
    (hu : UniqWf us) (hpar : ParentBal x.nodes x.heads)
    (hvpar : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    (hheads : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau)
    (sourceSize : Nat) (hsource : sourceSize≤2^24+2^22)
    (hb : ∀ m, tableBusCount sizeTable.interactions tr t (ZkFormal.Udr.pubOf Fp bytes) B_SIZE false m=
      ([[0,(nodePayload x.nodes:Fp),((x.nodes.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload x.values:Fp),((x.values.filter fun v => !v.dup).length:Fp)],
        [2,(sourceSize:Fp),0]] : List (List Fp)).count m)
    (he : (stateWitnessOfV3 k x).epochId.length=32) (ha : (stateWitnessOfV3 k x).appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions (stateWitnessOfV3 k x),t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry (stateWitnessOfV3 k x).entries).length=sourceSize+44*p.lists.length+4)
    (hi : (stateWitnessOfV3 k x).innerBytes=inner) (hk : (stateWitnessOfV3 k x).implicit.length=p.hdr.K)
    : (ZkFormal.V3.encodeSW (stateWitnessOfV3 k x)).length≤8388608 := by
  have hp := native_payload_from_uniqueness k x hn hh hv hu hpar hvpar H hD hDup hEnt hheads
  have hc := native_count_from_uniqueness k x hn hh hv hu hpar hvpar H hD hDup hEnt hheads
  exact prepared_witness_paid hpub hroots hsize hn hv sourceSize hsource hb
    (stateWitnessOfV3 k x) he ha ht hd hi hk hp hc

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
