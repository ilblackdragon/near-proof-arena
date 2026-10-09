import ZkFormal.NearV3.Rcpt.Candidates.SizeCountAcceptedOverhead

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3

/-- The prepared candidate closes the exact native witness bound without an
assumed overhead interpretation or an independent field no-wrap premise. -/
theorem prepared_witness_paid {p : Prep} {inner bytes : Bytes}
    (hpub : countedPreparedBytes p inner=some bytes) (hroots : Public.RootsSized p)
    {tr : Trace Fp} {t : Nat}
    (hsize : TableLocal sizeTable tr t (ZkFormal.Udr.pubOf Fp bytes))
    {vs : List NodeS3} {es : List ValE} (hn : NodeWf3 vs) (hv : ValWf es)
    (sourceSize : Nat) (hsource : sourceSize≤2^24+2^22)
    (hb : ∀ m, tableBusCount sizeTable.interactions tr t (ZkFormal.Udr.pubOf Fp bytes) B_SIZE false m=
      ([[0,(nodePayload vs:Fp),((vs.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload es:Fp),((es.filter fun v => !v.dup).length:Fp)],
        [2,(sourceSize:Fp),0]] : List (List Fp)).count m)
    (w : StateWitness) (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*p.lists.length+4)
    (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K)
    (hp : witnessPayload w≤nodePayload vs+valPayload es)
    (hc : witnessRecordCount w≤(vs.filter fun v => !v.dup).length+(es.filter fun v => !v.dup).length) :
    (ZkFormal.V3.encodeSW w).length≤8388608 := by
  have hovh := counted_prepared_ovh hpub hroots tr t 2
  have hwrap := counted_prepared_no_wrap hpub hn hv sourceSize hsource
  have hfixed : fixedOverhead p inner=224+w.innerBytes.length+44*p.lists.length+69*w.implicit.length := by
    simp [fixedOverhead,hi,hk]
  rw [hfixed] at hovh hwrap
  exact authenticated_witness_paid hsize w p.lists.length (nodePayload vs) (valPayload es)
    sourceSize _ _ he ha ht hd hp hc hb hovh hwrap

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
