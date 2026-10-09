import ZkFormal.NearV3.Assembly.SchedulerCodecDigest

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha

/-- One installed native scheduler state supplies exactly the corresponding
physical codec sanity DIGEST lookup, with multiplicity one and its actual tau.
The remaining whole-table step is block enumeration and native installation. -/
theorem native_codec_consumer {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hl : Sched.Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Sched.Codec.kF=1)
    {u : SchedulerUpsertWitness} (hv : u.Valid)
    (hp : Sched.Codec.rowBytes tr t Sched.Codec.bpost f
      (37+24*Chacha.cv tr t f Sched.Codec.NN)=u.value) :
    (Sched.Codec.interactions[3]!).multNat tr t
      (f+5+24*Chacha.cv tr t f Sched.Codec.NN) pub=1 ∧
    (Sha.Gen.expectedDigests [schedulerSanityJob (Chacha.cv tr t f Sched.Codec.tau) u]).map Msg.toFp=
      [(Sched.Codec.interactions[3]!).msgVal tr t
        (f+5+24*Chacha.cv tr t f Sched.Codec.NN) pub] := by
  obtain ⟨_,_,_,_,hm,hmsg,hdig⟩:=Sched.Codec.codec_post hl hh hf hF
  refine ⟨hm,?_⟩
  obtain ⟨input,hlen,hi,hhsh⟩:=native_codec_hash hl hh hf hF hv hp
  have hb : ∀j,j<32→Chacha.cv tr t (f+5+24*Chacha.cv tr t f Sched.Codec.NN)
      (Sched.Codec.reg j)<256 := by
    intro j hj
    have he:=Sched.Codec.enc_rows hl hh hf hF (5+24*Chacha.cv tr t f Sched.Codec.NN+j) (by omega)
    have bb:=(Sched.Codec.bytes hl he.1 he.2.1).2.1
    rw [show f+(5+24*Chacha.cv tr t f Sched.Codec.NN+j)=
      f+5+24*Chacha.cv tr t f Sched.Codec.NN+j by omega,hdig j hj] at bb
    exact bb
  have he:=congrArg (List.map UInt8.toNat) hhsh
  have hreg : (List.range 32).map (fun j=>Chacha.cv tr t
      (f+5+24*Chacha.cv tr t f Sched.Codec.NN) (Sched.Codec.reg j))=
      (sha256 input).map UInt8.toNat := by
    rw [←he,List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_def,UInt8.toNat_ofNat',Nat.mod_eq_of_lt (hb j (List.mem_range.mp hj))]
  rw [hmsg,hreg]
  simp only [Sha.Gen.expectedDigests,schedulerSanityJob,hi,List.filter_cons_of_pos,List.filter_nil,
    List.map_cons,List.map_nil,List.length_map,Option.getD_some,hlen,nativeBytes_roundtrip]
  rfl

end ZkFormal.NearV3.Assembly.CodecDigest
