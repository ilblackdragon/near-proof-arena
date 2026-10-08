import ZkFormal.NearV3.Assembly.SchedulerCodecConsumer
import ZkFormal.NearV3.Render.Ups.CodecRelaySanity

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha

/-- Full original Codec DIGEST traffic at one physical row has exactly its
single declared digest interaction, not a selected subset of interactions. -/
theorem codec_digest_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    Near.rowTraffic Sched.Codec.interactions tr t r pub B_DIGEST false=
      List.replicate ((Sched.Codec.interactions[3]!).multNat tr t r pub)
        ((Sched.Codec.interactions[3]!).msgVal tr t r pub) := by
  simp [Near.rowTraffic,Sched.Codec.interactions,B_BYTES,B_VBYTES,B_DIGEST,Sched.B_SPOST,
    Sched.B_SPLEN,Sched.B_SPAR,Sched.B_SDL,Sched.B_SPUBB,Sched.B_SOP,Sched.B_SFIN,Sched.B_SDG,
    Sched.B_SA0,Sched.B_SCMP,Sched.B_S0F]

/-- Native post-byte installation discharges the complete physical sanity
DIGEST row using the same job and actual transition identifier. -/
theorem native_codec_row_traffic {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hl : Sched.Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Sched.Codec.kF=1)
    {u : SchedulerUpsertWitness} (hv : u.Valid)
    (hp : Sched.Codec.rowBytes tr t Sched.Codec.bpost f
      (37+24*Chacha.cv tr t f Sched.Codec.NN)=u.value) :
    Near.rowTraffic Sched.Codec.interactions tr t
      (f+5+24*Chacha.cv tr t f Sched.Codec.NN) pub B_DIGEST false=
      (Sha.Gen.expectedDigests [schedulerSanityJob (Chacha.cv tr t f Sched.Codec.tau) u]).map Msg.toFp := by
  obtain ⟨hm,he⟩:=native_codec_consumer hl hh hf hF hv hp
  rw [codec_digest_row,hm]
  exact he.symm

end ZkFormal.NearV3.Assembly.CodecDigest
