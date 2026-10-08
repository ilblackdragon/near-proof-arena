import ZkFormal.NearV3.Assembly.SchedulerNativeDigests
import ZkFormal.NearV3.Sched.View.CodecState

namespace ZkFormal.NearV3.Assembly
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha
namespace CodecDigest

private theorem state_hash_suffix (s : Bandwidth.State) (hs : s.sanityHash.length=32) :
    s.encode.drop (s.encode.length-32)=s.sanityHash := by
  unfold Bandwidth.State.encode
  rw [List.length_append,hs,Nat.add_sub_cancel,List.drop_left]

/-- Equality of actual scheduler state bytes pins the final 32 hash bytes,
without requiring allowance-list identity or any SHA injectivity premise. -/
theorem state_hash_eq {a b : Bandwidth.State} (ha : a.sanityHash.length=32)
    (hb : b.sanityHash.length=32) (he : a.encode=b.encode) : a.sanityHash=b.sanityHash := by
  rw [←state_hash_suffix a ha,←state_hash_suffix b hb,he]

/-- The actual codec digest registers equal the same accepted upsert's native
sanity hash as soon as its serialized post bytes are installed. -/
theorem native_codec_hash {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hl : Sched.Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Sched.Codec.kF=1)
    {u : SchedulerUpsertWitness} (hv : u.Valid)
    (hp : Sched.Codec.rowBytes tr t Sched.Codec.bpost f
      (37+24*Chacha.cv tr t f Sched.Codec.NN)=u.value) :
    ∃input, input.length=64 ∧ schedulerWitnessSanity u=some input ∧
      (List.range 32).map (fun j=>UInt8.ofNat (Chacha.cv tr t
        (f+5+24*Chacha.cv tr t f Sched.Codec.NN) (Sched.Codec.reg j)))=sha256 input := by
  obtain ⟨input,hi,hlen,links,hstate⟩:=SchedulerUpsertWitness.sanity hv
  refine ⟨input,hlen,hi,?_⟩
  have he:=Sched.Codec.codec_post_encode hl hh hf hF
  rw [hp,hstate] at he
  exact (state_hash_eq (by exact ArenaCore.sha256_length _)
    (by simp) he).symm

end CodecDigest
end ZkFormal.NearV3.Assembly
