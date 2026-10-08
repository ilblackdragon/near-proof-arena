import ZkFormal.NearV3.Render.Ups.CodecRelayRows
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched UpsGen

/-- Ordinary scheduler state recovered from the codec block. -/
def codecPostBytes (tr : Trace Fp) (t f : Nat) : NearSpec.Bytes :=
  NearSpec.Bandwidth.State.encode ⟨Codec.postLinks tr t f (cv tr t f Codec.NN),
    (List.range 32).map fun j=>UInt8.ofNat (cv tr t (f+5+24*cv tr t f Codec.NN) (Codec.reg j))⟩

theorem codecPostBytes_length {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hL : Codec.CLocal tr t pub) (hH : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : cv tr t f Codec.kF=1) :
    (codecPostBytes tr t f).length=37+24*cv tr t f Codec.NN := by
  have h:=congrArg List.length (codecRelayBlock_state hL hH hf hF)
  simpa only [codecPostBytes,List.length_map,List.length_range] using h.symm

theorem codecPostBytes_getD {tr : Trace Fp} {t f p : Nat} {pub : List Fp}
    (hL : Codec.CLocal tr t pub) (hH : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : cv tr t f Codec.kF=1)
    (hp : p<37+24*cv tr t f Codec.NN) :
    ((codecPostBytes tr t f).map UInt8.toNat).getD p 0=cv tr t (f+p) Codec.bpost := by
  have he:=codecRelayBlock_state hL hH hf hF
  change _=codecPostBytes tr t f at he
  rw [←he,List.map_map]
  rw [Codec.getD_map_range _ _ hp]
  have henc:=Codec.enc_rows hL hH hf hF p (by
    change p<5+24*cv tr t f Codec.NN+32
    omega)
  have hb:=(Codec.bytes hL henc.1 henc.2.1).2.1
  change cv tr t (f+p) Codec.bpost<256 at hb
  exact UInt8.toNat_ofNat_of_lt' hb

/-- The complete physical relay block is exactly the fresh SHA job's bytes. -/
theorem codecRelayBlock_value {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hL : Codec.CLocal tr t pub) (hH : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : cv tr t f Codec.kF=1) :
    codecRelayBlock tr t f (37+24*cv tr t f Codec.NN) pub=
      (shaByteMsgs ⟨Assembly.upsertJobId (cv tr t f Codec.tau) 0,
        (codecPostBytes tr t f).map UInt8.toNat,true⟩).map Msg.toFp := by
  rw [codecRelayBlock_exact hL hH hf hF]
  simp only [shaByteMsgs,List.length_map,codecPostBytes_length hL hH hf hF,List.map_map]
  apply List.map_congr_left
  intro p hp
  have hp:=List.mem_range.mp hp
  simp only [Function.comp_apply]
  rw [codecPostBytes_getD hL hH hf hF hp]
  simp only [Function.comp_apply,Msg.toFp,List.map_cons,List.map_nil]
  have hm (n : Nat) : Fp.ofNat (n%P)=Fp.ofNat n := Fp.ext (by simp [Fp.toNat_ofNat,Nat.mod_mod])
  simp only [hm]
end ZkFormal.NearV3.Render.UpsRelay
