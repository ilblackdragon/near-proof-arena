import ZkFormal.NearV3.Render.Ups.CodecRelayIds
import ZkFormal.NearV3.Render.Ups.RelayFreshSha
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

noncomputable def relaySchedValue (tr : Trace Fp) (t tau : Nat) : NearSpec.Bytes :=
  (svOf tr t tau).map UInt8.ofNat

def relayTaus (tr : Trace Fp) (t : Nat) : List Nat :=
  (codecFirstRows tr t).map fun f=>Chacha.cv tr t f Codec.tau

theorem codecRelay_svOf_block {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {f : Nat}
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Codec.kF=1) :
    svOf tr t (Chacha.cv tr t f Codec.tau) =
      (List.range (37+24*Chacha.cv tr t f Codec.NN)).map fun p=>Chacha.cv tr t (f+p) Codec.bpost := by
  classical
  have hex : ∃g,g<tr.height t ∧ Chacha.cv tr t g Codec.kF=1 ∧
      Chacha.cv tr t g Codec.tau=Chacha.cv tr t f Codec.tau := ⟨f,hf,hF,rfl⟩
  unfold svOf
  rw [dif_pos hex]
  obtain ⟨hg,hG,ht⟩:=Classical.choose_spec hex
  have he:=codecRelay_block_unique hl hh hs hn hg hG hf hF ht
  rw [he]

theorem codecRelay_postValue {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {f : Nat}
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Codec.kF=1) :
    codecPostBytes tr t f=relaySchedValue tr t (Chacha.cv tr t f Codec.tau) := by
  unfold relaySchedValue
  rw [codecRelay_svOf_block hl hh hs hn hf hF,List.map_map]
  exact (codecRelayBlock_state hl hh hf hF).symm

private theorem relayBlock_exact {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : Chacha.cv tr t f Codec.kF=1) :
    codecRelayBlock tr t f (37+24*Chacha.cv tr t f Codec.NN) pub =
      (relayValueMsgs (Chacha.cv tr t f Codec.tau) (codecPostBytes tr t f)).map Msg.toFp := by
  change codecRelayBlock tr t f (37+24*ZkFormal.Near.cv tr t f Codec.NN) pub =
    (relayValueMsgs (ZkFormal.Near.cv tr t f Codec.tau) (codecPostBytes tr t f)).map Msg.toFp
  rw [codecRelayBlock_exact hl hh hf hF]
  simp only [relayValueMsgs,codecPostBytes_length hl hh hf hF,List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [codecPostBytes_getD hl hh hf hF (List.mem_range.mp hp)]
  rfl

theorem codecRelay_inventory {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) :
    (codecRelayMsgs tr t pub).Perm
      (((relayTaus tr t).flatMap fun tau=>relayValueMsgs tau (relaySchedValue tr t tau)).map Msg.toFp) := by
  have hp:=codecRelayMsgs_blocks hl hh
  rw [relayTaus,List.flatMap_map,List.map_flatMap]
  have he : ((codecFirstRows tr t).flatMap fun f=>
      codecRelayBlock tr t f (37+24*Chacha.cv tr t f Codec.NN) pub)=
      ((codecFirstRows tr t).flatMap fun f=>
        (relayValueMsgs (Chacha.cv tr t f Codec.tau)
          (relaySchedValue tr t (Chacha.cv tr t f Codec.tau))).map Msg.toFp) := by
    apply UpsRows.flatMap_congr'
    intro f hf
    have hf' : f<tr.height t ∧ Chacha.cv tr t f Codec.kF=1 := by
      simpa [codecFirstRows] using hf
    rw [relayBlock_exact hl hh hf'.1 hf'.2,codecRelay_postValue hl hh hs hn hf'.1 hf'.2]
  exact he ▸ hp

theorem relayTaus_bound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length≤32) : ∀tau∈relayTaus tr t,tau<32 := by
  intro tau ht
  obtain ⟨f,hf,rfl⟩:=List.mem_map.mp ht
  have hf' : f<tr.height t ∧ Chacha.cv tr t f Codec.kF=1 := by simpa [codecFirstRows] using hf
  have := (codecRelay_first_par hl hh hs (by omega) hf'.1 hf'.2).1
  omega
end ZkFormal.NearV3.Render.UpsRelay
