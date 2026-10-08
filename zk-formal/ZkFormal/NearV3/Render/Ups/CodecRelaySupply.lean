import ZkFormal.NearV3.Render.Ups.CodecRelayValues
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.V2 ZkFormal.Chacha ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

/-- The real global SPAR balance supplies the count bound used by candidate
codec extraction. Only this candidate table's identity is needed; the removed
SPOST interaction is never assumed to exist. -/
theorem codecRelay_spar_supply {AP : AirP} {tr : Trace Fp} {pub : List Fp} {t : Nat}
    (hH : HoldsP AP pub tr) (ht : t<AP.tables.length) (hT : AP.tables[t]! = codecTable)
    (SO : SparOwn AP) (I : PubIdx AP pub Fp.ofNat)
    {Ps : List InstPub} {fwd : List (Nat×Nat)}
    (hp : I.recs B_SPAR true=(render Ps fwd).par) : CodecSparSupply tr t pub Ps fwd := by
  intro m
  have hg:=busCount_go_ge tr pub B_SPAR false m AP.tables 0 t ht
  rw [Nat.zero_add,hT] at hg
  have hb:=hH.balance B_SPAR m
  rw [busCount_send_zero SO.none,
    pubCount_zero (s:=false) (fun seg h1 h2=>by rw [SO.pub seg h1 h2];simp) _,
    I.count,hp] at hb
  unfold busCount at hb
  omega

theorem relaySchedValue_length {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22) (tau : Nat) :
    (relaySchedValue tr t tau).length<2^24 := by
  classical
  unfold relaySchedValue svOf
  split
  · rename_i h
    obtain ⟨hf,hF,_⟩:=Classical.choose_spec h
    obtain ⟨_,hN,_⟩:=Codec.codec_block hl hh hf hF
    simp only [List.length_map,List.length_range]
    omega
  · simp
end ZkFormal.NearV3.Render.UpsRelay
