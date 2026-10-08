import ZkFormal.NearV3.Render.Ups.CodecRelaySupply
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueLength
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

private theorem splenCount (tr : Trace Fp) (t : Nat) (pub : List Fp) (m : List Fp) :
    tableBusCount codecTable.interactions tr t pub ZkFormal.NearV3.B_SPLEN true m =
    tableBusCount Codec.interactions tr t pub ZkFormal.NearV3.B_SPLEN true m := by
  rw [tableBusCount_eq,tableBusCount_eq]
  congr 1

/-- Every actual candidate SPLEN send describes the same decoded value used by
its complete fresh SHA relay inventory. -/
theorem codecRelay_splen_value {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {m : List Fp}
    (hm : 0<tableBusCount codecTable.interactions tr t pub ZkFormal.NearV3.B_SPLEN true m) :
    ∃tau,tau<P ∧ m=[tau,(relaySchedValue tr t tau).length].map Fp.ofNat := by
  rw [splenCount] at hm
  obtain ⟨f,hf,i,hi,hb,_,hmsg,hg⟩:=Chacha.exists_of_tableBusCount (by omega :
    tableBusCount Codec.interactions tr t pub ZkFormal.NearV3.B_SPLEN true m≠0)
  have he:=codec_splen_i hi hb
  subst i
  rw [Mem.multNat_c (by rw [Codec.i5_def])] at hg
  have hF : Chacha.cv tr t f Codec.kF=1 := by
    by_cases he : Chacha.cv tr t f Codec.kF=1
    · exact he
    · simp [he] at hg
  obtain ⟨_,_,_,hmsg5,_⟩:=Codec.codec_first hl hh hf hF
  refine ⟨Chacha.cv tr t f Codec.tau,Chacha.cv_lt _ _,?_⟩
  rw [←hmsg,hmsg5]
  unfold relaySchedValue
  rw [codecRelay_svOf_block hl hh hs hn hf hF,List.length_map,List.length_map,List.length_range]

/-- Global SPLEN ownership/balance needs only supply all actual UPS receives.
No separate value-byte, value-length, SPOST or fresh-digest assumption remains. -/
theorem codecRelay_schedLength {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) {v : List UpsSeg}
    (hbal : ∀m,((upsTraffic v).recvs ZkFormal.NearV3.B_SPLEN|>.map Msg.toFp).count m ≤
      tableBusCount codecTable.interactions tr t pub ZkFormal.NearV3.B_SPLEN true m) :
    Extract.SchedLength v (relaySchedValue tr t) := by
  refine ⟨?_,relaySchedValue_length hl hh⟩
  intro m hm
  have hc : 0<(((upsTraffic v).recvs ZkFormal.NearV3.B_SPLEN).map Msg.toFp).count m.toFp :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  exact codecRelay_splen_value hl hh hs hn (by have := hbal m.toFp;omega)
end ZkFormal.NearV3.Render.UpsRelay
