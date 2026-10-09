import ZkFormal.NearV3.Render.Ups.CodecRelayLength
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 Sched

/-- The unchanged SPLEN channel has one sending table and no public sender.
Unlike the old scheduler interface, this owns no SPOST interaction. -/
structure CodecLengthOwn (AP : AirP) (tc : Nat) : Prop where
  lt : tc<AP.tables.length
  tab : AP.tables[tc]! = codecTable
  only : ∀t,t<AP.tables.length → t≠tc → ∀i∈AP.tables[t]!.interactions,
    i.bus=ZkFormal.NearV3.B_SPLEN → i.send=false
  pub : ∀seg∈AP.pubSegs,seg.bus=ZkFormal.NearV3.B_SPLEN → seg.send=false

/-- SPLEN binding is derived from actual global balance and physical UPS
traffic. No assumed byte-family equality, length bound or SPOST ownership. -/
theorem codecRelay_schedLength_of_holds {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH : HoldsP AP pub tr) {tc tu : Nat} (O : CodecLengthOwn AP tc)
    (hu : tu<AP.tables.length) {v : List UpsSeg}
    (ht : TableTraffic AP.tables[tu]!.interactions tr tu pub (upsTraffic v))
    (SO : SparOwn AP) (I : PubIdx AP pub Fp.ofNat)
    {Ps : List InstPub} {fwd : List (Nat×Nat)}
    (hp : I.recs B_SPAR true=(render Ps fwd).par) (hn : Ps.length<2013265921) :
    Extract.SchedLength v (relaySchedValue tr tc) := by
  have hl : Codec.CLocal tr tc pub := by
    have h:=Chacha.local_of_holdsP hH O.lt
    rw [O.tab] at h
    exact h
  have hh : tr.height tc≤2^22 := height_le hH O.lt O.tab rfl
  have hs:=codecRelay_spar_supply hH O.lt O.tab SO I hp
  refine ⟨?_,relaySchedValue_length hl hh⟩
  intro m hm
  have hc : 0<(((upsTraffic v).recvs ZkFormal.NearV3.B_SPLEN).map Msg.toFp).count m.toFp :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  rw [←(ht ZkFormal.NearV3.B_SPLEN m.toFp).2] at hc
  obtain ⟨r,hr,i,hi,hb,hiSend,hmsg,hiMult⟩:=Chacha.exists_of_tableBusCount (by omega :
    tableBusCount AP.tables[tu]!.interactions tr tu pub ZkFormal.NearV3.B_SPLEN false m.toFp≠0)
  obtain ⟨q,hq,j,hj,hjb,hjs,hjm,hjn⟩:=Chacha.recv_matched hH O.lt O.only O.pub hu hr hi hb hiSend hiMult
  rw [O.tab] at hj
  have hc':=Chacha.tableBusCount_pos hq hj hjn
  rw [hjb,hjs,hjm,hmsg] at hc'
  exact codecRelay_splen_value hl hh hs hn (Nat.pos_of_ne_zero hc')
end ZkFormal.NearV3.Render.UpsRelay
