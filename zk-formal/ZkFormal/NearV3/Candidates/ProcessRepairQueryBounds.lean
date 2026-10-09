import ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryBounds
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueryBounds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection ProcPriorRoutedQueryBounds
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem query_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) (hm:query.multNat tr 0 r pub≠0) :
    cv (codec tr) 0 r Codec.tau<33 ∧ cv (codec tr) 0 r Codec.kidx<4096 ∧
    4096*cv (codec tr) 0 r Codec.tau+cv (codec tr) 0 r Codec.kidx<2^29 := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  change (interaction ProcPriorCodecActual.priorRead).multNat tr 0 r pub≠0 at hm
  rw [mult] at hm
  obtain ⟨_,hR,ha⟩:=query_flags hL hr hm
  have params:=ProcessRepairCodecParameters.active_small view hpub I Ps fwd hrec hlen hns hr ha
  have hN:∀q,q<(codec tr).height 0→cv (codec tr) 0 q Codec.act=1→
      1≤cv (codec tr) 0 q Codec.NN ∧ cv (codec tr) 0 q Codec.NN≤4096 := by
    intro q hq hqa
    have hp:=ProcessRepairCodecParameters.active_small view hpub I Ps fwd hrec hlen hns hq hqa
    exact hp.2.2.2.2
  have hb:=ProcPriorCodecSoundRecordBound.record_bound hL hN r hr hR
  exact ⟨params.1,by omega,by omega⟩

theorem consumer_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=68) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[0]!.toNat<33 ∧ (i.msgVal tr t r pub)[1]!.toNat<4096 ∧
    4096*(i.msgVal tr t r pub)[0]!.toNat+(i.msgVal tr t r pub)[1]!.toNat<2^29 := by
  have ht0:t=0 := Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference,←view.length] using ht) hn i (by simpa only [view.wires t,ProcessRepairBalance.reference] using hi) hs hb)
  subst t
  rw [view.wires] at hi
  have he:=receiver_eq hi hb hs
  subst i
  have hb:=query_bounds view hpub I Ps fwd hrec hlen hns hr hm
  unfold query
  rw [message]
  simpa only [ProcPriorCodecActual.priorRead,Interaction.msgVal,List.map_cons,List.map_nil,
    List.getElem!_cons_zero,List.getElem!_cons_succ,Codec.ev_c,Fp.toNat_ofNat,
    Nat.mod_eq_of_lt (show cv (codec tr) 0 r Codec.tau<P from cv_lt _ _),
    Nat.mod_eq_of_lt (show cv (codec tr) 0 r Codec.kidx<P from cv_lt _ _)] using hb
/-- Bus balance transports the authenticated query ranges to every live
memory-side bus-68 send, with no public bus-68 traffic. -/
theorem sender_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=68) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[0]!.toNat<33 ∧ (i.msgVal tr t r pub)[1]!.toNat<4096 ∧
    4096*(i.msgVal tr t r pub)[0]!.toNat+(i.msgVal tr t r pub)[1]!.toNat<2^29 := by
  have ht0:0<AP.tables.length := by rw [view.length];decide +kernel
  have ho:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=68→i.send=true := by
    intro t ht hn i hi hb
    cases hs:i.send with
    | false=>exact (other_tables (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference,←view.length] using ht) hn i (by simpa only [view.wires t,ProcessRepairBalance.reference] using hi) hs hb).elim
    | true=>rfl
  obtain ⟨q,hq,j,hj,hb',hs',he,hm'⟩:=send_matched view.valid ht0 ho h68 ht hr hi hb hs hm
  have hh:=consumer_bounds view hpub I Ps fwd hrec hlen hns ht0 hq hj hb' hs' hm'
  rw [he] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairQueryBounds
