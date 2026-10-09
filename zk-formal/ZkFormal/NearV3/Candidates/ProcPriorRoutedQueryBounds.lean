import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecParameters
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryBounds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def query : Interaction:=interaction ProcPriorCodecActual.priorRead

theorem query_flags {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) (hr:r<tr.height t)
    (hm:ProcPriorCodecActual.priorRead.multNat tr t r pub≠0) :
    cv tr t r Codec.fA=1 ∧ cv tr t r Codec.kR=1 ∧ cv tr t r Codec.act=1 := by
  have hg:(Expr.mul (c Codec.fA) (c Codec.e2)).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c Codec.fA) (c Codec.e2)).eval tr t r pub=1
    · exact he
    · simp only [ProcPriorCodecActual.priorRead,Interaction.multNat,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hk:=ProcPriorCodecSoundGeometry.kinds hL hr
  have hF:cv tr t r Codec.fA=1 := by
    by_cases hz:cv tr t r Codec.fA=0
    · rw [ZkFormal.Near.eval_mul,Codec.ev_c,hz] at hg
      change (0:Fp)*_=1 at hg
      have h01:(0:Fp)≠1 := by decide +kernel
      exact (h01 (by grind only)).elim
    · omega
  exact ⟨hF,by omega,by omega⟩

/-- Ranges of the actual fused Codec's memory query fields, derived from the
corrected AIR and authenticated public parameter inventory. -/
theorem query_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) (hm:query.multNat tr 0 r pub≠0) :
    cv (codec tr) 0 r Codec.tau<33 ∧ cv (codec tr) 0 r Codec.kidx<4096 ∧
    4096*cv (codec tr) 0 r Codec.tau+cv (codec tr) 0 r Codec.kidx<2^29 := by
  have hL:=ProcPriorRoutedCodecParameters.local_codec hH htables
  change (interaction ProcPriorCodecActual.priorRead).multNat tr 0 r pub≠0 at hm
  rw [mult] at hm
  obtain ⟨_,hR,ha⟩:=query_flags hL hr hm
  have params:=ProcPriorRoutedCodecParameters.active_small hH htables hpub I Ps fwd hrec hlen hns hr ha
  have hN:∀q,q<(codec tr).height 0→cv (codec tr) 0 q Codec.act=1→
      1≤cv (codec tr) 0 q Codec.NN ∧ cv (codec tr) 0 q Codec.NN≤4096 := by
    intro q hq hqa
    have hp:=ProcPriorRoutedCodecParameters.active_small hH htables hpub I Ps fwd hrec hlen hns hq hqa
    exact hp.2.2.2.2
  have hb:=ProcPriorCodecSoundRecordBound.record_bound hL hN r hr hR
  exact ⟨params.1,by omega,by omega⟩

theorem raw_receivers :ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==68 && !i.send)=[query] := rfl

theorem receiver_eq {i:Interaction} (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hb:i.bus=68) (hs:i.send=false) :i=query := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=68→j.send=false→j=query := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==68 && !i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=68→j.send=false→j=query :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=68→j.send=false→j=query)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs

theorem other_tables {AP:AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=false→i.bus≠68 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.send || i.bus != 68)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he,List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv

/-- Every live bus-68 table consumer in the installed family carries small
natural timestamp and link-index fields. -/
theorem consumer_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=68) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[0]!.toNat<33 ∧ (i.msgVal tr t r pub)[1]!.toNat<4096 ∧
    4096*(i.msgVal tr t r pub)[0]!.toNat+(i.msgVal tr t r pub)[1]!.toNat<2^29 := by
  have ht0:t=0 := Classical.byContradiction (fun hn=>other_tables htables t ht hn i hi hs hb)
  subst t
  rw [htables] at hi
  have he:=receiver_eq hi hb hs
  subst i
  have hb:=query_bounds hH htables hpub I Ps fwd hrec hlen hns hr hm
  unfold query
  rw [message]
  simpa only [ProcPriorCodecActual.priorRead,Interaction.msgVal,List.map_cons,List.map_nil,
    List.getElem!_cons_zero,List.getElem!_cons_succ,Codec.ev_c,Fp.toNat_ofNat,
    Nat.mod_eq_of_lt (show cv (codec tr) 0 r Codec.tau<P from cv_lt _ _),
    Nat.mod_eq_of_lt (show cv (codec tr) 0 r Codec.kidx<P from cv_lt _ _)] using hb
/-- Bus balance transports the authenticated query ranges to every live
memory-side bus-68 send, with no public bus-68 traffic. -/
theorem sender_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have ho:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=68→i.send=true := by
    intro t ht hn i hi hb
    cases hs:i.send with
    | false=>exact (other_tables htables t ht hn i hi hs hb).elim
    | true=>rfl
  obtain ⟨q,hq,j,hj,hb',hs',he,hm'⟩:=send_matched hH ht0 ho h68 ht hr hi hb hs hm
  have hh:=consumer_bounds hH htables hpub I Ps fwd hrec hlen hns ht0 hq hj hb' hs' hm'
  rw [he] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryBounds
