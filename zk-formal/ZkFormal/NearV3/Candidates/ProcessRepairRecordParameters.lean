import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordParameters
import ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordParameters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedRecordParameters
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
/-- The real bus76 supplier is the SPAR-authenticated Codec first header. -/
theorem header_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1)
    (hw:cv (recordTrace tr) 0 r ProcPriorRecordTable.sender+
      cv (recordTrace tr) 0 r ProcPriorRecordTable.receiver+cv (recordTrace tr) 0 r ProcPriorRecordTable.amount=0) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:recv∈AP.tables[0]!.interactions := by rw [view.wires];exact recv_member
  rcases recv_src view.valid ht hr hi (show recv.bus=76 from rfl) (show recv.send=false from rfl) (header_live hs ha hw) with hp|hp
  · exact (hp (h76 _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference, ←view.length] using ht') hn j (by simpa only [view.wires t', ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    unfold send at hjm hmsg
    rw [ProcPriorRoutedCodecProjection.mult] at hjm
    rw [ProcPriorRoutedCodecProjection.message,recv_message] at hmsg
    have hF:cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.kF=1 := by
      have hh:(c Codec.kF).eval (ProcPriorRoutedCodecProjection.codec tr) 0 q pub=1 := by
        by_cases he:(c Codec.kF).eval (ProcPriorRoutedCodecProjection.codec tr) 0 q pub=1
        · exact he
        · simp only [ProcPriorCodecParameter.interaction,Interaction.multNat,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hjm
          exact (hjm rfl).elim
      change (ProcPriorRoutedCodecProjection.codec tr).cell 0 q Codec.kF=1 at hh
      unfold cv
      rw [hh]
      rfl
    have hL:=ProcessRepairCodecParameters.local_codec view
    have hk:=ProcPriorCodecSoundGeometry.kinds hL hq
    have hact:cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.act=1 := by omega
    have hb:=ProcessRepairCodecParameters.active_small view hpub I Ps fwd hrec hlen hns hq hact
    have he0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
    have he1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
    change cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.tau=cv (recordTrace tr) 0 r ProcPriorRecordTable.tau at he0
    change cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.nn=cv (recordTrace tr) 0 r ProcPriorRecordTable.shards at he1
    omega
/-- Every arbitrary active Record row carries authentic bounded parameters,
via its actual header and the concrete Codec-to-Record bus76 join. -/
theorem active_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨f,hfr,hfs,hfa,hfw,hft,hfn⟩:=ProcPriorRecordOrigin.header_origin hv r hr hs ha
  have hb:=header_bounds view hpub h76 I Ps fwd hrec hlen hns (show f<tr.height 0 by omega) hfs hfa hfw
  change cv (recordTrace tr) 0 f ProcPriorRecordTable.tau=cv (recordTrace tr) 0 r ProcPriorRecordTable.tau at hft
  change cv (recordTrace tr) 0 f ProcPriorRecordTable.shards=cv (recordTrace tr) 0 r ProcPriorRecordTable.shards at hfn
  rw [hft,hfn] at hb
  exact hb

theorem prepared_active_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have hl:(p.sched.map instOf).length≤33 := by
    rw [List.length_map];exact prepD0_len hprep
  have hn:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64 := by
    intro P0 hm
    obtain ⟨sp,hsp,he⟩:=List.mem_map.mp hm
    subst P0
    have hs:=prepD0_sched hprep sp hsp
    exact ⟨hs.n1,hs.n64⟩
  exact active_bounds view hpub h76 I _ fwd hrec hl hn hr hs ha
end ZkFormal.NearV3.Candidates.ProcessRepairRecordParameters
