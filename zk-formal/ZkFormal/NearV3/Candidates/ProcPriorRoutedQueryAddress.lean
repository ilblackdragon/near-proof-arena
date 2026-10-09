import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryBounds
import ZkFormal.NearV3.Candidates.ProcPriorRoutedLastWrite
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryAddress
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem read_member :ProcPriorRoutedLastWrite.read∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hraw:ProcPriorRoutedLastWrite.read∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    have hh:ProcPriorRoutedLastWrite.read∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==68 && i.send) := by
      rw [ProcPriorRoutedLastWrite.raw_senders];exact List.mem_singleton_self _
    exact (List.mem_filter.mp hh).1
  have hp:ProcPriorRoutedLastWrite.read∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠ProcPriorRoutedLastWrite.read := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠ProcPriorRoutedLastWrite.read := by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=68 at hb
    omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠ProcPriorRoutedLastWrite.read) (hd true) (hd false)).mp hall) _ hp rfl

theorem read_live {tr:Trace Fp} {r:Nat} {pub:List Fp}
    (ha:Live (memory tr) 0 r) (hq:cv (memory tr) 0 r query=1) :
    ProcPriorRoutedLastWrite.read.multNat tr 0 r pub≠0 := by
  change ProcPriorCodecFamilyRead.read.multNat tr 0 r pub≠0
  rw [ProcPriorCodecFamilyRead.projected_mult]
  have hcell (x:Nat) (hx:cv (memory tr) 0 r x=1) :(memory tr).cell 0 r x=(1:Fp) := by
    change (memory tr).cell 0 r x=Fp.ofNat 1
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  have hs:=hcell (ProcPriorVertical4Linear.stage 0) ha.1
  have hact:=hcell act ha.2
  have hquery:=hcell query hq
  change (if (memory tr).cell 0 r (ProcPriorVertical4Linear.stage 0)*
    ((memory tr).cell 0 r act*(memory tr).cell 0 r query)=1 then 1 else 0)+0≠0
  rw [hs,hact,hquery]
  decide +kernel

/-- Every live query in the actual memory stage has a bounded natural address.
The range is authenticated through the real Codec consumer and SPAR public
inventory, not assumed as an ordering or generated-trace condition. -/
theorem query_address {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r query=1) :
    cv (memory tr) 0 r tau<33 ∧ cv (memory tr) 0 r link<4096 ∧ address (memory tr) 0 r<2^29 := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:ProcPriorRoutedLastWrite.read∈AP.tables[0]!.interactions := by rw [htables];exact read_member
  have hh:=ProcPriorRoutedQueryBounds.sender_bounds hH htables hpub h68 I Ps fwd hrec hlen hns ht hr hi
    (show ProcPriorRoutedLastWrite.read.bus=68 from rfl) (show ProcPriorRoutedLastWrite.read.send=true from rfl) (read_live ha hq)
  unfold ProcPriorRoutedLastWrite.read at hh
  rw [ProcPriorCodecFamilyRead.projected_message] at hh
  change ((memory tr).cell 0 r tau).toNat<33 ∧ ((memory tr).cell 0 r link).toNat<4096 ∧
    4096*((memory tr).cell 0 r tau).toNat+((memory tr).cell 0 r link).toNat<2^29 at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryAddress
