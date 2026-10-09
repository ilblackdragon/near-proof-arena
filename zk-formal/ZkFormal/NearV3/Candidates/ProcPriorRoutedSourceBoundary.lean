import ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedVParent
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedSourceView
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def filtered (j b:Nat) (dir:Bool):List Interaction:=
  ((base j).interactions.filter (fun i=>i.bus==b && i.send==dir)).map (HorizontalTables.interaction (offset j))

theorem mult_focus (tr:Trace Fp) (pub:List Fp) (j r:Nat) (es:List Expr) (k:Nat) :
    Interaction.multNat.go (HorizontalTrace.project (offset j) tr) 0 r pub es k=
      Interaction.multNat.go (source tr) j r pub es k := by
  induction es generalizing k with
  | nil=>rfl
  | cons e es ih=>
    have he:e.eval (HorizontalTrace.project (offset j) tr) 0 r pub=e.eval (source tr) j r pub:=rfl
    simp only [Interaction.multNat.go,he,ih]

theorem component_count (tr:Trace Fp) (pub msg:List Fp) (j b:Nat) (dir:Bool) :
    tableBusCount (filtered j b dir) tr 0 pub b dir msg=
      tableBusCount (base j).interactions (source tr) j pub b dir msg := by
  rw [ProcPriorRoutedVParent.filter_count (base j).interactions]
  have hc:=HorizontalTraffic.count_map (HorizontalTables.expression (offset j))
    ((base j).interactions.filter (fun i=>i.bus==b && i.send==dir)) tr (HorizontalTrace.project (offset j) tr) 0 pub b dir msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)
  refine hc.trans ?_
  simp only [tableBusCount,Interaction.multNat,mult_focus]
  simp only [Interaction.msgVal,Expr.eval,rowEnv,HorizontalTrace.project,source,Trace.height]
  rfl

theorem fused_count (tr:Trace Fp) (pub msg:List Fp) (b:Nat) (hb:b=64 ∨ b=65 ∨ b=66) (dir:Bool) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub b dir msg=
      Rcpt.Candidates.SourceLog22.boundaryCount (source tr) 0 1 2 3 pub b dir msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have he:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==b && i.send==dir)=
    filtered 0 b dir++filtered 1 b dir++filtered 2 b dir++filtered 3 b dir:=by
    rcases hb with rfl|rfl|rfl <;> cases dir <;> rfl
  rw [he]
  simp only [HorizontalTraffic.count_append,component_count]
  rfl

theorem tail_absent (b:Nat) (hb:b=64 ∨ b=65 ∨ b=66) :
    ((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != b)))=true := by
  rcases hb with rfl|rfl|rfl <;> decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (b:Nat)
    (hb:b=64 ∨ b=65 ∨ b=66) (dir:Bool) (msg:List Fp) :
    busCount AP.toAir tr pub b dir msg=
      Rcpt.Candidates.SourceLog22.boundaryCount (source tr) 0 1 2 3 pub b dir msg := by
  have htail:busCount.go tr pub b dir msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=0:=by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hbus
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1:=by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 1) t ht];exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp (tail_absent b hb) _ hmem) i hi
    have hn:i.bus≠b:=by simpa using hh
    exact (hn hbus).elim
  unfold busCount
  change busCount.go tr pub b dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub b dir msg+
    busCount.go tr pub b dir msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=_
  rw [htail,Nat.add_zero,fused_count tr pub msg b hb dir]

theorem cells {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66) :
    (∀x,x<57→(source tr).cell 0 ((source tr).height 0-1) x=(source tr).cell 1 0 x) ∧
    (∀x,x<57→(source tr).cell 1 ((source tr).height 1-1) x=(source tr).cell 2 0 x) ∧
    (∀x,x<57→(source tr).cell 2 ((source tr).height 2-1) x=(source tr).cell 3 0 x) := by
  apply Rcpt.Candidates.SourceLog22.boundaries_cells
  intro b hb msg
  have hb':b=64 ∨ b=65 ∨ b=66:=by simpa using hb
  have hp (dir:Bool):pubCount AP pub b dir msg=0:=by
    apply pubCount_zero
    intro seg hs he
    have h:=hpub seg hs
    rcases hb' with rfl|rfl|rfl <;> omega
  have hh:=hH.balance b msg
  rw [global_count htables b hb' true,global_count htables b hb' false,hp true,hp false] at hh
  simpa only [Nat.add_zero] using hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceBoundary
