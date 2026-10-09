import ZkFormal.NearV3.Candidates.ProcessRepairShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceBoundary
namespace ZkFormal.NearV3.Candidates.ProcessRepairSourceView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ProcPriorRoutedSourceView
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem local_source (j:Nat) (hj:j<4) {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :TableLocal (base j) (source tr) j pub := by
  have h:=v.component (14+j) (by have hl:20=ProcPriorComparatorRoutedFamily.selected.length:=rfl;omega) (by omega)
  have cases:j=0∨j=1∨j=2∨j=3:=by omega
  have h0:TableLocal (base j) (HorizontalTrace.project (offset j) tr) 0 pub := by
    rcases cases with rfl|rfl|rfl|rfl <;> exact (ProcPriorComparatorRouting.local_iff _ _ _ _).mp h
  exact ⟨h0.log_ge,h0.log_le,h0.constr,h0.bits⟩
theorem cells {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66) :
    (∀x,x<57→(source tr).cell 0 ((source tr).height 0-1) x=(source tr).cell 1 0 x) ∧
    (∀x,x<57→(source tr).cell 1 ((source tr).height 1-1) x=(source tr).cell 2 0 x) ∧
    (∀x,x<57→(source tr).cell 2 ((source tr).height 2-1) x=(source tr).cell 3 0 x) := by
  apply Rcpt.Candidates.SourceLog22.boundaries_cells
  intro b hb msg
  have hb':b=64 ∨ b=65 ∨ b=66:=by simpa using hb
  have hp (dir:Bool):pubCount AP pub b dir msg=0:=by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg hs he
    have h:=hpub seg hs
    rcases hb' with rfl|rfl|rfl <;> omega
  have hh:=v.valid.balance b msg
  rw [ProcessRepairBalance.count v,ProcessRepairBalance.count v,ProcPriorRoutedSourceBoundary.global_count (AP:=ProcessRepairBalance.reference AP) rfl b hb' true,ProcPriorRoutedSourceBoundary.global_count (AP:=ProcessRepairBalance.reference AP) rfl b hb' false,hp true,hp false] at hh
  simpa only [Nat.add_zero] using hh
end ZkFormal.NearV3.Candidates.ProcessRepairSourceView
