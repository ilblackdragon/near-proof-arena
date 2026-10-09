import ZkFormal.NearV3.Candidates.ProcessRepairVbytesEntry
import ZkFormal.NearV3.Candidates.ProcessRepairKeyView
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueByte
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Near
open Qv.Candidates.ValueTable
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem entry {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0) (hg:(ProcPriorRoutedKeyView.key tr).cell 0 r gb=1) :
    ∃e∈es,e.vid=ZkFormal.Chacha.cv (ProcPriorRoutedKeyView.key tr) 0 r vid ∧
      ZkFormal.Chacha.cv (ProcPriorRoutedKeyView.key tr) 0 r pos<e.bytes.length ∧
      ZkFormal.Chacha.cv (ProcPriorRoutedKeyView.key tr) 0 r byte=e.bytes.getD (ZkFormal.Chacha.cv (ProcPriorRoutedKeyView.key tr) 0 r pos) 0 := by
  let i:Interaction:=Qv.Candidates.KeyTrafficRepair.interactions[0]!
  have hi:i∈Qv.Candidates.KeyTrafficRepair.interactions:=by simp [i,Qv.Candidates.KeyTrafficRepair.interactions,Qv.Candidates.CombinedTable.interactions]
  have hir:ProcPriorRoutedKeyView.routed i=i:=rfl
  have hmem:ProcPriorRoutedKeyView.interaction i∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcPriorRoutedKeyView.member hi
  have hmult:(ProcPriorRoutedKeyView.interaction i).multNat tr 0 r pub=i.multNat (ProcPriorRoutedKeyView.key tr) 0 r pub:=by
    unfold ProcPriorRoutedKeyView.interaction
    rw [hir]
    exact HorizontalTraffic.mult_map _ _ tr (ProcPriorRoutedKeyView.key tr) 0 r 0 pub
      (by intro e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)
  have hm:(ProcPriorRoutedKeyView.interaction i).multNat tr 0 r pub≠0:=by
    rw [hmult]
    change (if (ProcPriorRoutedKeyView.key tr).cell 0 r gb=1 then 1 else 0)+0≠0
    rw [hg];decide
  have hmsg:(ProcPriorRoutedKeyView.interaction i).msgVal tr 0 r pub=
      [(ProcPriorRoutedKeyView.key tr).cell 0 r vid,(ProcPriorRoutedKeyView.key tr).cell 0 r pos,
        (ProcPriorRoutedKeyView.key tr).cell 0 r byte]:=by
    unfold ProcPriorRoutedKeyView.interaction
    rw [hir]
    change [_,_,_]=_
    simp only [HorizontalTrace.expression_eval]
    rfl
  have h:=ProcessRepairVbytesEntry.sender_entry view hpub hw hT
    (show 0<AP.tables.length by rw [view.length];decide +kernel) hr hmem
    (show (ProcPriorRoutedKeyView.interaction i).bus=B_VBYTES from rfl)
    (show (ProcPriorRoutedKeyView.interaction i).send=true from rfl) hm
  rw [hmsg] at h
  exact h
end ZkFormal.NearV3.Candidates.ProcessRepairQueueByte
