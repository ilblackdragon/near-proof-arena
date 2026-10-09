import ZkFormal.NearV3.Candidates.ProcessRepairShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaBytes
import ZkFormal.NearV3.Assembly.ShaUnionBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairByteRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ProcPriorRoutedShaFacts (count sumCount)

theorem component {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) (j:Nat) (hj:j<4)
    {id pos byte:Fp} (hm:0<count tr pub j false B_BYTES [id,pos,byte]) :
    byte.toNat<256 := by
  have he:=ShaPackingTrace.table_traffic (ProcPriorRoutedShaView.sha j tr) 0
    B_BYTES B_DIGEST B_BYTES pub [id,pos,byte] false
  change 0<tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
    (ProcPriorRoutedShaView.sha j tr) 0 pub B_BYTES false [id,pos,byte] at hm
  rw [he] at hm
  have hl:=ShaPackingTrace.decode_local (ProcessRepairShaFacts.local_sha j hj view)
  exact Assembly.shaCountAt_byte_range ⟨hl.log_ge,hl.log_le,hl.constr⟩ hm

theorem union_range {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) (js:List Nat)
    (hjs:∀j∈js,j<4) {id pos byte:Fp}
    (hm:0<sumCount tr pub js false B_BYTES [id,pos,byte]) :byte.toNat<256 := by
  induction js with
  | nil=>simp [sumCount] at hm
  | cons j js ih=>
    by_cases hp:0<count tr pub j false B_BYTES [id,pos,byte]
    · exact component view j (hjs j (by simp)) hp
    · apply ih (fun k hk=>hjs k (by simp [hk]))
      simp only [sumCount] at hm
      omega

/-- Actual BYTES sends are bounded by the installed SHA receivers. Public
receives must be excluded explicitly; excluding public sends is insufficient. -/
theorem sent {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_BYTES false msg=0)
    {id pos byte:Fp} (hm:0<busCount AP.toAir tr pub B_BYTES true [id,pos,byte]) :
    byte.toNat<256 := by
  have hb:=view.valid.balance B_BYTES [id,pos,byte]
  rw [hpub] at hb
  have hr:0<busCount AP.toAir tr pub B_BYTES false [id,pos,byte]:=by omega
  rw [ProcessRepairBalance.count view] at hr
  rw [ProcPriorRoutedShaBytes.global_count (AP:=ProcessRepairBalance.reference AP) rfl] at hr
  exact union_range view [0,1,2,3]
    (by intro j hj;simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj;omega) hr
end ZkFormal.NearV3.Candidates.ProcessRepairByteRange
