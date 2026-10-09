import ZkFormal.NearV3.Candidates.ProcCodecRecordEntry
import ZkFormal.NearV3.Candidates.ProcCodecRecordPartition
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordIndex
import ZkFormal.NearV3.Candidates.ProcCodecFieldInside
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundaries
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteTests
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordCarry
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedLinkGates
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedComparators
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedTerminal
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForwardPayload
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAssembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler

theorem active_of_entry (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (present : Bool) (vid : Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (hcodec : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev)
      R present vid gd fwd=.ok out) (r : Nat) (hrange : r<out.rows.size)
    (hentry : ∀e∈(cRec.drop 17).take 8,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0) :
    ∀e∈cRec.filter (fun e=>!(ProcPriorCodecActual.retiredRec.contains e)),e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  let I := ProcPreparedSequence.input sp prev
  have hidx := ProcCodecGeneratedRecordIndex.active I R present vid gd fwd out hcodec r hrange
  have hin := ProcCodecFieldInside.active I R present vid gd fwd out hcodec r hrange
  have hb := ProcCodecGeneratedBoundaries.active I R present vid gd fwd out hcodec r hrange
  have hac := ProcCodecPhysicalRecordGroups.accumulator_carry I R present vid gd fwd out hcodec r hrange
  have hbt := ProcCodecGeneratedByteTests.active I R present vid gd fwd out hcodec r hrange
  have hcarry := ProcCodecGeneratedRecordCarry.active I R present vid gd fwd out hcodec r hrange
  have hlink := ProcCodecGeneratedLinkGates.active_equations I R present vid gd fwd out hcodec r hrange
  have hcmp := ProcCodecGeneratedComparators.active I R present vid gd fwd out hcodec r hrange
  have hend := ProcCodecGeneratedTerminal.active sp hs prev tauV R hr present vid gd fwd out hcodec r hrange
  have hctl := ProcCodecGeneratedRecordConstraints.active_controls I R present vid gd fwd out hcodec r hrange
  have hforward := ProcCodecGeneratedForwardPayload.active sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg present vid fwd out hcodec r hrange
  apply ProcCodecRecordPartition.assemble
  intro group hgroup e he
  simp only [ProcCodecRecordPartition.pieces,List.mem_cons,List.mem_nil_iff,or_false] at hgroup
  rcases hgroup with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hidx e (List.mem_append_left _ (List.mem_append_left _ he))
  · exact hin e he
  · exact hb e (List.mem_append_left _ he)
  · exact hidx e (List.mem_append_left _ (List.mem_append_right _ he))
  · exact hb e (List.mem_append_right _ he)
  · exact hentry e he
  · exact hac e (List.mem_append_left _ (List.mem_append_left _ he))
  · exact hbt e he
  · exact hidx e (List.mem_append_right _ he)
  · exact hcarry e he
  · exact hlink e (List.mem_append_left _ he)
  · exact hac e (List.mem_append_left _ (List.mem_append_right _ he))
  · exact hlink e (List.mem_append_right _ he)
  · exact hcmp e he
  · exact hac e (List.mem_append_right _ he)
  · exact hend e he
  · exact hctl e (List.mem_append_left _ he)
  · exact hforward e he
  · exact hctl e (List.mem_append_right _ he)
theorem active (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (present : Bool) (vid : Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (hcodec : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev)
      R present vid gd fwd=.ok out) (r : Nat) (hrange : r<out.rows.size) :
    ∀e∈cRec.filter (fun e=>!(ProcPriorCodecActual.retiredRec.contains e)),e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply active_of_entry sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg present vid fwd out hcodec r hrange
  apply ProcCodecPhysicalRecordGroups.active_of_records (ProcPreparedSequence.input sp prev) R present vid gd fwd out hcodec _
    (fun e he=>List.mem_of_mem_drop (List.mem_of_mem_take he)) ?_ r hrange
  intro k f g hk hf hgg
  simpa only [ProcCodecRecordEntry.equations_eq] using
    ProcCodecRecordEntry.active (ProcPreparedSequence.input sp prev) R present vid gd fwd out hcodec k f g hk hf hgg
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAssembly
