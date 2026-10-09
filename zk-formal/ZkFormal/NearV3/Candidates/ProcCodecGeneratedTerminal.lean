import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPrefix
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndInactive
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndLocal
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndSaturation
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedTerminal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler

theorem saturation (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k : Nat) (hk : k<R.n*R.n) :
    ∀e∈(cRec.drop 55).take 1,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*2+7))=0 := by
  obtain ⟨rows,cmps,before,after,hp,ht,_,ha⟩ := ProcCodecGeneratedRecordPrefix.cell I R present vid gb fwd out h k 2 7 hk (by decide) (by decide)
  obtain ⟨a,ha',he⟩ := ProcPriorCodecEndSaturation.actual I R present gb fwd vid k rows cmps before after hk hp ht
    (if 5+24*k+8*2+7+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*2+7+1]![c]! else fun _=>0)
    (if 5+24*k+8*2+7=0 then 1 else 0) 0 1
  have heq : a=out.rows[5+24*k+8*2+7]! := Array.push_inj_right.mp (ha'.symm.trans ha)
  subst a
  exact he

theorem debit (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (present : Bool) (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R present vid gb fwd=.ok out)
    (k : Nat) (hk : k<R.n*R.n) :
    ∀e∈(cRec.drop 54).take 1 ++ (cRec.drop 56).take 3,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*2+7))=0 := by
  have hn := (ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr).2.1
  have hi : k<sp.ids.length*sp.ids.length := by simpa [hn,ProcPreparedSequence.input] using hk
  obtain ⟨rows,cmps,before,after,hp,ht,_,ha⟩ := ProcCodecGeneratedRecordPrefix.cell
    (ProcPreparedSequence.input sp prev) R present vid gb fwd out h k 2 7 hk (by decide) (by decide)
  obtain ⟨a,ha',he⟩ := ProcPriorCodecEndLocal.native sp hs prev tauV R hr present gb fwd vid k rows cmps before after hi hp ht
    (if 5+24*k+8*2+7+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*2+7+1]![c]! else fun _=>0)
    (if 5+24*k+8*2+7=0 then 1 else 0) 0 1
  have heq : a=out.rows[5+24*k+8*2+7]! := Array.push_inj_right.mp (ha'.symm.trans ha)
  subst a
  exact he

theorem terminal (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (present : Bool) (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R present vid gb fwd=.ok out)
    (k : Nat) (hk : k<R.n*R.n) :
    ∀e∈(cRec.drop 54).take 5,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*2+7))=0 := by
  have hd := debit sp hs prev tauV R hr present vid gb fwd out h k hk
  have hs := saturation (ProcPreparedSequence.input sp prev) R present vid gb fwd out h k hk
  have he : (cRec.drop 54).take 5=(cRec.drop 54).take 1 ++ (cRec.drop 55).take 1 ++ (cRec.drop 56).take 3 := by decide +kernel
  rw [he]
  intro e hm
  rcases List.mem_append.mp hm with hm|hm
  · rcases List.mem_append.mp hm with hm|hm
    · exact hd e (List.mem_append_left _ hm)
    · exact hs e hm
  · exact hd e (List.mem_append_right _ hm)
theorem active (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (present : Bool) (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R present vid gb fwd=.ok out)
    (r : Nat) (hrange : r<out.rows.size) :
    ∀e∈(cRec.drop 54).take 5,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecPhysicalRecordGroups.active_of_records (ProcPreparedSequence.input sp prev) R present vid gb fwd out h _
    (fun e he=>List.mem_of_mem_drop (List.mem_of_mem_take he)) ?_ r hrange
  intro k f g hk hf hg
  by_cases hend : f=2 ∧ g=7
  · obtain ⟨rfl,rfl⟩ := hend
    exact terminal sp hs prev tauV R hr present vid gb fwd out h k hk
  · have hnot : f≠2 ∨ g≠7 := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    refine ProcCodecGeneratedRecordPosition.property (ProcPreparedSequence.input sp prev) R present vid gb fwd out h k f g hk hf hg
      (fun a=>∀e∈(cRec.drop 54).take 5,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
        (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0)
        (if 5+24*k+8*f+g=0 then 1 else 0) 0 1)=0) ?_
    intro before after hstep
    exact ProcPriorCodecEndInactive.actual (ProcPreparedSequence.input sp prev) R present gb fwd vid k f g before after hk hf hg hnot hstep _ _ _ _
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedTerminal
