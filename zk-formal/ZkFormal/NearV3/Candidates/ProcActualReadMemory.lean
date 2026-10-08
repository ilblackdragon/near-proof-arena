import ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant
namespace ZkFormal.NearV3.Candidates.ProcActualReadMemory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcMemoryTimeInvariant

theorem read_list (aa gg : Array Nat) (cs : List CReq) (start : Nat)
    (ops : Array (Array Gen.MOp)) (hids : cs.map CReq.cid=List.range' start cs.length)
    (hb : AllBefore (start+1) ops) :
    ∃out,forIn cs ops (ProcActualReplayFactor.readStep aa gg)=.ok out ∧
      AllBefore (start+cs.length+1) out := by
  induction cs generalizing start ops with
  | nil => exact ⟨ops,rfl,by simpa using hb⟩
  | cons c cs ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at hids
    obtain ⟨next,hn,hb'⟩ := read_step aa gg c ops (by simpa [hids.1] using hb)
    obtain ⟨out,ho,hend⟩ := ih (start+1) next hids.2 (by simpa [hids.1,Nat.add_assoc] using hb')
    refine ⟨out,?_,?_⟩
    · simpa only [List.forIn_cons,hn,bind,Except.bind] using ho
    · simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hend

theorem conversion_ids (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv) :
    cv.toList.map CReq.cid=List.range' 0 cv.size := by
  have hf := ProcActualInitialPush.loop_facts I cv h
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hb : i<cv.size := by simpa using hi
    have hh := (hf i hb).1
    simpa [getElem!_pos,hb] using hh

theorem read_array (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (aa gg : Array Nat) (n : Nat) :
    ∃out,forIn cv (Array.replicate n #[]) (ProcActualReplayFactor.readStep aa gg)=.ok out ∧
      AllBefore (cv.size+1) out := by
  have hi := conversion_ids I cv h
  obtain ⟨out,ho,hb⟩ := read_list aa gg cv.toList 0 (Array.replicate n #[])
    (by simpa using hi) (empty_logs 1 n)
  exact ⟨out,by simpa only [Array.forIn_toList] using ho,by simpa using hb⟩

open NearSpecV3.Scheduler in
theorem prepared_reads (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv) :
    let I := ProcPreparedSequence.input sp prev
    let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
    ∃out,forIn cv (Array.replicate (I.ids.length*I.ids.length) #[])
      (ProcActualReplayFactor.readStep lp.a2 lp.g2)=.ok out ∧ AllBefore T0 out := by
  dsimp only
  let I := ProcPreparedSequence.input sp prev
  obtain ⟨out,ho,hb⟩ := read_array I cv hcv _ _ (I.ids.length*I.ids.length)
  have hv := ProcActualConversionExact.loop_view I I.raw #[] cv hcv
  have hlen : cv.size=(convRaw I.p I.ids.length I.raw).length := by
    have hh := congrArg List.length hv
    simpa [ProcActualConversionExact.view] using hh
  have hc : cv.size≤I.raw.length := by rw [hlen]; exact List.length_filterMap_le _ _
  have hraw := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  change I.raw.length≤4096 at hraw
  have hconst : 4097≤T0 := by decide
  exact ⟨out,ho,fun ops hm=>before_mono _ _ ops (hb ops hm) (by omega)⟩
end ZkFormal.NearV3.Candidates.ProcActualReadMemory
