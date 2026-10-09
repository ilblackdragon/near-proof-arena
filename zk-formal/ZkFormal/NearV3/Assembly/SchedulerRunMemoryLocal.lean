import ZkFormal.NearV3.Assembly.SchedulerRunComparisonTraffic
import ZkFormal.NearV3.Candidates.ProcActualMemorySegOk
import ZkFormal.NearV3.Candidates.MemConcatLocal
import ZkFormal.NearV3.Candidates.ProcActualPublic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem prior_run_segments {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) :
    ∀R∈bs.map NativeBlock.run,∀g∈R.segs,SegOk g := by
  intro R hR
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hR
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  have hidx:=hc.indexed i b hi
  have hm: b.pub∈p.sched:=List.mem_iff_getElem?.mpr ⟨i,hidx.1.1⟩
  have hs:=prepD0_sched hp b.pub hm
  have hpub:=ProcActualPublic.schedPub_fields b.witness.ctx b.pub (hc.valid b hb).1.2.2.1
  have ht:b.run.tau≤32:=by
    have hil:i<bs.length:=List.getElem?_eq_some_iff.mp hi |>.1
    rw [hidx.2.1]
    have hn:=hc.length
    omega
  have hr:ActualRun.run (ProcPreparedSequence.input b.pub b.old) b.run.tau=.ok b.run :=by
    rw [hidx.2.1];exact hidx.1.2
  exact ProcActualMemorySegOk.run b.pub hs hpub.1 b.old b.run.tau ht b.run hr

theorem prior_memory_table {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (t : Nat) (pub : List Fp) :
    TableLocal Mem.table (MemConcatCells.trace (bs.map NativeBlock.run)) t pub := by
  let base:Run:=⟨0,0,0,0,[],[],#[],[],#[],[],[],[],0,
    ⟨#[],#[],#[],#[],NearSpecV3.Rng.ofSeed []⟩⟩
  apply MemConcatLocal.table base _ (prior_run_segments hp B bs hc)
  have hd:=prior_run_data hp B bs hc
  have hh:=memory_rows_bound (bs.map NativeBlock.run) 67200 (by
    intro R hR
    obtain ⟨sp,prev,hs,hr,_⟩:=hd R hR
    exact ProcActualMemoryRowBudget.run _ _ R hr hs.n64
      (ProcActualRunComparisonBudget.prepared_cost sp hs prev R.tau R hr))
  simp only [List.length_map] at hh
  have hn:=hc.length
  omega
end ZkFormal.NearV3.Assembly.CodecDigest
