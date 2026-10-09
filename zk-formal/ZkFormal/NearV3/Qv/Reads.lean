import ZkFormal.NearV3.Qv.Buffered

/-! Queue read interface for extracted witnesses. The three tree arguments
preserve the actual runtime read points; moving reads across writes needs a
separate preservation proof. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3 ReexecV3D0

structure MainValues where
  delayed : Option Bytes
  buffered : Option Bytes
  shards : List Nat
  yielded : Option Bytes

def MainValues.Valid (v : MainValues) : Prop :=
  EmptyQueue v.delayed ∧ BufferedValue v.buffered v.shards ∧ EmptyQueue v.yielded

def MainValues.Reads (v : MainValues) (pre afterScheduler afterReceipts : PTrie) : Prop :=
  pre.find keyDelayedIdx = some v.delayed ∧
  afterScheduler.find keyBufferedIdx = some v.buffered ∧
  (∀ s ∈ v.shards, ∃ value, afterScheduler.find (keyGroupsData s) = some value) ∧
  afterReceipts.find keyYieldIdx = some v.yielded

theorem readKey_iff (t : PTrie) (key : List Nat) (what : String) (v : Option Bytes) :
    readKey t key what = .ok v ↔ t.find key = some v := by
  cases ht : t.find key <;> simp [readKey,ht]

def groupReadStep (t : PTrie) (s : Nat) (_ : Unit) : Except String (ForInStep Unit) := do
  let _ ← readKey t (keyGroupsData s) "BufferedReceiptGroupsQueueData"
  pure (.yield ())

theorem groupReads_of_loop (t : PTrie) : ∀ (ss : List Nat) {u : Unit},
    forIn ss () (groupReadStep t) = .ok u →
      ∀ s ∈ ss, ∃ v, t.find (keyGroupsData s) = some v
  | [], _, _ => by simp
  | a::ss, u, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step,hs,h⟩ := bind_ok' h
    unfold groupReadStep at hs
    obtain ⟨v,hv,hs⟩ := bind_ok' hs
    simp only [pure,Except.pure,Except.ok.injEq] at hs
    subst step
    have ht := groupReads_of_loop t ss h
    intro s hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨v,(readKey_iff _ _ _ _).mp hv⟩
    · exact ht s hmem

theorem groupReads_loop (t : PTrie) : ∀ (ss : List Nat),
    (∀ s ∈ ss, ∃ v, t.find (keyGroupsData s) = some v) →
      forIn ss () (groupReadStep t) = .ok ()
  | [], _ => rfl
  | a::ss, h => by
    obtain ⟨v,hv⟩ := h a (by simp)
    have hr := (readKey_iff t (keyGroupsData a) "BufferedReceiptGroupsQueueData" v).mpr hv
    have ht := groupReads_loop t ss (fun s hs => h s (by simp [hs]))
    rw [List.forIn_cons]
    simp only [groupReadStep,hr,bind,Except.bind,pure,Except.pure]
    exact ht

theorem groupReads_loop_iff (t : PTrie) (ss : List Nat) :
    forIn ss () (groupReadStep t) = .ok () ↔
      ∀ s ∈ ss, ∃ v, t.find (keyGroupsData s) = some v :=
  ⟨groupReads_of_loop t ss,groupReads_loop t ss⟩

/-- Actual successful new-chunk execution supplies the parser semantics and
all deterministic queue reads at their original runtime stages. -/
theorem applyNewChunk_queue_reads {prims : Prims} {ctx : ApplyCtx} {pre : PTrie}
    {receipts : List NearSpec.Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx pre receipts = .ok out) :
    ∃ afterScheduler so, ∃ v : MainValues, schedStep prims ctx pre = .ok (afterScheduler,so) ∧
      v.Valid ∧ v.Reads pre afterScheduler out.trie := by
  unfold applyNewChunk at h
  obtain ⟨delayed,hd,h⟩ := bind_ok' h
  obtain ⟨u1,hde,h⟩ := bind_ok' h
  obtain ⟨⟨mid,so⟩,hstep,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨buffered,hb,h⟩ := bind_ok' h
  obtain ⟨shards,hbs,h⟩ := bind_ok' h
  obtain ⟨u2,hgroups,h⟩ := bind_ok' h
  obtain ⟨⟨acc,limits⟩,happly,h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨yielded,hy,h⟩ := bind_ok' h
  obtain ⟨u3,hye,h⟩ := bind_ok' h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  cases u1; cases u2; cases u3
  refine ⟨mid,so,⟨delayed,buffered,shards,yielded⟩,hstep,?_,?_,?_,?_,?_⟩
  · exact ⟨(queueEmpty_iff _ _).mp hde,(bufferedShards_iff _ _).mp hbs,(queueEmpty_iff _ _).mp hye⟩
  · exact (readKey_iff _ _ _ _).mp hd
  · exact (readKey_iff _ _ _ _).mp hb
  · exact groupReads_of_loop mid shards hgroups
  · exact (readKey_iff _ _ _ _).mp hy

/-- Missing-chunk delayed-index reads demand determinacy only. They do not
require an empty queue and must not inherit the new-chunk parser restriction. -/
theorem applyMissingChunk_delayed_read {prims : Prims} {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre = .ok post) :
    ∃ delayed, pre.find keyDelayedIdx = some delayed := by
  unfold applyMissingChunk at h
  obtain ⟨delayed,hd,_⟩ := bind_ok' h
  exact ⟨delayed,(readKey_iff _ _ _ _).mp hd⟩

end ZkFormal.NearV3.Qv
