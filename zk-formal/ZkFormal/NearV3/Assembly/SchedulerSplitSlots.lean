import ZkFormal.NearV3.Assembly.SchedulerSplitShape

namespace ZkFormal.NearV3.Assembly
open NearSpec Render.UpsGen

private theorem drop_head (xs : List Nat) (n : Nat) :
    (xs.drop n).headD 0=xs.getD n 0 := by
  induction xs generalizing n with
  | nil=>simp
  | cons x xs ih=>cases n with
    | zero=>rfl
    | succ n=>exact ih n

/-- The split's old slot is the actual native divergent nibble used by AIR. -/
theorem splitOldSlot_metadata (run : TreeRun) : splitOldSlot run=run.splitNibble := by
  unfold splitOldSlot
  rw [drop_head]
  cases h:run.terminalSource <;> simp [nativeKey,TreeRun.splitNibble,h]

/-- Every present new split child occupies exactly the first/last slot dictated
by the remaining fixed scheduler key, irrespective of the old trie key size. -/
theorem splitNewSlotNative_metadata {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run)
    (hn : run.terminalKey.drop run.matched≠[]) :
    splitNewSlotNative run=(if run.splitCursor [0,15]=1 then 0 else 15) := by
  have hk:=(trace_fixedKey_bounds hr).1
  have hd : run.terminalKey.drop run.matched=[0,15].drop (run.consumed [0,15]+run.matched) := by
    rw [hk,List.drop_drop]
  unfold splitNewSlotNative
  rw [hd]
  cases h:run.consumed [0,15]+run.matched with
  | zero=>simp [TreeRun.splitCursor,h]
  | succ n=>
    cases n with
    | zero=>simp [TreeRun.splitCursor,h]
    | succ n=>simp [h] at hd;exact (hn (List.drop_eq_nil_of_le hd)).elim

end ZkFormal.NearV3.Assembly
