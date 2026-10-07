import ZkFormal.NearV3.Assembly.Execution

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def checkedImplicitStep (k : WalkD0) (p : Blk × Transition) (root : Bytes) :
    Except String (ForInStep Bytes) := do
  let ctx := blockCtx k.L k.H.shardId k.slotB2.gasLimit p.1 p.1.hdr.nextGasPrice
  let pre := partialTrie p.2.values root [keyDelayedIdx, keyBwState]
  let post ← applyMissingChunk prims ctx pre
  check (post.hashOf == p.2.postStateRoot) "invalid: implicit transition post state root"
  pure (.yield post.hashOf)

def implicitPairs (x : ExtV3) (tau : Nat) (blocks : List Blk) : List (Blk × Transition) :=
  (blocks.zipIdx tau).map (fun (b, i) => (b, x.transition i))

theorem ImplicitRunV3.loop {k : WalkD0} {x : ExtV3} {tau : Nat} {root last : Bytes} {bs : List Blk}
    (h : ImplicitRunV3 k x tau root bs last) :
    forIn (implicitPairs x tau bs) root (checkedImplicitStep k) = .ok last := by
  induction h with
  | nil tau root => simp [implicitPairs, pure, Except.pure]
  | cons tau root b bs post last hr hp ht ih =>
    have hs : checkedImplicitStep k (b, x.transition tau) root = .ok (.yield post.hashOf) := by
      simp [checkedImplicitStep, ExtV3.transition, hr, hp, check, pure, Except.pure, bind, Except.bind]
    simp only [implicitPairs, List.zipIdx_cons, List.map_cons, List.forIn_cons]
    rw [hs]
    exact ih

private theorem zip_map_zipIdx {α β : Type} (f : Nat → β) (xs : List α) (start : Nat) :
    xs.zip ((xs.zipIdx start).map (fun (_, i) => f i)) =
      (xs.zipIdx start).map (fun (x, i) => (x, f i)) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [List.zipIdx_cons, ih]

private theorem map_zipIdx_shift {α β : Type} (f : Nat → β) (xs : List α) (start shift : Nat) :
    ((xs.zipIdx start).map (fun (_, i) => f (i + shift))) =
      (xs.zipIdx (start + shift)).map (fun (_, i) => f i) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    congr 1
    have he : start + shift + 1 = start + 1 + shift := by omega
    simpa only [he] using ih (start + 1)

theorem stateWitnessOfV3_implicit_pairs (k : WalkD0) (x : ExtV3) :
    k.implicitBlks.zip (stateWitnessOfV3 k x).implicit = implicitPairs x 1 k.implicitBlks := by
  simp only [stateWitnessOfV3]
  rw [map_zipIdx_shift, zip_map_zipIdx]
  rfl

theorem ImplicitRunV3.witness_loop {k : WalkD0} {x : ExtV3} {root last : Bytes}
    (h : ImplicitRunV3 k x 1 root k.implicitBlks last) :
    forIn (k.implicitBlks.zip (stateWitnessOfV3 k x).implicit) root
      (checkedImplicitStep k) = .ok last := by
  rw [stateWitnessOfV3_implicit_pairs]
  exact h.loop

end ZkFormal.NearV3.Assembly
