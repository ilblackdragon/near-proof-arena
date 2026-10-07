import ZkFormal.NearV3.Assembly.RetainedStore
import ZkFormal.NearV3.Assembly.WitnessSize
import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

def StoreLookupEq (a b : List Bytes) : Prop := ∀ h, storeGet (mkStore a) h = storeGet (mkStore b) h

theorem StoreLookupEq.partialTrie {a b : List Bytes} (h : StoreLookupEq a b)
    (root : Bytes) (keys : List (List Nat)) : partialTrie a root keys = partialTrie b root keys := by
  unfold NearSpecV3.partialTrie
  rw [buildFor_store_congr h]

theorem StoreLookupEq.append {a b : List Bytes} (h : StoreLookupEq a b) (extra : List Bytes) :
    StoreLookupEq (a++extra) (b++extra) := by
  intro key
  simp only [storeGet_append,h key]

theorem StoreLookupEq.rebuildPost {a b : List Bytes} (h : StoreLookupEq a b)
    (post : PTrie) (keys : List (List Nat)) : rebuildPost a post keys = rebuildPost b post keys := by
  unfold NearSpecV3.rebuildPost
  exact (h.append _ |>.append _).partialTrie _ _

theorem forIn_aligned {α σ : Type} (r : α → α → Prop)
    (f : α → σ → Except String (ForInStep σ)) (g : α → σ → Except String (ForInStep σ))
    {xs : List α} {ys : List α}
    (ha : Aligned r xs ys) (hf : ∀ a b, r a b → ∀ s, f a s = g b s) (s : σ) :
    forIn xs s f = forIn ys s g := by
  induction ha generalizing s with
  | nil => rfl
  | cons h ha ih =>
    rw [List.forIn_cons,List.forIn_cons,hf _ _ h s]
    cases g _ s with
    | error err => rfl
    | ok step => cases step with
      | done out => rfl
      | yield out => exact ih out

def unfoldStep (k : WalkD0) (pair : Blk × Transition)
    (st : List (PTrie × PTrie) × Bytes) : Except String (ForInStep (List (PTrie × PTrie) × Bytes)) := do
  let ctx := blockCtx k.L k.H.shardId k.slotB2.gasLimit pair.1 pair.1.hdr.nextGasPrice
  let keys := [keyDelayedIdx,keyBwState]
  let pre := partialTrie pair.2.values st.2 keys
  let post ← applyMissingChunk prims ctx pre
  pure (.yield (st.1 ++ [(pre,rebuildPost pair.2.values post keys)],post.hashOf))

theorem unfoldStep_storeEq (k : WalkD0) (b : Blk) (t u : Transition)
    (h : StoreLookupEq t.values u.values) (st : List (PTrie × PTrie) × Bytes) :
    unfoldStep k (b,t) st = unfoldStep k (b,u) st := by
  unfold unfoldStep
  simp only [h.partialTrie]
  cases applyMissingChunk prims (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
      (partialTrie u.values st.2 [keyDelayedIdx,keyBwState]) with
  | error err => rfl
  | ok post => simp only [bind,Except.bind,pure,Except.pure,h.rebuildPost]

theorem zip_storeEq (blocks : List Blk) {ts us : List Transition}
    (h : Aligned (fun t u => StoreLookupEq t.values u.values) ts us) :
    Aligned (fun (a : Blk × Transition) b => a.1 = b.1 ∧ StoreLookupEq a.2.values b.2.values)
      (blocks.zip ts) (blocks.zip us) := by
  induction h generalizing blocks with
  | nil => simp only [List.zip_nil_right]; exact .nil
  | cons h hs ih =>
    cases blocks with
    | nil => exact .nil
    | cons b blocks => exact .cons ⟨rfl,h⟩ (ih blocks)

theorem unfoldLoop_storeEq (k : WalkD0) (blocks : List Blk) {ts us : List Transition}
    (h : Aligned (fun t u => StoreLookupEq t.values u.values) ts us) (st : List (PTrie × PTrie) × Bytes) :
    forIn (blocks.zip ts) st (unfoldStep k) = forIn (blocks.zip us) st (unfoldStep k) := by
  apply forIn_aligned _ _ _ (zip_storeEq blocks h)
  rintro ⟨b,t⟩ ⟨b',u⟩ ⟨hb,hv⟩ s
  cases hb
  exact unfoldStep_storeEq k b t u hv s

theorem triesD0_storeEq {cb wa wb : Bytes} {a b : StateWitness}
    (ha : decodeW wa = .ok a) (hb : decodeW wb = .ok b)
    (he : a.entries = b.entries) (hm : StoreLookupEq a.main.values b.main.values)
    (hi : Aligned (fun t u => StoreLookupEq t.values u.values) a.implicit b.implicit) :
    triesD0 cb wa = triesD0 cb wb := by
  have hr (k : WalkD0) : appliedReceipts k a = appliedReceipts k b := by
    unfold appliedReceipts
    rw [he]
  unfold triesD0
  cases walkD0 cb with
  | error err => rfl
  | ok k =>
    have hl := unfoldLoop_storeEq k k.implicitBlks hi
    unfold ZkFormal.NearV3.Assembly.unfoldStep at hl
    dsimp only at hl
    simp only [bind,Except.bind,pure,Except.pure] at hl
    simp only [ha,hb,bind,Except.bind,hr,hm.partialTrie,hm.rebuildPost,pure,Except.pure,throw]
    repeat' first | rfl | (rw [hl]) | (split; all_goals try rfl)
    all_goals grind only

theorem unfoldBytes_storeEq {cb wa wb : Bytes} {a b : StateWitness}
    (ha : decodeW wa = .ok a) (hb : decodeW wb = .ok b)
    (he : a.entries = b.entries) (hm : StoreLookupEq a.main.values b.main.values)
    (hi : Aligned (fun t u => StoreLookupEq t.values u.values) a.implicit b.implicit) :
    unfoldBytes cb wa = unfoldBytes cb wb := by
  unfold unfoldBytes
  rw [triesD0_storeEq ha hb he hm hi]

/-- Retaining first-match original blobs suffices semantically. This says nothing
about their allocation as AIR rows or the unchanged value-byte budget. -/
theorem retainedStore_storeEq {front original : List Bytes}
    (hp : ∀ v ∈ front, Found (mkStore original) v) :
    StoreLookupEq (retainedStore front original) original := retainedStore_lookup hp

end ZkFormal.NearV3.Assembly
