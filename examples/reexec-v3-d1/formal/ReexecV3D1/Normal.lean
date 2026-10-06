import ReexecV3D1.NormalDefs
import ReexecV3D1.NormLemmas
import ReexecV3D1.Canon

namespace ReexecV3D1

open NearSpec NearSpecV3

set_option hygiene false in
/-- One lockstep step of `h` (the accepting run of `checkD1`), `hk` (the run of its
verbatim copy `keysD1`, whose auxiliary matchers are different constants, so results are
matched by definitional unification) and the goal (`checkD1` on the normal form). -/
macro "lstep3" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _;
     obtain ⟨_, ha, h⟩ := bind_ok h; obtain ⟨_, hb, hk⟩ := bind_ok hk;
     cases (ha.symm.trans hb); rw [ha, ok_bind];
     (try dsimp only at h); (try dsimp only at hk); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _));
     split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (rename_i heq; split at hk <;> (rename_i heq2; first
          | (cases (heq.symm.trans heq2); done)
          | (cases (heq.symm.trans heq2);
             (try dsimp only at h); (try dsimp only at hk); (try dsimp only))))))

set_option hygiene false in
/-- Lockstep of `h` and the goal only. -/
macro "lstep2" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h; rw [ha, ok_bind];
     (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _)); split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (obtain ⟨_, ht, _⟩ := bind_ok h;
         simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at ht; done)
      | (cases h; done)
      | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
      | (guard_hyp h :~ (bind (m := Except String) _ _) = _; (try dsimp only at h); (try dsimp only))))

set_option hygiene false in
/-- Lockstep of `h` and the goal when their auxiliary matchers differ (or coincide). -/
macro "lstep2m" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h;
     rw [ha, ok_bind]; (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _));
     split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (rename_i heq; split <;> (rename_i heq2; first
          | (cases (heq.symm.trans heq2); done)
          | (cases (heq.symm.trans heq2); (try dsimp only at h); (try dsimp only))))))

theorem normImpl_length : ∀ (r : Bytes) (ts : List Transition), (normImpl r ts).length = ts.length
  | _, [] => rfl
  | _, _ :: ts => by simp [normImpl, normImpl_length _ ts]

theorem foldl_add_shift (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

theorem sum_le_of_nodup_subset : ∀ (l m : List Bytes), l.Nodup → (∀ x ∈ l, x ∈ m) →
    (l.map List.length).foldl (· + ·) 0 ≤ (m.map List.length).foldl (· + ·) 0
  | [], m, _, _ => by simp
  | a :: l, m, hn, hs => by
    rw [List.nodup_cons] at hn
    have ham : a ∈ m := hs a List.mem_cons_self
    have hp := List.perm_cons_erase ham
    have hsub : ∀ x ∈ l, x ∈ m.erase a := by
      intro x hx
      have hxm := hs x (List.mem_cons_of_mem _ hx)
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr hxm
    have ih := sum_le_of_nodup_subset l (m.erase a) hn.2 hsub
    have hm : (m.map List.length).foldl (· + ·) 0 = a.length + ((m.erase a).map List.length).foldl (· + ·) 0 := by
      rw [(hp.map List.length).foldl_eq' (fun _ _ _ _ _ => by omega) 0]
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_add_shift _ (0 + a.length)]; omega
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_shift _ (0 + a.length), hm]; omega

theorem sum_normVals_le (vals q : List Bytes) :
    ((normVals vals q).map List.length).foldl (· + ·) 0 ≤ (vals.map List.length).foldl (· + ·) 0 := by
  apply sum_le_of_nodup_subset
  · unfold normVals
    exact (isort_perm _ _).symm.nodup (by
      have := dedupLastBy_pairwise id (q.filterMap (storeGet (mkStore vals)))
      exact this.imp (fun h => h))
  · intro x hx
    unfold normVals at hx
    rw [mem_isort] at hx
    have := mem_dedupLastBy id _ x hx
    rw [List.mem_filterMap] at this
    obtain ⟨y, -, hy⟩ := this
    exact (storeGet_some_hash hy).2

theorem ptrie_main1 (K : List (List Nat)) (R : Bytes) (t : Transition) :
    partialTrie (normMain K R t).values R [keyBufferedIdx] = partialTrie t.values R [keyBufferedIdx] :=
  partialTrie_normVals _ _ R _ (fun x hx => List.mem_append_left _ hx)

theorem ptrie_main2 (K : List (List Nat)) (R : Bytes) (t : Transition) :
    partialTrie (normMain K R t).values R K = partialTrie t.values R K :=
  partialTrie_normVals _ _ R _ (fun x hx => List.mem_append_right _ hx)

theorem ptrie_normT (r : Bytes) (t : Transition) :
    partialTrie (normT r t).values r [keyDelayedIdx, keyBwState] =
      partialTrie t.values r [keyDelayedIdx, keyBwState] :=
  partialTrie_normVals _ _ r _ (fun x hx => hx)

theorem forIn_normImpl {α : Type} (f : α × Transition → Bytes → Except String (ForInStep Bytes))
    (hf : ∀ M T r, f (M, normT r T) r = f (M, T) r)
    (hpost : ∀ M T r r', f (M, T) r = .ok (.yield r') → r' = T.postStateRoot) :
    ∀ (xs : List α) (ys : List Transition) (r : Bytes),
      forIn (xs.zip (normImpl r ys)) r f = forIn (xs.zip ys) r f
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [normImpl]
  | M :: xs, T :: ys, r => by
    simp only [normImpl, List.zip_cons_cons, List.forIn_cons]
    rw [hf M T r]
    cases hfr : f (M, T) r with
    | error e => rfl
    | ok st =>
      cases st with
      | done b => rfl
      | yield r' =>
        have := hpost M T r r' hfr
        subst this
        exact forIn_normImpl f hf hpost xs ys T.postStateRoot

section proj
variable (K : List (List Nat)) (R : Bytes) (s : StateWitnessD1)
@[simp] theorem normW_epochId : (normW K R s).epochId = s.epochId := rfl
@[simp] theorem normW_innerBytes : (normW K R s).innerBytes = s.innerBytes := rfl
@[simp] theorem normW_inner : (normW K R s).inner = s.inner := rfl
@[simp] theorem normW_arh : (normW K R s).appliedReceiptsHash = s.appliedReceiptsHash := rfl
@[simp] theorem normW_txs : (normW K R s).txs = s.txs := rfl
@[simp] theorem normW_newTxs : (normW K R s).newTxs = s.newTxs := rfl
@[simp] theorem normW_entries : (normW K R s).entries = normEntries s.entries := rfl
@[simp] theorem normW_main : (normW K R s).main = normMain K R s.main := rfl
@[simp] theorem normW_implicit : (normW K R s).implicit = normImpl s.main.postStateRoot s.implicit := rfl
@[simp] theorem normMain_post (t : Transition) : (normMain K R t).postStateRoot = t.postStateRoot := rfl
end proj

set_option maxHeartbeats 1000000 in
theorem checkD1_normal {cb w w' sw sw' : Bytes} {s : StateWitnessD1} {K : List (List Nat)} {R : Bytes}
    (hw : decodeWitnessFile w = .ok (sw, [])) (hw' : decodeWitnessFile w' = .ok (sw', []))
    (hl : lenT sw' ≤ lenT sw)
    (hs : decodeStateWitnessD1 sw = .ok s) (hs' : decodeStateWitnessD1 sw' = .ok (normW K R s))
    (hk : keysD1 cb w = .ok (K, R))
    (h : checkD1 cb w = .ok ()) : checkD1 cb w' = .ok () := by
  unfold checkD1 at h ⊢
  unfold keysD1 at hk
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [hc, ok_bind] at hk ⊢
  rw [hw, ok_bind] at h hk
  rw [hw', ok_bind]
  simp only [List.isEmpty_nil, check_true, ok_bind] at h hk ⊢
  obtain ⟨u2, h2, h⟩ := bind_ok h
  rw [h2, ok_bind] at hk
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  rw [decide_eq_true (Nat.le_trans hl hlen), check_true, ok_bind]
  rw [hs, ok_bind] at h hk
  rw [hs', ok_bind]
  simp only [normW_epochId, normW_innerBytes, normW_inner, normW_arh, normW_txs, normW_newTxs,
    normW_entries, normW_implicit,
    lookupLast_normEntries, distinctKeys_normEntries_length, normImpl_length]
  repeat lstep3
  -- base_state size: the normal form is no larger
  obtain ⟨u, ha, h⟩ := bind_ok h
  obtain ⟨u', hb, hk⟩ := bind_ok hk
  cases (ha.symm.trans hb)
  have hS : (List.map List.length s.main.values).foldl (· + ·) 0 ≤ 3000000 := by
    have := check_ok (by cases u; exact ha); simpa using this
  have hS' : (List.map List.length (normW K R s).main.values).foldl (· + ·) 0 ≤ 3000000 :=
    Nat.le_trans (sum_normVals_le _ _) hS
  rw [decide_eq_true hS', check_true, ok_bind]
  (try dsimp only at h); (try dsimp only at hk); (try dsimp only)
  lstep3
  -- the index lookup in the main trie, and the keys / root of the main build
  split at h
  all_goals first | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done) | skip
  rename_i v heq
  split at hk
  all_goals first | (rename_i heq2; cases (heq.symm.trans heq2); done) | skip
  rename_i v' heq2
  cases (heq.symm.trans heq2)
  obtain ⟨bsh, ha, h⟩ := bind_ok h
  obtain ⟨bsh', hb, hk⟩ := bind_ok hk
  have e : (Except.ok bsh : Except String (List Nat)) = Except.ok bsh' := ha.symm.trans hb
  cases e
  injection hk with hk
  cases hk
  -- now K, R are the run's keys and root: the normal form reveals the same tries
  rw [normW_main, ptrie_main1]
  simp only [heq]
  rw [ha, ok_bind, ptrie_main2]
  (try dsimp only at h); (try dsimp only)
  repeat lstep2
  rw [normMain_post]
  obtain ⟨u, ha, h⟩ := bind_ok h
  have hroot := check_ok (by cases u; exact ha)
  rw [ha, ok_bind]
  (try dsimp only at h); (try dsimp only)
  lstep2
  simp only [beq_iff_eq] at hroot
  rw [← hroot]
  rw [forIn_normImpl]
  · exact h
  · intro M T r
    simp only [ptrie_normT]
    rfl
  · intro M T r r' hf
    obtain ⟨t', -, hf⟩ := bind_ok hf
    obtain ⟨u, hc, hf⟩ := bind_ok hf
    have := check_ok (by cases u; exact hc)
    simp only [beq_iff_eq] at this
    simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
    rw [← hf, this]

set_option maxHeartbeats 1000000 in
/-- `keysD1` computes the same keys and root on the normal form. -/
theorem keysD1_normal {cb w w' sw sw' : Bytes} {s : StateWitnessD1} {K : List (List Nat)} {R : Bytes}
    (hw : decodeWitnessFile w = .ok (sw, [])) (hw' : decodeWitnessFile w' = .ok (sw', []))
    (hl : lenT sw' ≤ lenT sw)
    (hs : decodeStateWitnessD1 sw = .ok s) (hs' : decodeStateWitnessD1 sw' = .ok (normW K R s))
    (hk : keysD1 cb w = .ok (K, R)) : keysD1 cb w' = .ok (K, R) := by
  have h := hk
  unfold keysD1 at h ⊢
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [hc, ok_bind]
  rw [hw, ok_bind] at h
  rw [hw', ok_bind]
  simp only [List.isEmpty_nil, check_true, ok_bind] at h ⊢
  obtain ⟨u2, h2, h⟩ := bind_ok h
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  rw [decide_eq_true (Nat.le_trans hl hlen), check_true, ok_bind]
  rw [hs, ok_bind] at h
  rw [hs', ok_bind]
  simp only [normW_epochId, normW_innerBytes, normW_arh, normW_entries, normW_txs, normW_newTxs,
    lookupLast_normEntries, distinctKeys_normEntries_length]
  repeat lstep2
  obtain ⟨u, ha, h⟩ := bind_ok h
  have hS : (List.map List.length s.main.values).foldl (· + ·) 0 ≤ 3000000 := by
    have := check_ok (by cases u; exact ha); simpa using this
  have hS' : (List.map List.length (normW K R s).main.values).foldl (· + ·) 0 ≤ 3000000 :=
    Nat.le_trans (sum_normVals_le _ _) hS
  rw [decide_eq_true hS', check_true, ok_bind]
  (try dsimp only at h); (try dsimp only)
  lstep2
  split at h
  all_goals first | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done) | skip
  rename_i v heq
  obtain ⟨bsh, ha, h⟩ := bind_ok h
  injection h with h
  cases h
  rw [normW_main, ptrie_main1]
  simp only [heq]
  rw [ha, ok_bind]
  rfl

/-! ## The normal form is a fixed point -/

theorem qFor_normVals (vals q : List Bytes) (R : Bytes) (K : List (List Nat))
    (hq : ∀ x ∈ qFor (mkStore vals) trieFuel R K, x ∈ q) :
    qFor (mkStore (normVals vals q)) trieFuel R K = qFor (mkStore vals) trieFuel R K :=
  qFor_agree _ _ trieFuel R K (fun x hx => storeGet_normVals vals q x (hq x hx))

theorem normMain_idem (K : List (List Nat)) (R : Bytes) (t : Transition) :
    normMain K R (normMain K R t) = normMain K R t := by
  have h1 := qFor_normVals t.values (qFor (mkStore t.values) trieFuel R [keyBufferedIdx] ++
    qFor (mkStore t.values) trieFuel R K) R [keyBufferedIdx] (fun x hx => List.mem_append_left _ hx)
  have h2 := qFor_normVals t.values (qFor (mkStore t.values) trieFuel R [keyBufferedIdx] ++
    qFor (mkStore t.values) trieFuel R K) R K (fun x hx => List.mem_append_right _ hx)
  unfold normMain
  simp only [Transition.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  show normVals (normMain K R t).values _ = _
  unfold normMain
  dsimp only
  rw [h1, h2]
  exact normVals_idem _ _ _ (fun x hx => hx)

theorem normT_idem (r : Bytes) (t : Transition) : normT r (normT r t) = normT r t := by
  have h1 := qFor_normVals t.values (qFor (mkStore t.values) trieFuel r [keyDelayedIdx, keyBwState]) r
    [keyDelayedIdx, keyBwState] (fun x hx => hx)
  unfold normT
  simp only [Transition.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  show normVals (normT r t).values _ = _
  unfold normT
  dsimp only
  rw [h1]
  exact normVals_idem _ _ _ (fun x hx => hx)

theorem normImpl_idem : ∀ (r : Bytes) (ts : List Transition), normImpl r (normImpl r ts) = normImpl r ts
  | _, [] => rfl
  | r, t :: ts => by
    simp only [normImpl]
    rw [normT_idem]
    show normT r t :: normImpl (normT r t).postStateRoot (normImpl t.postStateRoot ts) = _
    rw [show (normT r t).postStateRoot = t.postStateRoot from rfl, normImpl_idem]

theorem normW_idem (K : List (List Nat)) (R : Bytes) (s : StateWitnessD1) :
    normW K R (normW K R s) = normW K R s := by
  unfold normW
  dsimp only
  rw [normEntries_idem, normMain_idem]
  rw [show (normMain K R s.main).postStateRoot = s.main.postStateRoot from rfl, normImpl_idem]

end ReexecV3D1
