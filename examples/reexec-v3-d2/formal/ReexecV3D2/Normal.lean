import ReexecV3D2.NormalDefs
import ReexecV3D2.TrieQ
import ReexecV3D2.Canon
import ReexecV3D2.StoreCong

namespace ReexecV3D2

open NearSpec NearSpecV3 NearSpecV3.D2

set_option hygiene false in
/-- One lockstep step of `h` (the accepting run of `checkD2`), `hk` (the run of its
verbatim copy `keysD2`, whose auxiliary matchers are different constants, so results are
matched by definitional unification) and the goal (`checkD2` on the normal form). -/
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

theorem sum_normValsH_le (vals q : List Bytes) :
    ((normValsH vals q).map List.length).foldl (· + ·) 0 ≤ (vals.map List.length).foldl (· + ·) 0 :=
  sum_le_of_nodup_subset _ _ (normValsH_nodup vals q) (fun _ hx => mem_normValsH hx)

theorem sum_normMain_le (R : Bytes) (t : Transition) :
    ((normMain R t).values.map List.length).foldl (· + ·) 0 ≤ (t.values.map List.length).foldl (· + ·) 0 :=
  sum_normValsH_le _ _

theorem reveal_main (R : Bytes) (t : Transition) :
    revealAll (mkHStore (normMain R t).values) revealFuel R = revealAll (mkHStore t.values) revealFuel R :=
  revealAll_normValsH _ _ R (fun x hx => hx)

theorem reveal_normT (r : Bytes) (t : Transition) :
    revealTrie (normT r t).values r = revealTrie t.values r :=
  revealAll_normValsH _ _ r (fun x hx => hx)

theorem applyNewChunkD2_env (prims : Prims) (ctx : ApplyCtx) (chainId : Bytes) (minStake : Nat)
    (sched : Scheduler.Params) (ts : Nat) (rv : Bytes) (eh : Nat) (vals : List (Bytes × Nat))
    (s1 s2 : HStore) (pre : Bytes) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lp : List (Bytes × Nat)) (inc : List Rcpt) (txs : List (TxD2 × Bool)) (oc : Congestion) :
    applyNewChunkD2 d2Hooks prims ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, s1, pre⟩ t vu lp inc txs oc =
    applyNewChunkD2 d2Hooks prims ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, s2, pre⟩ t vu lp inc txs oc :=
  applyNewChunkD2_store ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, .tip, pre⟩ s1 s2 prims t vu lp inc txs oc

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
variable (R : Bytes) (s : StateWitnessD2)
@[simp] theorem normW_epochId : (normW R s).epochId = s.epochId := rfl
@[simp] theorem normW_innerBytes : (normW R s).innerBytes = s.innerBytes := rfl
@[simp] theorem normW_inner : (normW R s).inner = s.inner := rfl
@[simp] theorem normW_arh : (normW R s).appliedReceiptsHash = s.appliedReceiptsHash := rfl
@[simp] theorem normW_txs : (normW R s).txs = s.txs := rfl
@[simp] theorem normW_newTxs : (normW R s).newTxs = s.newTxs := rfl
@[simp] theorem normW_entries : (normW R s).entries = normEntriesD2 s.entries := rfl
@[simp] theorem normW_main : (normW R s).main = normMain R s.main := rfl
@[simp] theorem normW_implicit : (normW R s).implicit = normImpl s.main.postStateRoot s.implicit := rfl
@[simp] theorem normMain_post (t : Transition) : (normMain R t).postStateRoot = t.postStateRoot := rfl
@[simp] theorem normT_post (t : Transition) : (normT R t).postStateRoot = t.postStateRoot := rfl
end proj

set_option maxHeartbeats 2000000 in
theorem checkD2_normal {cb w w' sw sw' : Bytes} {s : StateWitnessD2} {R : Bytes}
    (hw : decodeWitnessFile w = .ok (sw, [])) (hw' : decodeWitnessFile w' = .ok (sw', []))
    (hl : lenT sw' ≤ lenT sw)
    (hs : decodeStateWitnessD2 sw = .ok s) (hs' : decodeStateWitnessD2 sw' = .ok (normW R s))
    (hk : keysD2 cb w = .ok R)
    (h : checkD2 cb w = .ok ()) : checkD2 cb w' = .ok () := by
  unfold checkD2 checkD2Core at h ⊢
  unfold keysD2 at hk
  simp only [Bool.not_false, ite_true] at h hk ⊢
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [hc, ok_bind] at hk ⊢
  rw [hw, ok_bind] at h hk
  rw [hw', ok_bind]
  simp only [List.isEmpty_nil, check_true, ok_bind, List.append_nil] at h hk ⊢
  obtain ⟨u2, h2, h⟩ := bind_ok h
  rw [h2, ok_bind] at hk
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  rw [decide_eq_true (Nat.le_trans hl hlen), check_true, ok_bind]
  rw [hs, ok_bind] at h hk
  rw [hs', ok_bind]
  simp only [normW_epochId, normW_innerBytes, normW_arh, normW_txs, normW_newTxs,
    normW_entries, normW_implicit,
    lookupLastD2_normEntriesD2, distinctKeysD2_normEntriesD2_length, normImpl_length]
  repeat lstep3
  obtain ⟨sch, hsch, h⟩ := bind_ok h
  split at hk
  · cases hk
    split
    · rename_i p hp
      have e : some p = some sch := by rw [← hp]; cases hsch; rfl
      injection e with e
      subst e
      rw [show (pure p : Except String Scheduler.Params) = Except.ok p from rfl, ok_bind]
      (try dsimp only at h); (try dsimp only)
      rw [normW_main, reveal_main]
      lstep2
      rw [applyNewChunkD2_env (s2 := mkHStore s.main.values)]
      lstep2
      -- the storage-proof bound: the normal form is no larger
      obtain ⟨u, ha, h⟩ := bind_ok h
      have hS := check_ok (by cases u; exact ha)
      simp only [decide_eq_true_eq] at hS
      rw [decide_eq_true (Nat.le_trans (Nat.add_le_add_right (sum_normMain_le _ _) _) hS), check_true, ok_bind]
      (try dsimp only at h); (try dsimp only)
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
        simp only [reveal_normT, normT_post]
      · intro M T r r' hf
        dsimp only at hf
        split at hf
        · obtain ⟨M', -, hf⟩ := bind_ok hf
          obtain ⟨t', -, hf⟩ := bind_ok hf
          obtain ⟨u, hc, hf⟩ := bind_ok hf
          have := check_ok (by cases u; exact hc)
          simp only [beq_iff_eq] at this
          simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
          rw [← hf, this]
        · obtain ⟨M', hM, -⟩ := bind_ok hf
          cases hM
    · rename_i hp
      exfalso
      have e : (none : Option Scheduler.Params) = some sch := by rw [← hp]; cases hsch; rfl
      cases e
  · cases hk

set_option maxHeartbeats 1000000 in
/-- `keysD2` computes the same root on the normal form (it never reads `base_state`). -/
theorem keysD2_normal {cb w w' sw sw' : Bytes} {s : StateWitnessD2} {R : Bytes}
    (hw : decodeWitnessFile w = .ok (sw, [])) (hw' : decodeWitnessFile w' = .ok (sw', []))
    (hl : lenT sw' ≤ lenT sw)
    (hs : decodeStateWitnessD2 sw = .ok s) (hs' : decodeStateWitnessD2 sw' = .ok (normW R s))
    (hk : keysD2 cb w = .ok R) : keysD2 cb w' = .ok R := by
  have h := hk
  unfold keysD2 at h ⊢
  simp only [Bool.not_false, ite_true] at h ⊢
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
    lookupLastD2_normEntriesD2, distinctKeysD2_normEntriesD2_length]
  exact h

/-! ## The normal form is a fixed point -/

theorem normMain_idem (R : Bytes) (t : Transition) : normMain R (normMain R t) = normMain R t := by
  have h1 := qAll_normValsH t.values (qAll (mkHStore t.values) revealFuel R) R (fun x hx => hx)
  unfold normMain
  simp only [Transition.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  show normValsH (normMain R t).values _ = _
  unfold normMain
  dsimp only
  rw [h1]
  exact normValsH_idem _ _ _ (fun x hx => hx)

theorem normT_idem (r : Bytes) (t : Transition) : normT r (normT r t) = normT r t := by
  have h1 := qAll_normValsH t.values (qAll (mkHStore t.values) revealFuel r) r (fun x hx => hx)
  unfold normT
  simp only [Transition.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  show normValsH (normT r t).values _ = _
  unfold normT
  dsimp only
  rw [h1]
  exact normValsH_idem _ _ _ (fun x hx => hx)

theorem normImpl_idem : ∀ (r : Bytes) (ts : List Transition), normImpl r (normImpl r ts) = normImpl r ts
  | _, [] => rfl
  | r, t :: ts => by
    simp only [normImpl]
    rw [normT_idem]
    show normT r t :: normImpl (normT r t).postStateRoot (normImpl t.postStateRoot ts) = _
    rw [show (normT r t).postStateRoot = t.postStateRoot from rfl, normImpl_idem]

theorem normW_idem (R : Bytes) (s : StateWitnessD2) : normW R (normW R s) = normW R s := by
  unfold normW
  dsimp only
  rw [normEntriesD2_idem, normMain_idem]
  rw [show (normMain R s.main).postStateRoot = s.main.postStateRoot from rfl, normImpl_idem]

end ReexecV3D2
