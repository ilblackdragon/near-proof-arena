import ReexecV3D3.Helpers
import ReexecV3D3.StoreCongD3
import ReexecV3D3.NormBytes
import ReexecV3D3.Pools

/-!
# `checkD3` on a re-encoded witness (lockstep)

`checkD3_lockstep`: if `w'` is `w` with the ignored fields zeroed, the receipt-proof entries in
normal form, a main recorded store (`base_state ++ contract_code`) that answers every lookup like
`w`'s and is no larger, and implicit stores that reveal the same tries, then `checkD3` accepts
`w'` whenever it accepts `w`. The two runs are evaluated in lockstep: the claim and segment checks
see equal values, `lookupLastD2` / `distinctKeysD2` agree on the normal-form entries, the revealed
main trie is equal (`revealAll` reads the store only through `hGet`), the main transition is equal
(`applyNewChunkD2_d3_store`: the D3 hook reads the store only through `Env.codeOf`), the storage
bound only gets smaller, and every implicit transition reveals the same trie.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-- Implicit stores that reveal the same tries (from every root). -/
def IAg : List (List Bytes) → List Transition → Prop
  | _, [] => True
  | iv, t :: ts => (∀ r, revealTrie (iv.headD []) r = revealTrie t.values r) ∧ IAg iv.tail ts

theorem revealAll_ext {s s' : HStore} (h : ∀ x, hGet s' x = hGet s x) (fuel : Nat) (r : Bytes) :
    revealAll s' fuel r = revealAll s fuel r :=
  revealAll_agree s s' fuel r (fun x _ => h x)

theorem forIn_implV {α : Type} (f : α × Transition → Bytes → Except String (ForInStep Bytes))
    (hf : ∀ M T T' r, T'.postStateRoot = T.postStateRoot →
      revealTrie T'.values r = revealTrie T.values r → f (M, T') r = f (M, T) r) :
    ∀ (xs : List α) (iv : List (List Bytes)) (ys : List Transition) (r : Bytes), IAg iv ys →
      forIn (xs.zip (implV iv ys)) r f = forIn (xs.zip ys) r f
  | [], _, _, _, _ => by simp
  | _ :: _, _, [], _, _ => by simp [implV]
  | M :: xs, iv, T :: ys, r, ⟨hT, hrest⟩ => by
    simp only [implV, List.zip_cons_cons, List.forIn_cons]
    rw [hf M T (trV (iv.headD []) T) r rfl (hT r)]
    cases hfr : f (M, T) r with
    | error e => rfl
    | ok st =>
      cases st with
      | done b => rfl
      | yield r' => exact forIn_implV f hf xs iv.tail ys r' hrest

theorem applyNewChunkD2_env3 (cfg : Wasm.NearCfg) (prims : Prims) (ctx : ApplyCtx) (chainId : Bytes)
    (minStake : Nat) (sched : Scheduler.Params) (ts : Nat) (rv : Bytes) (eh : Nat)
    (vals : List (Bytes × Nat)) (s1 s2 : HStore) (hext : ∀ h, hGet s1 h = hGet s2 h) (pre : Bytes)
    (t : PTrie) (vu : Option ValidatorUpdateFacts) (lp : List (Bytes × Nat)) (inc : List Rcpt)
    (txs : List (TxD2 × Bool)) (oc : Congestion) :
    applyNewChunkD2 (D3.d3Hooks cfg) prims ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, s1, pre⟩
      t vu lp inc txs oc =
    applyNewChunkD2 (D3.d3Hooks cfg) prims ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, s2, pre⟩
      t vu lp inc txs oc :=
  applyNewChunkD2_d3_store cfg ⟨ctx, chainId, minStake, sched, ts, rv, eh, vals, .tip, pre⟩ hext prims t
    vu lp inc txs oc

set_option hygiene false in
/-- Lockstep of `h` and the goal: a bind is matched by its head's value; a `match` is split in
`h` (which splits the goal's identical `match` along). -/
macro "lsx" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h;
     rw [ha, ok_bind]; (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _)); split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (obtain ⟨_, ht, _⟩ := bind_ok h;
         simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at ht; done)
      | (cases h; done)
      | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
      | ((try dsimp only at h); (try dsimp only))))

theorem check_dec {p : Prop} {inst : Decidable p} (hp : p) (m : String) :
    NearSpecV3.check (@decide p inst) m = .ok () := by
  rw [@decide_eq_true p inst hp]; rfl

section proj
variable (mv : List Bytes) (iv : List (List Bytes)) (s : StateWitnessD2)
@[simp] theorem normWV_epochId : (normWV mv iv s).epochId = s.epochId := rfl
@[simp] theorem normWV_innerBytes : (normWV mv iv s).innerBytes = s.innerBytes := rfl
@[simp] theorem normWV_inner : (normWV mv iv s).inner = s.inner := rfl
@[simp] theorem normWV_arh : (normWV mv iv s).appliedReceiptsHash = s.appliedReceiptsHash := rfl
@[simp] theorem normWV_txs : (normWV mv iv s).txs = s.txs := rfl
@[simp] theorem normWV_newTxs : (normWV mv iv s).newTxs = s.newTxs := rfl
@[simp] theorem normWV_entries : (normWV mv iv s).entries = normEntriesD2 s.entries := rfl
@[simp] theorem normWV_main_values : (normWV mv iv s).main.values = mv := rfl
@[simp] theorem normWV_main_post : (normWV mv iv s).main.postStateRoot = s.main.postStateRoot := rfl
@[simp] theorem normWV_implicit : (normWV mv iv s).implicit = implV iv s.implicit := rfl
end proj

set_option maxHeartbeats 4000000 in
/-- **Lockstep.** `checkD3` accepts the re-encoded witness `w'` if it accepts `w`. -/
theorem checkD3_lockstep {cb w w' sw sw' : Bytes} {codes codes' : List Bytes} {s : StateWitnessD2}
    {mv : List Bytes} {iv : List (List Bytes)}
    (hw : decodeWitnessFile w = .ok (sw, codes)) (hw' : decodeWitnessFile w' = .ok (sw', codes'))
    (hl : lenT sw' ≤ 8388608)
    (hs : decodeStateWitnessD2 sw = .ok s) (hs' : decodeStateWitnessD2 sw' = .ok (normWV mv iv s))
    (hst : ∀ h, hGet (mkHStore (mv ++ codes')) h = hGet (mkHStore (s.main.values ++ codes)) h)
    (hsum : ((mv ++ codes').map List.length).foldl (· + ·) 0 ≤
      ((s.main.values ++ codes).map List.length).foldl (· + ·) 0)
    (himpl : IAg iv s.implicit)
    (h : D3.checkD3 cb w = .ok ()) : D3.checkD3 cb w' = .ok () := by
  unfold D3.checkD3 checkD2Core at h ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [hc, ok_bind]
  rw [hw, ok_bind] at h
  rw [hw', ok_bind]
  dsimp only at h ⊢
  obtain ⟨u2, h2, h⟩ := bind_ok h
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  rw [decide_eq_true hl, check_true, ok_bind]
  rw [hs, ok_bind] at h
  rw [hs', ok_bind]
  dsimp only [normWV_epochId, normWV_innerBytes, normWV_arh, normWV_txs, normWV_newTxs,
    normWV_entries, normWV_implicit, normWV_main_values, normWV_main_post]
  simp only [lookupLastD2_normEntriesD2, distinctKeysD2_normEntriesD2_length, implV_length]
  repeat lsx
  split at h
  · lsx
    rw [revealAll_ext (s := mkHStore (s.main.values ++ codes)) (s' := mkHStore (mv ++ codes')) hst]
    lsx
    rw [applyNewChunkD2_env3 (s2 := mkHStore (s.main.values ++ codes)) (hext := hst)]
    lsx
    obtain ⟨u, ha, h⟩ := bind_ok h
    have hS := check_ok (by cases u; exact ha)
    simp only [decide_eq_true_eq] at hS
    rw [check_dec (Nat.le_trans (Nat.add_le_add_right hsum _) hS), ok_bind]
    (try dsimp only at h); (try dsimp only)
    lsx
    lsx
    lsx
    rw [forIn_implV _ ?hf _ iv s.implicit _ himpl]
    · exact h
    · intro M T T' r hp hr
      dsimp only
      rw [hp, hr]
  · obtain ⟨_, ht, _⟩ := bind_ok h
    cases ht

end ReexecV3D3
