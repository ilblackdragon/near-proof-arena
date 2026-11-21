import NearSpecV3.E2E.Engine
import NearSpecV3.Successor.TierO3Inv

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# E2E-M11g, item 3: the engine's overlay invariant

Every overlay the engine machine (`Engine.lean`, `stepM`) holds is built from `Ovl.ofTrie P.t`
by `Ovl.set`, `Ovl.remove`, `Ovl.commit` and `Ovl.rollback` (`setAcct`/`setAK` are `set`); no
program the engine runs (the recorder programs of `StorageExecution`, the logged store programs of
`Logged/D2*.lean` and `Successor/{QueueExecution,GlobalExecution}.lean`, the Wasm write-back of
`functionCallRecordedF`) builds an `Ovl` otherwise. This file proves it, as a pass over all of them:

* **`OG t S o`**: the overlay's trie is `t`, its committed keys are distinct, and they include
  the list `S`. `set`/`remove`/`rollback` leave `trie` and `committed` alone; `commit` folds
  `kvPut`, which updates a key in place or appends a new one (`keys_kvPut`), so the committed keys
  stay distinct and only grow.
* **Logged store programs** (`…L_og`): `LOk` (`TierO3Inv.lean`) by the walk `olok`.
* **Recorder programs** (`…_og`): `Post` (`Engine.lean`) by the walk `mwalk`, which dispatches on
  the program's head (`post_head`: `pure`, `throw`, `if`, `try`, `>>=`, `match`, `let`) and closes
  a call by its lemma (`m_close`, guarded by the callee's name, `closeHeads`, so that unification
  never unfolds an unrelated program such as the Wasm interpreter behind `vmCall`). A `do` block's
  join point `have jp := v; b` is not inlined (that copies `v` into every branch): `post_let`
  replaces it by its specification — every call whose overlay arguments satisfy `OG t S` satisfies
  the postcondition (`Post.have_jp`) — proved once for `v` and applied at each call
  (`post_jpcall`).
* **One step** (`stepM_pq`): from a position whose overlay satisfies `OG t S` the machine goes to a
  position whose overlay satisfies `OG t S`, or to `done out` whose `out.committed` (the sorted
  final committed overlay, `finalizeStep`) contains `S`. The first step starts from
  `Ovl.ofTrie P.t` (`start_pq`).
* **Runs**: every overlay reached from `start` has trie `P.t` and distinct committed keys
  (`reach_trie_nodup`); its committed keys are in `out.committed` of every accepting run through
  it (`reach_covered`). The machine is deterministic, so an accepting run has one output
  (`done_unique`).

Nothing here changes a definition the checker uses.
-/

namespace NearSpecV3.E2E.OvlInv
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution

/-! ## Keys of an overlay map and `kvPut` -/

/-- The keys of a key → value list. -/
abbrev keys (l : List (Bytes × Option Bytes)) : List Bytes := l.map Prod.fst

theorem keys_kvPut (k : Bytes) (v : Option Bytes) :
    ∀ l : List (Bytes × Option Bytes),
      keys (kvPut k v l) = if k ∈ keys l then keys l else keys l ++ [k]
  | [] => by simp [kvPut]
  | (k', v') :: rest => by
    unfold kvPut
    by_cases h : k' = k
    · subst h; simp
    · have hb : (k' == k) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.mem_cons,
        keys_kvPut k v rest]
      have : ¬ k = k' := fun e => h e.symm
      by_cases hk : k ∈ keys rest <;> simp [hk, this]

theorem nodup_kvPut (k : Bytes) (v : Option Bytes) (l : List (Bytes × Option Bytes))
    (h : (keys l).Nodup) : (keys (kvPut k v l)).Nodup := by
  rw [keys_kvPut]
  split
  · exact h
  · rename_i hk
    exact List.nodup_append.mpr ⟨h, by simp, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; intro e; subst e; exact hk ha⟩

theorem mem_kvPut (k : Bytes) (v : Option Bytes) (l : List (Bytes × Option Bytes)) (x : Bytes)
    (h : x ∈ keys l) : x ∈ keys (kvPut k v l) := by
  rw [keys_kvPut]
  split
  · exact h
  · exact List.mem_append_left _ h

/-- The fold `Ovl.commit` runs. -/
def commitFold (p c : List (Bytes × Option Bytes)) : List (Bytes × Option Bytes) :=
  p.foldl (fun c (k, v) => kvPut k v c) c

theorem commitFold_nodup : ∀ (p c : List (Bytes × Option Bytes)), (keys c).Nodup →
    (keys (commitFold p c)).Nodup
  | [], _, h => h
  | (k, v) :: rest, c, h => commitFold_nodup rest (kvPut k v c) (nodup_kvPut k v c h)

theorem commitFold_mem : ∀ (p c : List (Bytes × Option Bytes)) (x : Bytes), x ∈ keys c →
    x ∈ keys (commitFold p c)
  | [], _, _, h => h
  | (k, v) :: rest, c, x, h => commitFold_mem rest (kvPut k v c) x (mem_kvPut k v c x h)

theorem commit_committed (o : Ovl) : o.commit.committed = commitFold o.prosp o.committed := rfl

/-! ## The overlay predicate -/

/-- **The overlay invariant**: trie `t`, distinct committed keys, and the committed keys include
`S`. -/
structure OG (t : PTrie) (S : List Bytes) (o : Ovl) : Prop where
  trie : o.trie = t
  nodup : (keys o.committed).Nodup
  incl : ∀ k ∈ S, k ∈ keys o.committed

section og
variable {t : PTrie} {S : List Bytes}

theorem OG.ofTrie (t : PTrie) : OG t [] (Ovl.ofTrie t) :=
  ⟨rfl, List.nodup_nil, fun _ h => by cases h⟩

theorem OG.self {o : Ovl} (h1 : o.trie = t) (h2 : (keys o.committed).Nodup) :
    OG t (keys o.committed) o := ⟨h1, h2, fun _ h => h⟩

theorem OG.set {o : Ovl} (h : OG t S o) (k v : Bytes) : OG t S (o.set k v) := ⟨h.1, h.2, h.3⟩
theorem OG.remove {o : Ovl} (h : OG t S o) (k : Bytes) : OG t S (o.remove k) := ⟨h.1, h.2, h.3⟩
theorem OG.rollback {o : Ovl} (h : OG t S o) : OG t S o.rollback := ⟨h.1, h.2, h.3⟩
theorem OG.setAcct {o : Ovl} (h : OG t S o) (a : Bytes) (x : Acct) : OG t S (o.setAcct a x) :=
  ⟨h.1, h.2, h.3⟩
theorem OG.setAK {o : Ovl} (h : OG t S o) (a : Bytes) (pk : PublicKey) (k : AK) :
    OG t S (o.setAK a pk k) := ⟨h.1, h.2, h.3⟩
theorem OG.commit {o : Ovl} (h : OG t S o) : OG t S o.commit :=
  ⟨h.1, commitFold_nodup _ _ h.2, fun k hk => commitFold_mem _ _ k (h.3 k hk)⟩

theorem OG.foldl {β : Type} {g : Ovl → β → Ovl} (hg : ∀ o b, OG t S o → OG t S (g o b)) :
    ∀ (l : List β) (o : Ovl), OG t S o → OG t S (l.foldl g o)
  | [], _, h => h
  | b :: l, o, h => OG.foldl hg l (g o b) (hg o b h)

theorem OG.afoldl {β : Type} {g : Ovl → β → Ovl} (hg : ∀ o b, OG t S o → OG t S (g o b))
    (l : Array β) (o : Ovl) (h : OG t S o) : OG t S (l.foldl g o) := by
  rw [← Array.foldl_toList]
  exact OG.foldl hg l.toList o h

theorem OG.foldl_rs {β : Type} {g : RS → β → RS} (hg : ∀ r b, OG t S r.o → OG t S (g r b).o) :
    ∀ (l : List β) (r : RS), OG t S r.o → OG t S (l.foldl g r).o
  | [], _, h => h
  | b :: l, r, h => OG.foldl_rs hg l (g r b) (hg r b h)

theorem OG.ite {c : Prop} [Decidable c] {a b : Ovl} (ha : OG t S a) (hb : OG t S b) :
    OG t S (if c then a else b) := by
  split <;> assumption

theorem OG.mono {S' : List Bytes} {o : Ovl} (h : OG t S o) (hs : ∀ k ∈ S', k ∈ S) : OG t S' o :=
  ⟨h.1, h.2, fun k hk => h.3 k (hs k hk)⟩

end og

/-- Close a leaf: an overlay built from overlays satisfying `OG` by the overlay operations. -/
syntax "og_leaf" : tactic
macro_rules | `(tactic| og_leaf) => `(tactic| (
  (try dsimp only [RS.setMeta, RS.writeDelayedIdx, ForInStep.value] at *)
  repeat' (first
    | assumption
    | exact True.intro
    | exact OG.ofTrie _
    | (refine OG.set ?_ _ _)
    | (refine OG.remove ?_ _)
    | (refine OG.commit ?_)
    | (refine OG.rollback ?_)
    | (refine OG.setAcct ?_ _ _)
    | (refine OG.setAK ?_ _ _ _)
    | (refine OG.foldl (fun _ _ _ => ?_) _ _ ?_)
    | (refine OG.afoldl (fun _ _ _ => ?_) _ _ ?_)
    | (refine OG.foldl_rs (fun _ _ _ => ?_) _ _ ?_)
    | (split <;> (try dsimp only at *))
    | (dsimp only at *))))

/-! ## Logged store programs keep `OG` -/

/-- Close a logged store program by a proved fact (extended below, function by function). -/
syntax "ogl_close" : tactic
macro_rules | `(tactic| ogl_close) => `(tactic| fail "ogl_close")

/-- The walk over a logged store program (`TierO3Inv`'s `lok` with the `OG` leaves). -/
macro "olok" : tactic => `(tactic|
  repeat' (first
    | (refine LOk.pure _ ?_; focus (og_leaf; done))
    | (exact LOk.throw _)
    | (exact LOk.throwThe _)
    | (exact fun _ => SOk.err _)
    | (simp only [pure_bind])
    | ogl_close
    | (show OG _ _ _; og_leaf; done)
    | ((refine LOk.bind (by ogl_close) fun _ _ => ?_); try dsimp only)
    | ((refine LOk.bind (ite_pure_og _ _ _ ?_ ?_) fun _ _ => ?_); try dsimp only)
    | ((refine LOk.bind (LOk.tru _) fun _ _ => ?_); try dsimp only)
    | (refine LOk.ite _ (fun _ => ?_) (fun _ => ?_))
    | (dsimp only)
    | (split <;> (try dsimp only))))

section queues
variable (t : PTrie) (S : List Bytes)

theorem ite_pure_og {c : Prop} [Decidable c] {x : LM RS} (v : RS) (hv : OG t S v.o)
    (hx : LOk (fun y : RS => OG t S y.o) x) :
    LOk (fun y : RS => OG t S y.o) (if c then pure v else x) :=
  LOk.ite _ (fun _ => LOk.pure _ hv) fun _ => hx

theorem groupsPopBackL_og (rs : RS) (s : Nat) (m : Meta) (h : OG t S rs.o) :
    LOk (fun x : RS × Meta × Option (Nat × Nat) => OG t S x.1.o) (groupsPopBackL rs s m) := by
  unfold groupsPopBackL; olok

theorem groupsPushBackL_og (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) (h : OG t S rs.o) :
    LOk (fun x : RS × Meta => OG t S x.1.o) (groupsPushBackL rs s m size gas) := by
  unfold groupsPushBackL; olok

macro_rules | `(tactic| ogl_close) => `(tactic| exact groupsPopBackL_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact groupsPushBackL_og _ _ _ _ _ _ _ (by assumption))

theorem metaPushedL_og (rs : RS) (s size gas : Nat) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (metaPushedL rs s size gas) := by
  unfold metaPushedL; olok

theorem metaPoppedL_og (rs : RS) (s size gas : Nat) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (metaPoppedL rs s size gas) := by
  unfold metaPoppedL; olok

macro_rules | `(tactic| ogl_close) => `(tactic| exact metaPushedL_og _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact metaPoppedL_og _ _ _ _ _ _ (by assumption))

theorem bufferReceiptL_og (rs : RS) (r : Rcpt) (size gas shard : Nat) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (bufferReceiptL rs r size gas shard) := by
  unfold bufferReceiptL; olok

macro_rules | `(tactic| ogl_close) => `(tactic| exact bufferReceiptL_og _ _ _ _ _ _ _ (by assumption))

theorem forwardOrBufferL_og (env : Env) (rs : RS) (r : Rcpt) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (forwardOrBufferL env rs r) := by
  unfold forwardOrBufferL; olok

theorem forwardOrBufferLWith_og (pol : QueuePolicy) (env : Env) (rs : RS) (r : Rcpt)
    (h : OG t S rs.o) : LOk (fun x : RS => OG t S x.o) (forwardOrBufferLWith pol env rs r) := by
  unfold forwardOrBufferLWith; olok

theorem fwdLoopL_og (env : Env) (s : Nat) : ∀ fuel i (acc : RS × Nat × List (Nat × Nat)),
    OG t S acc.1.o →
    LOk (fun x : RS × Nat × List (Nat × Nat) => OG t S x.1.o) (fwdLoopL env s fuel i acc)
  | 0, _, _, h => LOk.pure _ h
  | fuel + 1, i, (rs, k, pops), h => by
    unfold fwdLoopL
    dsimp only at h
    olok
    all_goals exact fwdLoopL_og env s fuel _ _ h

theorem fwdLoopLWith_og (pol : QueuePolicy) (env : Env) (s : Nat) :
    ∀ fuel i (acc : RS × Nat × List (Nat × Nat)), OG t S acc.1.o →
    LOk (fun x : RS × Nat × List (Nat × Nat) => OG t S x.1.o) (fwdLoopLWith pol env s fuel i acc)
  | 0, _, _, h => LOk.pure _ h
  | fuel + 1, i, (rs, k, pops), h => by
    unfold fwdLoopLWith
    dsimp only at h
    olok
    all_goals exact fwdLoopLWith_og pol env s fuel _ _ h

theorem forwardFromBufferToShardL_og (env : Env) (rs : RS) (s : Nat) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (forwardFromBufferToShardL env rs s) := by
  unfold forwardFromBufferToShardL
  refine LOk.bind (fwdLoopL_og t S env s _ _ _ h) fun ⟨rs', k, pops⟩ h' => ?_
  dsimp only at h' ⊢
  refine LOk.foldlM _ _ ?_ fun a _ ha => metaPoppedL_og t S _ _ _ _ ha
  og_leaf

theorem forwardFromBufferToShardLWith_og (pol : QueuePolicy) (env : Env) (rs : RS) (s : Nat)
    (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (forwardFromBufferToShardLWith pol env rs s) := by
  unfold forwardFromBufferToShardLWith
  refine LOk.bind (fwdLoopLWith_og t S pol env s _ _ _ h) fun ⟨rs', k, pops⟩ h' => ?_
  dsimp only at h' ⊢
  refine LOk.foldlM _ _ ?_ fun a _ ha => metaPoppedL_og t S _ _ _ _ ha
  og_leaf

theorem forwardFromBufferL_og (env : Env) (rs : RS) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (forwardFromBufferL env rs) := by
  unfold forwardFromBufferL
  refine LOk.ite _ (fun _ => LOk.throw _) fun _ => ?_
  exact LOk.foldlM (Q := fun x : RS => OG t S x.o) _ _ h
    fun a _ ha => forwardFromBufferToShardL_og t S _ _ _ ha

theorem forwardFromBufferLWith_og (pol : QueuePolicy) (env : Env) (rs : RS) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (forwardFromBufferLWith pol env rs) := by
  unfold forwardFromBufferLWith
  refine LOk.ite _ (fun _ => LOk.throw _) fun _ => ?_
  exact LOk.foldlM (Q := fun x : RS => OG t S x.o) _ _ h
    fun a _ ha => forwardFromBufferToShardLWith_og t S _ _ _ _ ha

theorem forwardFromBufferV3L_og (ga : Bool) (env : Env) (rs : RS) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (StorageExecution.forwardFromBufferV3L ga env rs) := by
  unfold StorageExecution.forwardFromBufferV3L
  refine LOk.bind (LOk.foldlM (Q := fun x : RS => OG t S x.o) _ _ h fun a _ ha => ?_) fun a ha => ?_
  · split
    · exact forwardFromBufferToShardLWith_og t S _ _ _ _ ha
    · exact forwardFromBufferToShardL_og t S _ _ _ ha
  · olok

theorem delayPushL_og (rs : RS) (r : Rcpt) (h : OG t S rs.o) :
    LOk (fun x : RS => OG t S x.o) (delayPushL rs r) := by
  unfold delayPushL; olok

theorem delayPopL_og (env : Env) : ∀ fuel (rs : RS), OG t S rs.o →
    LOk (fun x : RS × Option Rcpt => OG t S x.1.o) (delayPopL env fuel rs)
  | 0, _, h => LOk.pure _ h
  | fuel + 1, rs, h => by
    unfold delayPopL
    olok
    all_goals exact delayPopL_og env fuel _ (by og_leaf)

theorem delayPopLWith_og (pol : QueuePolicy) (env : Env) : ∀ fuel (rs : RS), OG t S rs.o →
    LOk (fun x : RS × Option Rcpt => OG t S x.1.o) (delayPopLWith pol env fuel rs)
  | 0, _, h => LOk.pure _ h
  | fuel + 1, rs, h => by
    unfold delayPopLWith
    olok
    all_goals exact delayPopLWith_og pol env fuel _ (by og_leaf)

macro_rules | `(tactic| ogl_close) => `(tactic| exact forwardOrBufferL_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact forwardOrBufferLWith_og _ _ _ _ _ _ (by assumption))

theorem processTxD2L_og (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : OG t S rs.1.o) :
    LOk (fun x : RS × List Bytes => OG t S x.1.o) (processTxD2L env rs tf) := by
  obtain ⟨rs, seen⟩ := rs
  dsimp only at h
  unfold processTxD2L
  olok

theorem validatorUpdateL_og (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts)
    (last : List (Bytes × Nat)) (h : OG t S o) :
    LOk (fun x : Ovl => OG t S x) (validatorUpdateL l own o f last) := by
  unfold validatorUpdateL
  refine LOk.bind (LOk.foldlM (Q := fun x : Ovl => OG t S x) _ _ h fun a _ ha => ?_) fun a ha => ?_
  · olok
  · olok

theorem schedOvlL_og (prims : Prims) (ctx : ApplyCtx) (o : Ovl) (h : OG t S o) :
    LOk (fun x : Ovl × SchedOut => OG t S x.1) (schedOvlL prims ctx o) := by
  unfold schedOvlL; olok


end queues

section acts
variable (t : PTrie) (S : List Bytes) (c : ActCtx) (st : ActSt) (res : AR) (h : OG t S st.o)
include h

theorem actCreateAccountL_og : LOk (fun p : ActSt × AR => OG t S p.1.o) (actCreateAccountL c st res) := by
  unfold actCreateAccountL; olok
theorem actDeployL_og (code : Bytes) : LOk (fun p : ActSt × AR => OG t S p.1.o) (actDeployL c st res code) := by
  unfold actDeployL; olok
theorem actTransferL_og (d : Nat) : LOk (fun p : ActSt × AR => OG t S p.1.o) (actTransferL c st res d) := by
  unfold actTransferL; olok
theorem actStakeL_og (s : Nat) (pk : PublicKey) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actStakeL c st res s pk) := by
  unfold actStakeL; olok
theorem actAddKeyL_og (pk : PublicKey) (ak : AK) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actAddKeyL c st res pk ak) := by
  unfold actAddKeyL; olok
theorem actDeleteKeyL_og (pk : PublicKey) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actDeleteKeyL c st res pk) := by
  unfold actDeleteKeyL; olok
theorem actDeleteAccountL_og (ben : Bytes) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actDeleteAccountL c st res ben) := by
  unfold actDeleteAccountL; olok
theorem actToGasKeyL_og (pk : PublicKey) (d : Nat) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actToGasKeyL c st res pk d) := by
  unfold actToGasKeyL; olok
theorem actFromGasKeyL_og (pk : PublicKey) (a : Nat) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actFromGasKeyL c st res pk a) := by
  unfold actFromGasKeyL; olok
theorem actDelegateL_og (d : Delegate) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (actDelegateL c st res d) := by
  unfold actDelegateL; olok

end acts


macro_rules | `(tactic| ogl_close) => `(tactic| first
  | exact actCreateAccountL_og _ _ _ _ _ (by assumption)
  | exact actDeployL_og _ _ _ _ _ (by assumption) _
  | exact actTransferL_og _ _ _ _ _ (by assumption) _
  | exact actStakeL_og _ _ _ _ _ (by assumption) _ _
  | exact actAddKeyL_og _ _ _ _ _ (by assumption) _ _
  | exact actDeleteKeyL_og _ _ _ _ _ (by assumption) _
  | exact actDeleteAccountL_og _ _ _ _ _ (by assumption) _
  | exact actToGasKeyL_og _ _ _ _ _ (by assumption) _ _
  | exact actFromGasKeyL_og _ _ _ _ _ (by assumption) _ _
  | exact actDelegateL_og _ _ _ _ _ (by assumption) _)

section global
variable (t : PTrie) (S : List Bytes)

/-- **The non-call actions keep `OG`** (`ordinaryAction`'s store program). -/
theorem applyActionL_og (c : ActCtx) (st : ActSt) (a : Act) (h : OG t S st.o) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (applyActionL d2HooksL c st a) := by
  unfold applyActionL; olok

theorem useGlobalL_og (c : ActCtx) (st : ActSt) (res : AR) (g : D3.L4.Gci) (h : OG t S st.o) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (GlobalExecution.useGlobalL c st res g) := by
  unfold GlobalExecution.useGlobalL; olok

theorem deployGlobalL_og (c : ActCtx) (st : ActSt) (res : AR) (d : D3.L4.DeployGlobal)
    (h : OG t S st.o) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (GlobalExecution.deployGlobalL c st res d) := by
  unfold GlobalExecution.deployGlobalL; olok

macro_rules | `(tactic| ogl_close) => `(tactic| exact useGlobalL_og _ _ _ _ _ _ (by assumption))

theorem stateInitL_og (c : ActCtx) (st : ActSt) (res : AR) (d : D3.L4.Dsi) (h : OG t S st.o) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (GlobalExecution.stateInitL c st res d) := by
  unfold GlobalExecution.stateInitL
  dsimp only
  split
  · refine LOk.bind (useGlobalL_og t S _ _ _ _ h) fun p hp => ?_
    refine LOk.ite _ (fun _ => ?_) (fun _ => ?_)
    · olok
    · split
      · refine LOk.bind (LOk.foldlM (Q := fun x : Ovl × Nat => OG t S x.1) _ _ hp
          fun a _ ha => ?_) fun a ha => ?_
        · olok
        · olok
      · olok
  · olok

theorem applyGlobalActionL_og (c : ActCtx) (st : ActSt) (res : AR) (b : Base) (h : OG t S st.o) :
    LOk (fun p : ActSt × AR => OG t S p.1.o) (GlobalExecution.applyGlobalActionL c st res b) := by
  unfold GlobalExecution.applyGlobalActionL
  split
  · exact deployGlobalL_og t S _ _ _ _ h
  · exact useGlobalL_og t S _ _ _ _ h
  · exact stateInitL_og t S _ _ _ _ h
  · exact LOk.throw _

theorem applyDistributionL_og (env : Env) (rs : RS) (r : Rcpt) (d : Distribution)
    (h : OG t S rs.o) :
    LOk (fun p : RS × Option Rcpt × Option Bytes => OG t S p.1.o)
      (GlobalExecution.applyDistributionL env rs r d) := by
  unfold GlobalExecution.applyDistributionL
  olok

end global

/-! ## Recorder programs keep `OG` (`Post`, `Engine.lean`) -/

theorem Post.tru {α : Type} (x : M α) : Post x (fun _ => True) := fun _ _ _ _ _ => trivial

theorem Post.bind {α β : Type} {Q : α → Prop} {Q' : β → Prop} {x : M α} {f : α → M β}
    (hx : Post x Q) (hf : ∀ a, Q a → Post (f a) Q') : Post (x >>= f) Q' := by
  intro r e b r' h
  rw [M.bind_run] at h
  unfold bindRes at h
  split at h
  · rename_i a r1 heq
    exact hf a (hx r e a r1 heq) r1 e b r' h
  · cases h

theorem Post.throw {α : Type} {Q : α → Prop} (err : String) : Post (throw err : M α) Q := by
  intro r e a r' h; cases h

theorem Post.ite {α : Type} {Q : α → Prop} (c : Prop) [Decidable c] {a b : M α} (ha : c → Post a Q)
    (hb : ¬ c → Post b Q) : Post (if c then a else b) Q := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem Post.logged {α : Type} {Q : α → Prop} {x : LM α} (h : LOk Q x) :
    Post (StorageExecution.logged x) Q := by
  intro r env a r' hx
  rw [logged_run_rr] at hx
  rcases (SRelQ.of_SOk (h env.preRoot)).runR (hGet env.store) with ⟨e, ks, he, _⟩ | ⟨_, hq⟩
  · rw [he] at hx; cases hx
  · revert hx hq
    generalize SM.runR (hGet env.store) (x env.preRoot) = p
    obtain ⟨out, keys⟩ := p
    intro hx hq
    cases out with
    | error e => cases hx
    | ok v =>
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      exact hq _ rfl

theorem Post.tryCatch {α : Type} {Q : α → Prop} {x : M α} {h : String → M α} (hx : Post x Q)
    (hh : ∀ e, Post (h e) Q) : Post (MonadExcept.tryCatch x h) Q := by
  intro r e a r' hr
  have : (MonadExcept.tryCatch x h : M α) r e = Except.tryCatch (x r e) (fun err => h err r e) := rfl
  rw [this] at hr
  cases hxr : x r e with
  | ok p =>
    rw [hxr] at hr
    obtain ⟨a', r1⟩ := p
    simp only [Except.tryCatch, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hx r e _ _ hxr
  | error err =>
    rw [hxr] at hr
    exact hh err r e a r' hr

theorem Post.foldlM {α β : Type} {Q : α → Prop} (l : List β) (init : α) (hi : Q init) {f : α → β → M α}
    (h : ∀ a b, Q a → Post (f a b) Q) : Post (l.foldlM f init) Q := by
  induction l generalizing init with
  | nil => exact post_pure _ _ hi
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact Post.bind (h init x hi) fun a ha => ih a ha

theorem Post.forIn_list {β σ : Type} {Q : σ → Prop} (l : List β) (init : σ) (hi : Q init)
    {f : β → σ → M (ForInStep σ)} (h : ∀ b s, Q s → Post (f b s) (fun r => Q r.value)) :
    Post (forIn l init f) Q := by
  induction l generalizing init with
  | nil => exact post_pure _ _ hi
  | cons x t ih =>
    rw [List.forIn_cons]
    refine Post.bind (h x init hi) fun r hr => ?_
    cases r with
    | done b => exact post_pure _ _ hr
    | yield b => exact ih b hr

theorem Post.forIn_array {β σ : Type} {Q : σ → Prop} (l : Array β) (init : σ) (hi : Q init)
    {f : β → σ → M (ForInStep σ)} (h : ∀ b s, Q s → Post (f b s) (fun r => Q r.value)) :
    Post (forIn l init f) Q := by
  rw [← Array.forIn_toList]
  exact Post.forIn_list _ _ hi h

theorem Post.forIn_ovl {t : PTrie} {S : List Bytes} {β γ : Type} (l : Array β) (init : MProd Ovl γ)
    (hi : OG t S init.fst) {f : β → MProd Ovl γ → M (ForInStep (MProd Ovl γ))}
    (h : ∀ b s, OG t S s.fst → Post (f b s) (fun r => OG t S r.value.fst)) :
    Post (forIn l init f) (fun s => OG t S s.fst) :=
  Post.forIn_array (Q := fun s => OG t S s.fst) l init hi h

theorem Post.forIn_ovlP {t : PTrie} {S : List Bytes} {β γ : Type} (l : Array β) (init : Ovl × γ)
    (hi : OG t S init.1) {f : β → Ovl × γ → M (ForInStep (Ovl × γ))}
    (h : ∀ b s, OG t S s.1 → Post (f b s) (fun r => OG t S r.value.1)) :
    Post (forIn l init f) (fun s => OG t S s.1) :=
  Post.forIn_array (Q := fun s => OG t S s.1) l init hi h

/-- Close a recorder program by a proved fact (extended below). -/
syntax "m_close" : tactic
macro_rules | `(tactic| m_close) => `(tactic| fail "m_close")

open Lean Elab Tactic Meta in
/-- The head constant of the program of a `Post x Q` goal (`none` for a `let`/`have`, a variable, …). -/
def postHead : TacticM (Option Name) := do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let ty := ty.consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do return none
  let x := (ty.getArg! 1).consumeMData
  return x.getAppFn.constName?

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` headed by the constant `n`. -/
elab "post_head " n:ident : tactic => do
  let some h ← postHead | throwError "post_head: no head"
  unless h == n.getId.eraseMacroScopes do throwError "post_head: {h}"

/-- The recorder programs with a proved `OG` fact (`m_close`): `m_close` is tried only on these
heads, since unifying a lemma's program with an unrelated head can unfold it (e.g. the Wasm
interpreter behind `vmCall`). -/
def closeHeads : List Lean.Name :=
  [`NearSpecV3.Successor.StorageExecution.logged,
   `NearSpecV3.Successor.StorageExecution.applyAction,
   `NearSpecV3.Successor.StorageExecution.ordinaryAction,
   `NearSpecV3.Successor.StorageExecution.forwardOrBufferR,
   `NearSpecV3.Successor.StorageExecution.emitReceipts,
   `NearSpecV3.Successor.StorageExecution.actionLoop,
   `NearSpecV3.Successor.StorageExecution.applyActionReceipt,
   `NearSpecV3.Successor.StorageExecution.processReceipt,
   `NearSpecV3.Successor.StorageExecution.processWithInstant,
   `NearSpecV3.Successor.StorageExecution.processTxR,
   `NearSpecV3.Successor.StorageExecution.delayPopR,
   `NearSpecV3.Successor.StorageExecution.forwardFromBufferR,
   `NearSpecV3.Successor.StorageExecution.validatorUpdateR,
   `NearSpecV3.Successor.StorageExecution.schedOvlR]

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` headed by a program of `closeHeads`. -/
elab "post_callee" : tactic => do
  let some h ← postHead | throwError "post_callee: no head"
  unless closeHeads.contains h do throwError "post_callee: {h}"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post (x >>= f) Q` with `x` headed by a program of `closeHeads`. -/
elab "post_bind_callee" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "post_bind_callee"
  let x := (ty.getArg! 1).consumeMData
  unless x.isAppOfArity ``Bind.bind 6 do throwError "post_bind_callee: no bind"
  let some h := (x.getArg! 4).consumeMData.getAppFn.constName? | throwError "post_bind_callee"
  unless closeHeads.contains h do throwError "post_bind_callee: {h}"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is `Post x Q` with `x` a `match` application. -/
elab "post_match" : tactic => do
  let some h ← postHead | throwError "post_match: no head"
  unless (← isMatcher h) do throwError "post_match: {h}"

/-- A join point `have jp := v; b jp` of a `do` block, by a specification `Spec` of `jp`: walked
once for `v` and used at every call of `jp` in `b` (zeta-reducing it would copy `v` into every
branch that calls it). -/
theorem Post.have_jp {α F : Type} {Q : α → Prop} (v : F) (b : F → M α) (Spec : F → Prop)
    (hv : Spec v) (hb : ∀ jp, Spec jp → Post (b jp) Q) : Post (b v) Q := hb v hv

open Lean Elab Tactic Meta in
/-- The `OG t S` facts about a join point argument `x` (an overlay, a receipt or action state,
or a pair whose first component is one), for the local `t`, `S`. -/
partial def ogFacts (t S x : Expr) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType x))
  if ty.isConstOf ``NearSpecV3.D2.Ovl then
    return #[← mkAppM ``OG #[t, S, x]]
  if ty.isConstOf ``NearSpecV3.D2.RS then
    return #[← mkAppM ``OG #[t, S, ← mkAppM ``NearSpecV3.D2.RS.o #[x]]]
  if ty.isConstOf ``NearSpecV3.D2.ActSt then
    return #[← mkAppM ``OG #[t, S, ← mkAppM ``NearSpecV3.D2.ActSt.o #[x]]]
  if ty.isAppOfArity ``Prod 2 then
    return ← ogFacts t S (← mkAppM ``Prod.fst #[x])
  if ty.isAppOfArity ``MProd 2 then
    return ← ogFacts t S (← mkAppM ``MProd.fst #[x])
  return #[]

open Lean Elab Tactic Meta in
/-- On `Post (let x := v; b) Q`: a value `x` is substituted; a join point (a function into the
monad) is replaced by its specification (`Post.have_jp`): every call with arguments satisfying
their `OG t S` facts satisfies `Q`. Two goals: the specification of `v`, and `b` under it. -/
elab "post_let" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "post_let"
  let α := ty.getArg! 0
  let Q := ty.getArg! 2
  let .letE n T v b _ := (ty.getArg! 1).consumeMData | throwError "post_let: no let"
  let isJp ← forallTelescope T fun xs r => do
    if xs.isEmpty then return false
    let r := r.consumeMData
    return r.isAppOf ``NearSpecV3.Successor.StorageExecution.M || r.isAppOf ``StateT
  if !isJp then
    let g' ← g.replaceTargetDefEq (mkApp3 ty.getAppFn α (b.instantiate1 v) Q)
    replaceMainGoal [g']
    return
  let lctx ← getLCtx
  let some tD := lctx.findFromUserName? `t | throwError "post_let: no t"
  let some SD := lctx.findFromUserName? `S | throwError "post_let: no S"
  let specOf (jp : Expr) : MetaM Expr := forallTelescope T fun xs _ => do
    let mut facts : Array Expr := #[]
    for x in xs do
      facts := facts ++ (← ogFacts tD.toExpr SD.toExpr x)
    let post ← mkAppM ``NearSpecV3.E2E.Post #[mkAppN jp xs, Q]
    let inner ← facts.foldrM (fun f acc => mkArrow f acc) post
    mkForallFVars xs inner
  let spec ← withLocalDeclD n T fun jp => do mkLambdaFVars #[jp] (← specOf jp)
  let hv ← mkFreshExprSyntheticOpaqueMVar (← specOf v)
  let hbTy ← withLocalDeclD n T fun jp => do
    mkForallFVars #[jp] (← mkArrow (← specOf jp)
      (← mkAppM ``NearSpecV3.E2E.Post #[b.instantiate1 jp, Q]))
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy
  let bl := Expr.lam n T b .default
  g.assign (← mkAppOptM ``Post.have_jp #[α, T, Q, v, bl, spec, hv, hb])
  replaceMainGoal [hv.mvarId!, hb.mvarId!]

open Lean Elab Tactic Meta in
/-- On `Post (jp a…) Q` with `jp` a local join point: apply its specification (left as fact
goals). -/
elab "post_jpcall" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``NearSpecV3.E2E.Post 3 do throwError "post_jpcall"
  let f := (ty.getArg! 1).consumeMData.getAppFn
  unless f.isFVar do throwError "post_jpcall: not a local"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ok ← forallTelescope d.type fun _ c => do
      let c := c.consumeMData
      return c.isAppOfArity ``NearSpecV3.E2E.Post 3 && (c.getArg! 1).getAppFn == f
    if ok then
      let gs ← g.apply d.toExpr
      replaceMainGoal gs
      return
  throwError "post_jpcall: no specification"

open Lean Elab Tactic Meta in
/-- Succeed iff the goal is syntactically a `∀` (not a `Post` that unfolds to one). -/
elab "guard_forall" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isForall do throwError "guard_forall"

/-! The walk is a set of small `macro_rules` (one alternative each, tried latest first): large
nested tactic quotations are slow to compile. -/

/-- `mwalk` on a `pure` leaf. -/
syntax "mwalk_pure" : tactic
macro_rules | `(tactic| mwalk_pure) => `(tactic| (refine post_pure _ _ ?_; exact True.intro))
macro_rules | `(tactic| mwalk_pure) => `(tactic| (refine post_pure _ _ ?_; focus ((show OG _ _ _); og_leaf; done)))
macro_rules | `(tactic| mwalk_pure) => `(tactic| (refine post_pure _ _ ?_; focus (og_leaf; done)))

/-- `mwalk` on a bind (`>>=`). -/
syntax "mwalk_bind" : tactic
/-- Any other head: no fact on its value. -/
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Post.tru _) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : ActSt × AR => OG t S x.1.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : RS × _ => OG t S x.1.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : RS => OG t S x.o) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : Ovl => OG t S x) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Q := fun x : Ovl × _ => OG t S x.1) ?_ fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Post.foldlM (Q := fun x : Ovl × _ => OG t S x.1) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Post.forIn_ovlP (t := t) (S := S) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
set_option hygiene false in
macro_rules | `(tactic| mwalk_bind) => `(tactic| ((refine Post.bind (Post.forIn_ovl (t := t) (S := S) _ _ ?_ fun _ _ _ => ?_) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
/-- A proved head (`m_close`). -/
macro_rules | `(tactic| mwalk_bind) => `(tactic| (post_bind_callee; (refine Post.bind (by m_close) fun _ _ => ?_); try (dsimp (config := { zeta := false }) only)))
/-- A `pure` head. -/
macro_rules | `(tactic| mwalk_bind) => `(tactic| simp (config := { zeta := false }) only [pure_bind])

/-- One step of the walk over a recorder program, dispatching on the program's head. -/
syntax "mwalk1" : tactic
macro_rules | `(tactic| mwalk1) => `(tactic| dsimp (config := { zeta := false }) only)
macro_rules | `(tactic| mwalk1) => `(tactic| post_jpcall)
macro_rules | `(tactic| mwalk1) => `(tactic| (guard_forall; intro))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_callee; m_close))
macro_rules | `(tactic| mwalk1) => `(tactic| ((show OG _ _ _); og_leaf; done))
macro_rules | `(tactic| mwalk1) => `(tactic| post_let)
macro_rules | `(tactic| mwalk1) => `(tactic| (post_match; split <;> (try (dsimp (config := { zeta := false }) only))))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_head Bind.bind; mwalk_bind))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_head MonadExcept.tryCatch; refine Post.tryCatch ?_ fun _ => ?_))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_head ite; refine Post.ite _ (fun _ => ?_) (fun _ => ?_)))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_head MonadExcept.throw; exact Post.throw _))
macro_rules | `(tactic| mwalk1) => `(tactic| (post_head Pure.pure; mwalk_pure))

/-- **The walk over a recorder program** (the overlay predicate's parameters are the local `t`,
`S`). -/
macro "mwalk" : tactic => `(tactic| repeat' mwalk1)

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.logged; exact Post.logged (by ogl_close)))
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.validatorUpdateR; exact Post.logged (by ogl_close)))
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.schedOvlR; exact Post.logged (by ogl_close)))
macro_rules | `(tactic| ogl_close) => `(tactic| exact applyGlobalActionL_og _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact applyDistributionL_og _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact processTxD2L_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact delayPushL_og _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact delayPopL_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact delayPopLWith_og _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact forwardFromBufferL_og _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact forwardFromBufferLWith_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact forwardFromBufferV3L_og _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact validatorUpdateL_og _ _ _ _ _ _ _ (by assumption))
macro_rules | `(tactic| ogl_close) => `(tactic| exact schedOvlL_og _ _ _ _ _ (by assumption))

section rec
variable (t : PTrie) (S : List Bytes)

theorem ordinaryAction_og (c : ActCtx) (st : ActSt) (a : Act) (h : OG t S st.o) :
    Post (ordinaryAction c st a) (fun p : ActSt × AR => OG t S p.1.o) := by
  unfold ordinaryAction
  refine Post.bind (Post.logged (applyActionL_og t S c st a h)) fun p hp => ?_
  mwalk

theorem applyGlobal_og (ga : Bool) (c : ActCtx) (st : ActSt) (a : Act) (b : Base) (h : OG t S st.o) :
    Post (applyGlobal ga c st a b) (fun p : ActSt × AR => OG t S p.1.o) := by
  unfold applyGlobal
  mwalk

end rec

section rec5
variable (t : PTrie) (S : List Bytes)

theorem functionCallRecordedF_og (fl : Flags) (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (h : OG t S st.o) :
    Post (functionCallRecordedF fl fuelOf cfg c st ar b) (fun p : ActSt × AR => OG t S p.1.o) := by
  unfold functionCallRecordedF
  mwalk

theorem applyAction_og (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act)
    (h : OG t S st.o) :
    Post (StorageExecution.applyAction fl cfg c st a) (fun p : ActSt × AR => OG t S p.1.o) := by
  unfold StorageExecution.applyAction
  split
  · mwalk
    all_goals exact functionCallRecordedF_og t S _ _ _ _ _ _ _ h
  · exact applyGlobal_og t S _ _ _ _ _ h
  · exact applyGlobal_og t S _ _ _ _ _ h
  · exact applyGlobal_og t S _ _ _ _ _ h
  · exact ordinaryAction_og t S _ _ _ h

end rec5

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.applyAction; exact applyAction_og _ _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.ordinaryAction; exact ordinaryAction_og _ _ _ _ _ (by assumption)))

section rec6
variable (t : PTrie) (S : List Bytes)

theorem actionLoop_og (fl : Flags) (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR), OG t S acc.1.o →
      Post (StorageExecution.actionLoop fl hooks env r a inputs deployed attempted i acts acc)
        (fun p : ActSt × AR => OG t S p.1.o)
  | _, [], acc, h => by unfold StorageExecution.actionLoop; exact post_pure _ _ h
  | i, act :: rest, (st, res), h => by
    unfold StorageExecution.actionLoop
    dsimp only at h
    mwalk
    all_goals exact actionLoop_og fl hooks env r a inputs deployed attempted _ rest _ (by og_leaf)

theorem forwardOrBufferR_og (ga : Bool) (env : Env) (rs : RS) (r : Rcpt) (h : OG t S rs.o) :
    Post (forwardOrBufferR ga env rs r) (fun x : RS => OG t S x.o) := by
  unfold forwardOrBufferR; mwalk

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.forwardOrBufferR; exact forwardOrBufferR_og _ _ _ _ _ _ (by assumption)))


theorem emitReceipts_og (ga : Bool) (env : Env) (parent : Bytes) :
    ∀ (rs : RS) (k : Nat) (l : List Rcpt), OG t S rs.o →
      Post (StorageExecution.emitReceipts ga env parent rs k l) (fun x : RS × List Bytes => OG t S x.1.o)
  | rs, _, [], h => by unfold StorageExecution.emitReceipts; exact post_pure _ _ h
  | rs, k, nr :: rest, h => by
    unfold StorageExecution.emitReceipts
    dsimp only
    refine Post.ite _ (fun _ => ?_) (fun _ => ?_)
    · simp only [pure_bind]
      exact Post.bind (emitReceipts_og ga env parent _ (k + 1) rest h) fun p hp => post_pure _ _ hp
    · exact Post.bind (forwardOrBufferR_og t S _ _ _ _ h) fun rs' h' =>
        Post.bind (emitReceipts_og ga env parent rs' (k + 1) rest h') fun p hp => post_pure _ _ hp

end rec6

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.emitReceipts; exact emitReceipts_og _ _ _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.actionLoop; exact actionLoop_og _ _ _ _ _ _ _ _ _ _ _ _ _ (by first | assumption | og_leaf)))

section rec7
variable (t : PTrie) (S : List Bytes)

theorem applyActionReceipt_og (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (a : ActionR) (h : OG t S rs.o) :
    Post (StorageExecution.applyActionReceipt fl hooks env rs r a)
      (fun x : RS × OutD1 × Nat => OG t S x.1.o) := by
  unfold StorageExecution.applyActionReceipt
  mwalk


end rec7
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.applyActionReceipt; exact applyActionReceipt_og _ _ _ _ _ _ _ _ (by first | assumption | og_leaf)))

section rec8
variable (t : PTrie) (S : List Bytes)

theorem processReceipt_og (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OG t S rs.o) :
    Post (StorageExecution.processReceipt fl hooks env rs r)
      (fun x : RS × Option (OutD1 × Nat) => OG t S x.1.o) := by
  unfold StorageExecution.processReceipt
  mwalk

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.processReceipt; exact processReceipt_og _ _ _ _ _ _ _ (by assumption)))

theorem processWithTotals_og (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OG t S rs.o) :
    Post (StorageExecution.processWithTotals fl hooks env rs r) (fun x : RS => OG t S x.o) := by
  unfold StorageExecution.processWithTotals
  mwalk

theorem drain_og (fl : Flags) (hooks : NearCfg) (env : Env) : ∀ (fuel : Nat) (rs : RS), OG t S rs.o →
    Post (StorageExecution.processWithInstant.drain fl hooks env fuel rs) (fun x : RS => OG t S x.o)
  | 0, _, _ => by unfold StorageExecution.processWithInstant.drain; exact Post.throw _
  | f + 1, rs, h => by
    unfold StorageExecution.processWithInstant.drain
    split
    · exact post_pure _ _ h
    · exact Post.bind (processWithTotals_og t S fl hooks env _ _ ⟨h.1, h.2, h.3⟩) fun rs' h' =>
        drain_og fl hooks env f rs' h'

theorem processWithInstant_og (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt)
    (h : OG t S rs.o) :
    Post (StorageExecution.processWithInstant fl hooks env rs r) (fun x : RS => OG t S x.o) := by
  unfold StorageExecution.processWithInstant
  exact Post.bind (processWithTotals_og t S fl hooks env rs r h) fun rs' h' =>
    drain_og t S fl hooks env _ rs' h'

end rec8

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.processWithInstant; exact processWithInstant_og _ _ _ _ _ _ _ (by first | assumption | og_leaf)))

section eng
variable (t : PTrie) (S : List Bytes)

theorem processTxR_og (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : OG t S rs.1.o) :
    Post (processTxR env rs tf) (fun x : RS × List Bytes => OG t S x.1.o) := by
  unfold processTxR
  refine Post.bind (Post.logged (processTxD2L_og t S env rs tf h)) fun p hp => ?_
  mwalk

end eng

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.processTxR; exact processTxR_og _ _ _ _ _ (by assumption)))
/-! ## The final committed list keeps every committed key -/

theorem mem_insertSorted (p : Bytes × Option Bytes) :
    ∀ (l : List (Bytes × Option Bytes)) (x : Bytes), x ∈ keys l → x ∈ keys (insertSorted p l)
  | [], _, h => by cases h
  | q :: qs, x, h => by
    unfold insertSorted
    split
    · exact List.mem_cons_of_mem _ h
    · simp only [List.map_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_insertSorted p qs x h)

theorem mem_insertSorted_self (p : Bytes × Option Bytes) :
    ∀ (l : List (Bytes × Option Bytes)), p.1 ∈ keys (insertSorted p l)
  | [] => by simp [insertSorted]
  | q :: qs => by
    unfold insertSorted
    split
    · simp
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inr (mem_insertSorted_self p qs)

theorem mem_foldl_insertSorted : ∀ (l acc : List (Bytes × Option Bytes)) (x : Bytes),
    (x ∈ keys acc ∨ x ∈ keys l) → x ∈ keys (l.foldl (fun acc p => insertSorted p acc) acc)
  | [], _, _, h => by
    rcases h with h | h
    · exact h
    · cases h
  | p :: l, acc, x, h => by
    simp only [List.foldl_cons]
    apply mem_foldl_insertSorted l _ x
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inl (mem_insertSorted p acc x h)
    · subst h; exact Or.inl (mem_insertSorted_self p acc)
    · exact Or.inr h

theorem mem_sortKV (l : List (Bytes × Option Bytes)) (x : Bytes) (h : x ∈ keys l) :
    x ∈ keys (sortKV l) :=
  mem_foldl_insertSorted l [] x (Or.inr h)

/-! ## One machine step -/

/-- The overlay of a position (lane B's `posOvl`). -/
def ovlOfPos : EPos → Option Ovl
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => some rs.o
  | _ => none

/-- **What a step reaches**: an overlay satisfying `OG t S`, or a final output whose committed
list includes `S`. -/
def PQ (t : PTrie) (S : List Bytes) : EPos → Prop
  | .start => False
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => OG t S rs.o
  | .done out => ∀ k ∈ S, k ∈ keys (out.committed.getD [])

section steps
variable (t : PTrie) (S : List Bytes)

theorem raceCheck_post (out : MainOutD2) (Q : MainOutD2 → Prop) (h : Q out) :
    Post (raceCheck out) Q := by
  unfold raceCheck
  exact Post.bind (Post.tru _) fun _ _ => Post.ite _ (fun _ => Post.throw _) fun _ => post_pure _ _ h


theorem finalizeStep_og (env : Env) (yf yn : Nat) (rs : RS) (i : Nat) (h : OG t S rs.o) :
    Post (finalizeStep env yf yn (rs, i))
      (fun out : MainOutD2 => ∀ k ∈ S, k ∈ keys (out.committed.getD [])) := by
  delta finalizeStep
  dsimp only
  mwalk
  all_goals
    refine post_pure _ _ ?_
    intro k hk
    exact mem_sortKV _ k ((OG.commit (by
      first
        | exact h
        | exact OG.set h _ _
        | (split <;> first | exact h | exact OG.set h _ _))).incl k hk)

end steps

section steps2
variable (t : PTrie) (S : List Bytes)

theorem delayPopR_og (ga : Bool) (env : Env) (fuel : Nat) (rs : RS) (h : OG t S rs.o) :
    Post (delayPopR ga env fuel rs) (fun x : RS × Option Rcpt => OG t S x.1.o) := by
  unfold delayPopR; mwalk

theorem forwardFromBufferR_og (ga : Bool) (env : Env) (rs : RS) (h : OG t S rs.o) :
    Post (forwardFromBufferR ga env rs) (fun x : RS => OG t S x.o) := by
  unfold forwardFromBufferR; mwalk

end steps2

macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.delayPopR; exact delayPopR_og _ _ _ _ _ _ (by assumption)))
macro_rules | `(tactic| m_close) => `(tactic| (post_head NearSpecV3.Successor.StorageExecution.forwardFromBufferR; exact forwardFromBufferR_og _ _ _ _ _ (by assumption)))

section steps2b
variable (t : PTrie) (S : List Bytes)

theorem localsBody_og (fl : Flags) (hooks : NearCfg) (env : Env) (dec : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) (h : OG t S rs.o) :
    Post (localsBody fl hooks env dec rs r) (fun x : RS => OG t S x.o) := by
  unfold localsBody
  refine Post.bind (Post.tru _) fun _ _ => ?_
  refine Post.ite _ (fun _ => Post.logged (delayPushL_og t S rs r h)) fun _ => ?_
  exact Post.bind (Post.tru _) fun _ _ => processWithInstant_og t S _ _ _ _ _ h

theorem incomingBody_og (fl : Flags) (hooks : NearCfg) (env : Env) (dec : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) (h : OG t S rs.o) :
    Post (incomingBody fl hooks env dec rs r) (fun x : RS => OG t S x.o) := by
  unfold incomingBody
  refine Post.ite _ (fun _ => Post.throw _) fun _ => ?_
  refine Post.bind (Post.tru _) fun _ _ => ?_
  refine Post.ite _ (fun _ => Post.logged (delayPushL_og t S rs r h)) fun _ => ?_
  exact Post.bind (Post.tru _) fun _ _ => processWithInstant_og t S _ _ _ _ _ h

end steps2b
section machine0
variable (t : PTrie) (S : List Bytes)

theorem delayedK_og (fl : Flags) (hooks : NearCfg) (env : Env) (f : Nat) (rs : RS) (h : OG t S rs.o) :
    Post (delayedK fl hooks env (fun rs => pure (EPos.delayed 0 rs)) (fun rs => pure (EPos.delayed f rs)) rs)
      (PQ t S) := by
  unfold delayedK; mwalk

theorem yieldK_og (ga : Bool) (env : Env) (yf yn f : Nat) (rs : RS) (i k : Nat) (h : OG t S rs.o) :
    Post (yieldK ga env yn (fun p => pure (EPos.yields yf yn 0 p.2 0 p.1))
      (fun p => pure (EPos.yields yf yn f p.2.1 p.2.2 p.1)) rs i k) (PQ t S) := by
  unfold yieldK; mwalk

end machine0

section machine
variable (S : List Bytes)

/-- **One step keeps `PQ`** from every position other than `start`. -/
theorem stepM_pq (P : Prog) (p : EPos) (hp : PQ P.t S p) : Post (stepM P p) (PQ P.t S) := by
  cases p with
  | start => exact hp.elim
  | txs rest acc rs =>
    cases rest with
    | nil =>
      exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ ⟨hp.1, hp.2, hp.3⟩
    | cons x rest =>
      exact Post.bind (processTxR_og P.t S _ _ _ hp) fun q hq => post_pure _ _ hq
  | locals rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (localsBody_og P.t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | delayed fuel rs =>
    cases fuel with
    | zero => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | succ f =>
      exact delayedK_og P.t S _ _ _ f rs hp
  | incoming rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (incomingBody_og P.t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | yields yf yn fuel i k rs =>
    cases fuel with
    | zero =>
      exact Post.bind (Post.bind (finalizeStep_og P.t S _ _ _ _ _ hp) fun out hout =>
        raceCheck_post out _ hout) fun out hout => post_pure _ _ hout
    | succ f =>
      exact yieldK_og P.t S _ _ yf yn f rs i k hp
  | done out => exact post_pure _ _ hp

end machine
/-- The first step (`preludeK`): the overlay starts as `Ovl.ofTrie P.t`. -/
theorem preludeK_pq (t : PTrie) (fl : Flags) (prims : Prims) (env : Env)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (cong : Congestion)
    (txs : List (TxD2 × Bool)) :
    Post (preludeK fl prims env t vu props cong fun rs => pure (EPos.txs txs [] rs)) (PQ t []) := by
  let S : List Bytes := []
  show Post _ (PQ t S)
  have h0 : OG t S (Ovl.ofTrie t) := OG.ofTrie t
  unfold preludeK
  mwalk

theorem start_pq (P : Prog) : Post (stepM P .start) (PQ P.t []) :=
  preludeK_pq P.t P.fl P.prims P.env P.vu P.props P.cong P.txs

theorem PQ.of_ovl {t : PTrie} {S : List Bytes} {p : EPos} {o : Ovl} (ho : ovlOfPos p = some o)
    (h : OG t S o) : PQ t S p := by
  cases p <;> simp only [ovlOfPos, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;> exact h

theorem PQ.og {t : PTrie} {S : List Bytes} {p : EPos} {o : Ovl} (ho : ovlOfPos p = some o)
    (h : PQ t S p) : OG t S o := by
  cases p <;> simp only [ovlOfPos, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;> exact h

theorem estep_post {P : Prog} {c c' : EConf} {Q : EPos → Prop} (hq : Post (stepM P c.pos) Q)
    (h : estep P c = .ok c') : Q c'.pos := by
  unfold estep at h
  split at h
  · rename_i p r heq
    cases h
    exact hq _ _ _ _ heq
  · cases h

/-- **Along any run, `PQ` is kept** (from a position other than `start`). -/
theorem esteps_pq (P : Prog) (S : List Bytes) {a b : EConf} (h : ESteps P a b)
    (ha : PQ P.t S a.pos) : PQ P.t S b.pos := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (estep_post (stepM_pq S P _ ha) hs)

/-- **Every configuration reached from `start`** is `start` or satisfies `PQ P.t []`. -/
theorem reach_pq (P : Prog) {a b : EConf} (h : ESteps P a b)
    (ha : a.pos = .start ∨ PQ P.t [] a.pos) : b.pos = .start ∨ PQ P.t [] b.pos := by
  induction h with
  | refl => exact ha
  | @step a b c hs _ ih =>
    apply ih
    right
    rcases ha with ha | ha
    · obtain ⟨pos, r⟩ := a
      simp only at ha
      subst ha
      exact estep_post (start_pq P) hs
    · exact estep_post (stepM_pq [] P _ ha) hs

/-- **The trie and distinctness invariant**: every overlay reached from `start` has the program's
trie `P.t` and distinct committed keys. -/
theorem reach_trie_nodup (P : Prog) (r0 : Recording) {c : EConf} {o : Ovl}
    (h : ESteps P ⟨.start, r0⟩ c) (ho : ovlOfPos c.pos = some o) :
    o.trie = P.t ∧ (keys o.committed).Nodup := by
  rcases reach_pq P h (Or.inl rfl) with hs | hp
  · rw [hs] at ho; cases ho
  · have := PQ.og ho hp
    exact ⟨this.1, this.2⟩

/-- **Committed keys survive to the output**: on a run from `start` that reaches `done out`,
every committed key of every overlay on the way is in `out.committed`. -/
theorem reach_covered (P : Prog) (r0 : Recording) {c : EConf} {o : Ovl} {out : MainOutD2}
    {r : Recording} (h1 : ESteps P ⟨.start, r0⟩ c) (ho : ovlOfPos c.pos = some o)
    (h2 : ESteps P c ⟨.done out, r⟩) :
    ∀ k ∈ keys o.committed, k ∈ keys (out.committed.getD []) := by
  obtain ⟨ht, hn⟩ := reach_trie_nodup P r0 h1 ho
  have := esteps_pq P (keys o.committed) h2 (PQ.of_ovl ho (OG.self ht hn))
  exact this

/-! ## The machine is deterministic: an accepting run has one output -/

theorem estep_done (P : Prog) (out : MainOutD2) (r : Recording) :
    estep P ⟨.done out, r⟩ = .ok ⟨.done out, r⟩ := rfl

theorem esteps_from_done (P : Prog) {out : MainOutD2} {r : Recording} {c : EConf}
    (h : ESteps P ⟨.done out, r⟩ c) : c = ⟨.done out, r⟩ := by
  generalize ha : (⟨.done out, r⟩ : EConf) = a at h
  induction h with
  | refl => first | rfl | exact ha.symm
  | step hs _ ih =>
    subst ha
    rw [estep_done] at hs
    cases hs
    exact ih rfl

theorem esteps_total (P : Prog) {a b c : EConf} (hb : ESteps P a b) (hc : ESteps P a c) :
    ESteps P b c ∨ ESteps P c b := by
  induction hb generalizing c with
  | refl => exact Or.inl hc
  | @step a a' b hs _ ih =>
    cases hc with
    | refl => exact Or.inr (.step hs ‹_›)
    | step hs' hc' =>
      rw [hs] at hs'
      cases hs'
      exact ih hc'

/-- **One output per accepting run.** -/
theorem done_unique (P : Prog) {a : EConf} {o1 o2 : MainOutD2} {r1 r2 : Recording}
    (h1 : ESteps P a ⟨.done o1, r1⟩) (h2 : ESteps P a ⟨.done o2, r2⟩) : o1 = o2 := by
  rcases esteps_total P h1 h2 with h | h
  · have := esteps_from_done P h; cases this; rfl
  · have := esteps_from_done P h; cases this; rfl

#print axioms applyActionReceipt_og
#print axioms functionCallRecordedF_og
#print axioms stepM_pq
#print axioms start_pq
#print axioms reach_trie_nodup
#print axioms reach_covered
#print axioms done_unique

end NearSpecV3.E2E.OvlInv
