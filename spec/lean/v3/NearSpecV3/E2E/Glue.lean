import NearSpecV3.E2E.TreeM8C
import NearSpecV3.E2E.OvlInv

set_option linter.unusedVariables false

/-!
# E2E-M12, item 2: the glue of the split leaves (STATE = F ∧ B; INIT / FINAL = G ∧ B's IF)

`TreeM8.split_sound` (and lane F's relative, canonical `M5T1.SplitC.split_sound_relC`) compose a
split leaf from an engine half (lane F / lane G), a state half (lane B) and a **glue** lemma
`SplitGlue M : ∀ x x', Meaning k x x' → M.wOut x' = M.apply (M.qOf x x') (M.wIn x)`. Lane F
split the glue into its side `ReqsFaithful` (along a meaning instance the output overlay is the
input overlay updated by the meaning's requests) and lane B's side `ApplyFaithful` (lane B's state
function computes the root of the updated overlay); `glue_of` composes them. This file proves the
engine-semantics side for the three split leaves, at the level both lanes' statements meet: the
**overlay's partial trie and its committed lookups** (lane B's working-set entries are
`(k, pre(trie, k), cur, written)` with `cur`/`written` from `kvFind k o.committed`,
`StateViewParams.entryAt`, so they depend on the overlay only through these two).

## 1. The overlay invariant for any trie (`stepM_pqT`, `esteps_pqT`)

`OvlInv.stepM_pq` keeps `OG P.t S` (trie `P.t`, distinct committed keys, committed keys ⊇ `S`)
along a step; its proof never uses that the trie is `P.t` (only `start` creates an overlay).
`stepM_pqT` is the same proof for any trie `t`: so along **every** run of engine steps from a
configuration whose overlay has distinct committed keys, the trie is unchanged and committed
keys only grow — also for configurations not reached from `start` (canonical openings of a leaf's
input digest need not be).

## 2. STATE (lane F's `ReqsFaithful`, proved with two preconditions)

* `ovE x`: the overlay a configuration carries — `rs.o` at positions with a receipt state; at
  `start` the overlay the first step creates, `Ovl.ofTrie I.prog.t` (`= Ovl.ofTrie I.tMain`).
* `netQ o o'`: the **net requests** of the step(s): the committed entries of `o'` that differ from
  `o`'s (key, new value). `updK q f`: the lookup `f` updated by `q` (last write per key).
* **`state_reqs`**: for `MState x x'` (VM-free engine steps) with `OvOK x` (the input overlay's
  committed keys are distinct — lane B's `fits` checks `ovlInv`, so every circuit-form `stRoot`
  satisfies it) and `x'` not at `done`: `ovE x = some o`, `ovE x' = some o'`, `o'.trie = o.trie`,
  and `kv o' = updK (netQ o o') (kv o)` — lane F's `ReqsFaithful` (`OvlSem.ovOut x' = upd (qOf x
  x') (ovIn x)`) for `Ov := PTrie × (Bytes → Option (Option Bytes))`.
* **`state_glue`**: `SplitGlueOn` (the glue restricted by the preconditions) for the STATE split
  semantics `stateSem root apply` (state value = `root I trie lookups`, lane B's working-set root
  over the chunk's keys) from lane B's `ApplyFaithfulS` (`apply q (root I t f) = root I t (updK q
  f)`: `m5tSeg` applies the net requests; `e2e-general/join/GlueB.lean` shows lane B's working set
  has this shape: `entryAt o k = entryOf o.trie (kv o) k`, `wsRoot_entryAt`, `rootB`);
  `split_sound_relC_on` is `split_sound_relC` with the
  preconditions passed through the engine half (`EngHalfRCOn`), and **`state_sound_relC`** is
  `TmplSoundRel8C sf V A Bad .state` from `EngHalfRCOn` (lane F), `StHalf` (lane B) and
  `ApplyFaithfulS` (lane B).

Why two preconditions. Lane F's `ReqsFaithful` quantifies over all meaning instances. (a)
Without distinct committed keys `OvlInv`'s walk does not apply (and `kvPut` on a list with repeated
keys is not a map update), so the statement is not provable for arbitrary inputs; the engine half
obtains `OvOK` from the state commitment's `fits` form. (b) A STATE run that ends at `eng I ⟨done
out⟩` has no overlay (`finalizeStep` commits it and hashes the trie); lane B's working set at `done`
is `[]` (`wsOfB`), so the glue there is the FINAL glue (§4). **Finding (M12):** the STATE segment
that contains the finalize step `yields _ _ 0 _ _ rs → done out` cannot use the working-set glue; it
must end at the last `yields` position, and the finalize step must be in a leaf whose state half
proves the post-state root (lane B's IF-FINAL, the FINAL leaf). Since `MFinal` starts at
`eng I ⟨done out⟩`, this needs either a STATE leaf for the finalize step alone with lane B's
IF-FINAL as its state half, or `FinStart` extended to `yields _ _ 0 _ _ _` (a `Templates.lean`
change; no change to `S`, `claimDigest` or the checker). Recorded, not changed.

## 3. INIT (lane G ∧ lane B's IF-INTAKE)

**`init_glue`**: INIT's output `eng I ⟨start, _⟩` carries `ovE = Ovl.ofTrie I.tMain`, whose every
committed lookup is `none`: the working-set entries are `(k, pre, pre, false)` — exactly what
lane B's IF-INTAKE computes `R_0` from (the authenticated partial trie `I.tMain`,
`I.tMain.hashOf = slotB2.prevStateRoot` by the intake's check, which lane G's `PSR` value reads).
So `wOut (eng I start) = root I I.tMain (fun _ => none)` = IF-INTAKE's `R_0`.

**Finding (M12, boundary gap) — fixed by D-a.** In M12 `R_0` was not in INIT's output boundary
(the state component at `start` had no overlay, so lane B's `wsOfB` was `[]`). Integrator decision
D-a adopted option (a): `View.split` now carries the intake's overlay at `start`
(`EngSt.ovl0 = some (Ovl.ofTrie I.tMain)`, `Bnd.stOfI`; `none` elsewhere), lane B's `ovlOf` reads it
there (`StateViewParams.ovlOf`), so `stD` at `start` commits the working set of IF-INTAKE
(`StViewEJoin.wsOf_start`: entries `(k, pre, pre, false)`, trie `I.tMain`). **`init_glue_view`**:
the state component of `eng I ⟨start, r⟩` carries exactly `ovE` — the overlay the STATE glue
starts from — so the first STATE leaf takes `wIn` from its input digest.

## 4. FINAL (lane G ∧ lane B's IF-FINAL)

`finalizeStep` computes the post-state root as `finalizeR` (the logged, lazy-trie
`Ovl.finalizeL`) of the committed overlay; lane B's `m5b_final` concludes `applyChanges (some T)
(sortKV n) = some (some T') ∧ rootHash (some T') = post` for its committed change list `n`.
**`final_glue`**: if the overlay's trie is `T` (not the empty hash), its sorted committed list is
`sortKV n`, and `m5b_final`'s conclusion holds, then `Ovl.finalize o = .ok post` (the D2,
non-lazy finalize). Open (named, `FinalizeAgree`): the logged lazy `finalizeR o` returns
`Ovl.finalize o` (the lazy-trie / partial-trie agreement for the finalize fold; not in the spec
library today).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.Glue
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution NearSpecV3.E2E.OvlInv

/-! ## 1. The overlay invariant for any trie -/

section machine
variable (t : PTrie) (S : List Bytes)

/-- `OvlInv.stepM_pq` for any trie `t` (same proof). -/
theorem stepM_pqT (P : Prog) (p : EPos) (hp : PQ t S p) : Post (stepM P p) (PQ t S) := by
  cases p with
  | start => exact hp.elim
  | txs rest acc rs =>
    cases rest with
    | nil =>
      exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ ⟨hp.1, hp.2, hp.3⟩
    | cons x rest =>
      exact Post.bind (processTxR_og t S _ _ _ hp) fun q hq => post_pure _ _ hq
  | locals rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (localsBody_og t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | delayed fuel rs =>
    cases fuel with
    | zero => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | succ f =>
      exact delayedK_og t S _ _ _ f rs hp
  | incoming rest rs =>
    cases rest with
    | nil => exact Post.bind (Post.tru _) fun _ _ => post_pure _ _ hp
    | cons r rest =>
      exact Post.bind (incomingBody_og t S _ _ _ _ _ _ hp) fun q hq => post_pure _ _ hq
  | yields yf yn fuel i k rs =>
    cases fuel with
    | zero =>
      exact Post.bind (Post.bind (finalizeStep_og t S _ _ _ _ _ hp) fun out hout =>
        raceCheck_post out _ hout) fun out hout => post_pure _ _ hout
    | succ f =>
      exact yieldK_og t S _ _ yf yn f rs i k hp
  | done out => exact post_pure _ _ hp

/-- **Along any run, `PQ t S` is kept**, for any trie `t`. -/
theorem esteps_pqT (P : Prog) {a b : EConf} (h : ESteps P a b) (ha : PQ t S a.pos) :
    PQ t S b.pos := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (estep_post (stepM_pqT t S P _ ha) hs)

end machine

/-! ## 2. Committed lookups and net requests -/

/-- A key → value list (the overlay's committed changes; a request list). -/
abbrev KV := List (Bytes × Option Bytes)

/-- The committed lookup of an overlay. -/
def kv (o : Ovl) (k : Bytes) : Option (Option Bytes) := kvFind k o.committed

/-- **The net requests** from `o` to `o'`: the committed entries of `o'` whose value differs from
`o`'s. -/
def netQ (o o' : Ovl) : KV := o'.committed.filter fun p => kvFind p.1 o.committed != some p.2

/-- A lookup updated by a request list (the first entry per key; with distinct keys, the
request). -/
def updK (q : KV) (f : Bytes → Option (Option Bytes)) (k : Bytes) : Option (Option Bytes) :=
  match kvFind k q with
  | some v => some v
  | none => f k

theorem kvFind_none_of {k : Bytes} : ∀ {l : KV}, k ∉ keys l → kvFind k l = none
  | [], _ => rfl
  | (k', v) :: rest, h => by
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    have hb : (k' == k) = false := by simpa using fun e => h.1 e.symm
    simp only [kvFind, hb, Bool.false_eq_true, ↓reduceIte]
    exact kvFind_none_of h.2

theorem mem_of_kvFind {k : Bytes} {v : Option Bytes} : ∀ {l : KV}, kvFind k l = some v → k ∈ keys l
  | [], h => by cases h
  | (k', w) :: rest, h => by
    simp only [kvFind] at h
    by_cases e : k' = k
    · subst e; simp [keys]
    · have hb : (k' == k) = false := by simpa using e
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (mem_of_kvFind h)

theorem kvFind_isSome_of_mem {k : Bytes} : ∀ {l : KV}, k ∈ keys l → ∃ v, kvFind k l = some v
  | [], h => by cases h
  | (k', w) :: rest, h => by
    simp only [kvFind]
    by_cases e : k' = k
    · subst e; exact ⟨w, by simp⟩
    · have hb : (k' == k) = false := by simpa using e
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      simp only [keys, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm e
      · exact kvFind_isSome_of_mem h

/-- A filter of a list with distinct keys: the lookup is the list's, if it passes the filter. -/
theorem kvFind_filter {k : Bytes} (p : Bytes × Option Bytes → Bool) :
    ∀ {l : KV}, (keys l).Nodup →
      kvFind k (l.filter p) = match kvFind k l with
        | some v => if p (k, v) then some v else none
        | none => none
  | [], _ => rfl
  | (k', w) :: rest, hn => by
    have hn' : (keys rest).Nodup := (List.nodup_cons.1 hn).2
    have hk' : k' ∉ keys rest := (List.nodup_cons.1 hn).1
    have ih := kvFind_filter (k := k) p hn'
    by_cases e : k' = k
    · subst e
      have hr : kvFind k' rest = none := kvFind_none_of hk'
      by_cases hp : p (k', w) = true
      · simp [List.filter_cons, hp, kvFind]
      · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, ih, hr, kvFind,
          beq_self_eq_true]
    · have hb : (k' == k) = false := by simpa using e
      by_cases hp : p (k', w) = true
      · simp only [List.filter_cons, hp, ↓reduceIte, kvFind, hb, Bool.false_eq_true]
        exact ih
      · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, kvFind, hb]
        exact ih

/-- **The per-key glue**: if `o'`'s committed keys are distinct and include `o`'s, then `o'`'s
committed lookups are `o`'s updated by the net requests. -/
theorem kv_net {o o' : Ovl} (hn : (keys o'.committed).Nodup)
    (hi : ∀ k ∈ keys o.committed, k ∈ keys o'.committed) (k : Bytes) :
    kv o' k = updK (netQ o o') (kv o) k := by
  unfold kv updK netQ
  rw [kvFind_filter _ hn]
  cases h' : kvFind k o'.committed with
  | none =>
    simp only
    cases h : kvFind k o.committed with
    | none => rfl
    | some v =>
      obtain ⟨w, hw⟩ := kvFind_isSome_of_mem (hi k (mem_of_kvFind h))
      rw [hw] at h'; cases h'
  | some v =>
    simp only
    by_cases hv : kvFind k o.committed = some v
    · simp [hv]
    · simp [hv]

/-! ## 3. STATE -/

/-- The overlay a configuration carries: the receipt state's at positions with one; at `start`, the
overlay the first step creates. -/
def ovE : RConf → Option Ovl
  | .base (.eng I c) =>
    match c.pos with
    | .start => some (Ovl.ofTrie I.prog.t)
    | p => ovlOfPos p
  | _ => none

/-- The input precondition: the carried overlay's committed keys are distinct. -/
def OvOK (x : RConf) : Prop := ∀ o, ovE x = some o → (keys o.committed).Nodup

/-- The output precondition: the configuration is not a finished engine. -/
def NotDone (x : RConf) : Prop := ∀ I c out, x = .base (.eng I c) → c.pos ≠ .done out

/-- STATE's precondition pair. -/
def StatePre (x x' : RConf) : Prop := OvOK x ∧ NotDone x'

theorem vfsteps_esteps {I : Intake} {c c' : EConf} (h : VFSteps I c c') : ESteps I.prog c c' := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (vfree_estep h) ih

theorem pq_of_ovE {I : Intake} {c : EConf} {o : Ovl} (h : ovE (.base (.eng I c)) = some o)
    (hn : (keys o.committed).Nodup) (hs : c.pos ≠ .start) :
    PQ o.trie (keys o.committed) c.pos := by
  simp only [ovE] at h
  cases hp : c.pos with
  | start => exact absurd hp hs
  | done out => rw [hp] at h; cases h
  | _ => rw [hp] at h; exact PQ.of_ovl h ⟨rfl, hn, fun _ h => h⟩

theorem ovE_of_pq {I : Intake} {c : EConf} {t : PTrie} {S : List Bytes} (h : PQ t S c.pos)
    (hd : ∀ out, c.pos ≠ .done out) :
    ∃ o, ovE (.base (.eng I c)) = some o ∧ OG t S o := by
  simp only [ovE]
  cases hp : c.pos with
  | start => rw [hp] at h; exact h.elim
  | done out => exact absurd hp (hd out)
  | txs _ _ rs => rw [hp] at h; exact ⟨rs.o, rfl, h⟩
  | locals _ rs => rw [hp] at h; exact ⟨rs.o, rfl, h⟩
  | delayed _ rs => rw [hp] at h; exact ⟨rs.o, rfl, h⟩
  | incoming _ rs => rw [hp] at h; exact ⟨rs.o, rfl, h⟩
  | yields _ _ _ _ _ rs => rw [hp] at h; exact ⟨rs.o, rfl, h⟩

/-- **STATE: lane F's side of the glue (`ReqsFaithful`), proved.** Along VM-free engine steps from
an overlay with distinct committed keys to a position that is not `done`, the trie is unchanged
and the committed lookups are the input's updated by the net requests. -/
theorem state_reqs {x x' : RConf} (hm : MState x x') (hp : StatePre x x') :
    ∃ o o', ovE x = some o ∧ ovE x' = some o' ∧ o'.trie = o.trie ∧
      ∀ k, kv o' k = updK (netQ o o') (kv o) k := by
  obtain ⟨hok, hnd⟩ := hp
  cases hm with
  | @run I c c' hv =>
  have hd' : ∀ out, c'.pos ≠ .done out := fun out => hnd I c' out rfl
  have he := vfsteps_esteps hv
  by_cases hs : c.pos = .start
  · -- the first step creates `Ovl.ofTrie I.prog.t`
    have ho : ovE (.base (.eng I c)) = some (Ovl.ofTrie I.prog.t) := by simp [ovE, hs]
    cases he with
    | refl =>
      refine ⟨_, _, ho, ho, rfl, fun k => ?_⟩
      exact kv_net (by simp [Ovl.ofTrie]) (fun _ h => h) k
    | @step _ b _ h1 h2 =>
      have hb : PQ I.prog.t [] b.pos := by
        obtain ⟨pos, r⟩ := c
        simp only at hs; subst hs
        exact estep_post (start_pq I.prog) h1
      obtain ⟨o', ho', hog⟩ := ovE_of_pq (I := I) (esteps_pqT _ _ _ h2 hb) hd'
      refine ⟨_, o', ho, ho', hog.trie, fun k => kv_net hog.nodup ?_ k⟩
      intro k hk; simp [Ovl.ofTrie, keys] at hk
  · cases ho : ovE (.base (.eng I c)) with
    | none =>
      exfalso
      simp only [ovE] at ho
      cases hp : c.pos with
      | start => exact hs hp
      | done out =>
        -- a run from `done` stays at `done` (`esteps_from_done`), contradicting `hd'`
        have := esteps_from_done I.prog (r := c.st) (by rw [← hp]; exact he)
        rw [this] at hd'; exact hd' out rfl
      | _ => rw [hp] at ho; simp [ovlOfPos] at ho
    | some o =>
      have hn := hok o ho
      have hq := esteps_pqT _ _ _ he (pq_of_ovE ho hn hs)
      obtain ⟨o', ho', hog⟩ := ovE_of_pq (I := I) hq hd'
      exact ⟨o, o', rfl, ho', hog.trie, fun k => kv_net hog.nodup hog.incl k⟩

/-! ### The split, relative and canonical, with a precondition -/

/-- The glue on the meaning instances satisfying `P`. -/
def SplitGlueOn {A : Airs8} {k : Tmpl} {S : SplitAir A k} (M : SplitSem S)
    (P : RConf → RConf → Prop) : Prop :=
  ∀ x x', Meaning k x x' → P x x' → M.wOut x' = M.apply (M.qOf x x') (M.wIn x)

/-- Lane F's `EngHalfRC` (`M5T1.SplitC`) with the precondition `P` of the meaning instance it opens
(STATE: the input overlay is `fits`-form, the output is not `done`). -/
def EngHalfRCOn (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl} {S : SplitAir A k}
    (M : SplitSem S) (P : RConf → RConf → Prop) (Bad : Prop) : Prop :=
  ∀ ctx b b' q r r', S.HoldsE ctx b b' q r r' → ∀ x, Canon sf x → b = lbOf V x →
    Bad ∨ ∃ x', Canon sf x' ∧ Meaning k x x' ∧ CtxLink k ctx x x' ∧ P x x' ∧ M.wIn x = r ∧
      q = M.qOf x x' ∧ (M.wOut x' = r' → b' = lbOf V x')

/-- **A split leaf is relatively, canonically sound** from its halves and the glue on `P`. -/
theorem split_sound_relC_on (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl}
    (S : SplitAir A k) (M : SplitSem S) (P : RConf → RConf → Prop) (Bad : Prop)
    (hE : EngHalfRCOn sf V M P Bad) (hS : StHalf M Bad) (hg : SplitGlueOn M P) :
    TmplSoundRel8C sf V A Bad k := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, r, r', h1, h2⟩ := S.joint ctx b b' tr hh
  rcases hE ctx b b' q r r' h1 x hc hx with hb | ⟨x', hc', hm, hl, hp, hr, hq, hout⟩
  · exact .inl hb
  rcases hS q r r' h2 with hb | hr'
  · exact .inl hb
  exact .inr ⟨x', hc', hout (by rw [hg x x' hm hp, ← hq, hr, hr']), hm, hl⟩

/-! ### The STATE split instance -/

/-- The intake of an engine configuration. -/
def intakeOf : RConf → Option Intake
  | .base (.eng I _) => some I
  | _ => none

/-- The STATE leaf's join as a `SplitAir` with the bus traffic a request list and the state value
the (optional) working-set root. -/
def stateAir {A : Airs8} (HoldsE : Bytes → LB → LB → KV → Option Bytes → Option Bytes → Prop)
    (HoldsS : KV → Option Bytes → Option Bytes → Prop)
    (joint : ∀ ctx b b' (tr : A.Tr (.tmpl .state)), A.Holds (.tmpl .state) ctx b b' tr →
      ∃ q r r', HoldsE ctx b b' q r r' ∧ HoldsS q r r') : SplitAir A .state :=
  ⟨KV, Option Bytes, HoldsE, HoldsS, joint⟩

/-- The state value of a configuration: lane B's working-set root (`root I trie lookups`: the root
over the chunk's keys `κ I` of the entries `(k, pre(trie, k), cur, written)`, `StateViewParams`'s
`wsRoot` of `entryAt`) of its overlay. -/
def wS (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes) (x : RConf) :
    Option Bytes :=
  match intakeOf x, ovE x with
  | some I, some o => some (root I o.trie (kv o))
  | _, _ => none

/-- The STATE split semantics (lane B's `apply` lifted to the optional value). -/
def stateSem {A : Airs8} {HoldsE HoldsS joint}
    (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes)
    (apply : KV → Bytes → Bytes) : SplitSem (stateAir (A := A) HoldsE HoldsS joint) where
  wIn := wS root
  wOut := wS root
  qOf x x' := match ovE x, ovE x' with
    | some o, some o' => netQ o o'
    | _, _ => []
  apply q r := r.map (apply q)

/-- **Lane B's side of the STATE glue** (`ApplyFaithful` at the working-set level): its state
function applied to a request list computes the root of the updated lookups (`m5tSeg`: `WsBus.
seg_root`, `chain_sound`; the trie, hence every `pre`, is unchanged). -/
def ApplyFaithfulS (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes)
    (apply : KV → Bytes → Bytes) : Prop :=
  ∀ I t f q, apply q (root I t f) = root I t (updK q f)

/-- **The STATE glue** (lane E): from lane B's `ApplyFaithfulS`, on STATE's precondition. -/
theorem state_glue {A : Airs8} {HoldsE HoldsS joint}
    (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes)
    (apply : KV → Bytes → Bytes) (hB : ApplyFaithfulS root apply) :
    SplitGlueOn (stateSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint) root apply)
      StatePre := by
  intro x x' hm hp
  obtain ⟨o, o', ho, ho', ht, hk⟩ := state_reqs hm hp
  cases hm with
  | @run I c c' _ =>
  simp only [stateSem, wS, intakeOf, ho, ho', Option.map_some, Option.some.injEq, ht]
  rw [hB, show kv o' = updK (netQ o o') (kv o) from funext hk]

/-- **STATE is relatively, canonically sound** from lane F's engine half (with the
precondition), lane B's state half and lane B's `ApplyFaithfulS`. -/
theorem state_sound_relC (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint}
    (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes)
    (apply : KV → Bytes → Bytes) (Bad : Prop)
    (hE : EngHalfRCOn sf V (stateSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS)
      (joint := joint) root apply) StatePre Bad)
    (hS : StHalf (stateSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint) root
      apply) Bad)
    (hB : ApplyFaithfulS root apply) : TmplSoundRel8C sf V A Bad .state :=
  split_sound_relC_on sf V _ _ StatePre Bad hE hS (state_glue root apply hB)

/-! ## 4. INIT -/

/-- **The INIT glue**: INIT's output `eng I ⟨start, _⟩` carries the intake's partial trie with no
committed change, so its working-set root is lane B's IF-INTAKE `R_0` (`root I I.tMain (fun _ =>
none)`: every entry `(k, pre, pre, false)`). -/
theorem init_glue (root : Intake → PTrie → (Bytes → Option (Option Bytes)) → Bytes) (I : Intake)
    (r : Recording) :
    ovE (.base (.eng I ⟨.start, r⟩)) = some (Ovl.ofTrie I.tMain) ∧
    wS root (.base (.eng I ⟨.start, r⟩)) = some (root I I.tMain fun _ => none) := by
  refine ⟨rfl, ?_⟩
  simp only [wS, intakeOf, ovE]
  congr 2

/-- **D-a: the view's state component at `start` carries the overlay the STATE glue starts from.** -/
theorem init_glue_view (κ : Intake → List Bytes) (I : Intake) (r : Recording) :
    (split κ (.base (.eng I ⟨.start, r⟩))).2.2.1 =
      .eng .start ⟨r, κ I, ovE (.base (.eng I ⟨.start, r⟩))⟩ := rfl

/-- INIT's meaning ends at `eng I ⟨start, _⟩` or at `gfin` (`init_step_shape`); in the first case the
engine configuration is at `start` (the intake step's continuation, `Machine.lean`). -/
theorem init_out_shape {cb wb : Bytes} {c : Conf} (h : CM.step (.init cb wb) = .ok c) :
    (∃ I e, c = .eng I e) ∨ ∃ G, c = .gfin G := init_step_shape h

/-! ## 5. FINAL -/

/-- **The FINAL glue** (D2 level): lane B's `m5b_final` conclusion for the overlay's trie and its
sorted committed changes is the overlay's `finalize`. -/
theorem final_glue {o : Ovl} {T T' : PTrie} {post : Bytes} {n : KV} (ht : o.trie = T)
    (hne : ∀ h, T = .hash h → h ≠ emptyRoot) (hs : sortKV o.committed = sortKV n)
    (hB : applyChanges (some T) (sortKV n) = some (some T') ∧ rootHash (some T') = post) :
    o.finalize = .ok post := by
  simp only [Ovl.finalize, ht, hs]
  cases T with
  | hash h =>
    have := hne h rfl
    simp only [beq_iff_eq, this, ↓reduceIte, hB.1, hB.2]
  | _ => simp only [hB.1, hB.2]

/-- The named FINAL premise (open): the checker's logged, lazy-trie finalize returns the D2
finalize of the same overlay. -/
def FinalizeAgree : Prop :=
  ∀ (o : Ovl) (r : Recording) (e : Env) (a : Bytes) (r' : Recording),
    finalizeR o r e = .ok (a, r') → o.finalize = .ok a

/-! ## 6. Honest runs are store-canonical: the structural part

`Canon sf x` (S1) asks every store in a call configuration to be `sf I`. On the honest run the
receipt step builds each query's `RealStore` with `store := fun hb => (env.codeOf (ofBA hb)).map
toBA` (`CutW.lean`), so the canonical store function is `sfE` below. The lemmas reduce canonicity
along an honest `RCM` run to two store facts:
* **(H1) the queries** — every query the honest engine issues for `I` has store `sfE I` (the
  receipt step's `env` is the program's `I.prog.env = I.env`; a walk over the `CutW` copies like
  `Tape.pwO_tle`, open);
* **(H2) the call machine** — a call-machine step keeps a canonical configuration canonical
  (lane A: `SegStore.seg_setSt`, `enter_setSt`, `TmplPrep.preConf_canon`; the whole-call answer
  `callResult q` likewise, for the tape entries).
`canon_enter` / `canon_next` / `canon_wasm` are the three `RCM` edges that create call
configurations; `base` configurations are canonical (`canon_base`). -/

/-- The canonical store of an intake: the code lookup of its environment (`CutW`'s query store). -/
def sfE (I : Intake) : TTN.Store := fun hb => (I.env.codeOf (NearSpecV3.D3.ofBA hb)).map NearSpecV3.D3.toBA

theorem setArgs_of_store {s : TTN.Store} {q : CutW.VmQ} (h : q.real.store = s) : setArgs s q = q := by
  cases q with
  | mk cfg code method ctx real =>
    cases real
    simp only at h
    subst h
    rfl

/-- **Enter**: a call started with a canonical query is canonical. -/
theorem canon_enter (sf : Intake → TTN.Store) (I : Intake) (c : EConf) (q : CutW.VmQ)
    (hq : q.real.store = sf I) : Canon sf (.call I c [] q .pre) := by
  simp only [Canon, setR, setK, List.map_nil, setConf, setArgs_of_store hq]

/-- **Next**: recording a canonical answer and starting a canonical query keeps canonicity. -/
theorem canon_next (sf : Intake → TTN.Store) {I : Intake} {c : EConf} {K : VmV} {q q' : CutW.VmQ}
    {r : Run} (hx : Canon sf (.call I c K q (.fin r))) (hq' : q'.real.store = sf I) :
    Canon sf (.call I c (K ++ [(q, r)]) q' .pre) := by
  simp only [Canon, setR, RConf.call.injEq, true_and] at hx ⊢
  obtain ⟨hK, hq, hr⟩ := hx
  have hr' : setRun (sf I) r = r := by simpa [setConf] using hr
  refine ⟨?_, setArgs_of_store hq', rfl⟩
  simp only [setK, List.map_append, List.map_cons, List.map_nil] at hK ⊢
  rw [hK, hq, hr']

/-- **Wasm**: a call-machine step that keeps the configuration's stores (H2) keeps canonicity. -/
theorem canon_wasm (sf : Intake → TTN.Store) {I : Intake} {c : EConf} {K : VmV} {q : CutW.VmQ}
    {cc cc' : CallCut.CallConf} (hx : Canon sf (.call I c K q cc)) (h2 : setConf (sf I) cc' = cc') :
    Canon sf (.call I c K q cc') := by
  simp only [Canon, setR, RConf.call.injEq, true_and] at hx ⊢
  exact ⟨hx.1, hx.2.1, h2⟩

#print axioms canon_enter
#print axioms canon_next
#print axioms canon_wasm
#print axioms stepM_pqT
#print axioms esteps_pqT
#print axioms kv_net
#print axioms state_reqs
#print axioms split_sound_relC_on
#print axioms state_glue
#print axioms state_sound_relC
#print axioms init_glue
#print axioms init_glue_view
#print axioms final_glue

end NearSpecV3.E2E.Glue
