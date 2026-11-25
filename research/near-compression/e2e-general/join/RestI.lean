
/-!
# Lane E, decision D-d: an incremental encoding of lane B's `rest`

Appended to `join/StViewE.lean` (not a lake module; `m5a/lean/join-check/run.sh` elaborates the
concatenation in lane B's package environment).

## The cost today

Lane B's `stRoot` carries `rest = bdigest (encRestB (restOfB v))`, where `restOfB v = (strip v,
ovlRest o)` is the **whole** state component minus the working set: the chunk's key list `κ I`
(every key the chunk touches), the position with its pending queue (the remaining transactions /
local / incoming receipts: witness-sized), the receipt state without the overlay, the recorder,
the start overlay, and the overlay's remainder — the partial trie's reveal shape `erase o.trie`
(the whole revealed pre-state structure), the committed key order, the prospective changes, the
removal count. A STATE / resume leaf recomputes `rest_out` from scratch: **one witness-sized hash
per engine step** (lane B's B-T2 finding), although the key list and the trie shape never change
along a run and the queue only loses its head.

## The encoding (`encRestI`)

`encRestI r = d_static ‖ d_queue ‖ d_move` (3 × 42 B; `rest = bdigest` of these 126 B):

| part | content | changes along a run | cost per engine step |
|---|---|---|---|
| `d_static` | `bdigest (d_keys ‖ d_shape)` (M14), `d_keys = bdigest (Ser.enc keys)`, `d_shape = bdigest (Ser.enc (erase trie))` — the chunk's key list and the trie's reveal shape (`restStatic`) | never before `done` (the trie is never modified; `κ I` is constant); the finalize step copies `d_keys` and sets `d_shape = bdigest (Ser.enc none)` | 0 (opened as 42 B, copied) |
| `d_queue` | `chainR id (pendQ v)` — a **cons chain** over the serialised pending items of the position (`txs` / `locals` / `incoming`) | the head is consumed | one SHA-384 of `42 + |item|` bytes per consumed item (`chainR_cons`: `d = bdigest (d_tail ‖ item)`; the leaf opens `d` into `d_tail` and the item) |
| `d_move` | `bdigest (Ser.enc (blankQ v, moving o))` — the position with the queue and the key list blanked, the receipt state without the overlay and output lists, the recorder, the committed key order, the prospective changes, the removal count (`restMove`) | every step | one hash of the moving state: `O(|RS| + |recorder| + |committed keys|)`, independent of the witness's key list, trie and pending receipts |

**Binding** (`encRestI_bind`): equal encodings give equal remainders or a `bdigest` collision
(`Sha384Coll`): the three 42-B digests split by length, `chainR_binding` for the queue, and
`restRecon` (the static part, the queue and the moving part determine the remainder). So
`stViewParams_BI` — lane B's parameters with `encRest := encRestI` — is a valid `StViewParams`
(lane B's `encRest_bind` field, generalised for this in D-d), and `stD_binding` holds for it
unchanged (`stD_binding_BI`).

## What the circuit does (interface change for lanes B / F)

`STC` opens `rest` (42 B) into its 126-B preimage; the engine half receives `(d_static, d_queue,
d_move)` instead of one digest. A step that consumes `n` pending items opens `d_queue` `n` times
(cons-chain pops); every step recomputes `d_move`; `d_static` is copied. `rest_out` costs one
compression of 126 B plus the pops and `d_move`, instead of the whole remainder. The remaining
large term is `d_move`'s receipt state (its own lists — `locals`, `limits`, `metas`, `bufIdx`,
`instant`, `deployed`, `attempted` — and the committed key order); splitting it further the same
way (a snoc chain `chainD` for the append-only committed key order) is the next step if lane F's
measured `d_move` is large.
-/

namespace LaneE.RestI

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.Enc
open StateM5a.StateView StateM5a.StateViewParams LaneE.StViewEJoin

abbrev Bytes := NearSpec.Bytes

/-! ## The parts -/

/-- The pending queue of a state component's position (serialised items). -/
def pendQ : StV → List Bytes
  | .eng (.txs rest _ _) _ => rest.map Ser.enc
  | .eng (.locals rest _) _ => rest.map Ser.enc
  | .eng (.incoming rest _) _ => rest.map Ser.enc
  | _ => []

/-- The position with its pending queue blanked. -/
def blankP : EPos → EPos
  | .txs _ acc rs => .txs [] acc rs
  | .locals _ rs => .locals [] rs
  | .incoming _ rs => .incoming [] rs
  | p => p

/-- The state component with the pending queue and the key list blanked. -/
def blankQ : StV → StV
  | .eng p st => .eng (blankP p) { st with keys := [] }
  | v => v

/-- The static part of a remainder: the key list and the trie's reveal shape. -/
def restStatic (r : RestB) : List Bytes × Option PTrie := (keysOf r.1, r.2.map (·.1))

/-- The moving part: the blanked component and the overlay's other parts. -/
def restMove (r : RestB) : StV × Option (List Bytes × List (Bytes × Option Bytes) × Nat) :=
  (blankQ r.1, r.2.map (·.2))

/-- The key list of a remainder (`restStatic`'s first part). -/
def restKeys (r : RestB) : List Bytes := keysOf r.1

/-- The trie's reveal shape (`none` without an overlay: `done`). -/
def restShape (r : RestB) : Option PTrie := r.2.map (·.1)

/-- `d_keys`: the key list's digest. -/
def dKeys (r : RestB) : Bytes := bdigest (Ser.enc (restKeys r))

/-- `d_shape`: the reveal shape's digest. -/
def dShape (r : RestB) : Bytes := bdigest (Ser.enc (restShape r))

/-- **`d_static = bdigest (d_keys ‖ d_shape)`** (M14: two sub-digests, so that the finalize step,
which drops the overlay, copies `d_keys` and replaces `d_shape` by the constant
`bdigest (Ser.enc none)` instead of re-hashing the key list). -/
def dStatic (r : RestB) : Bytes := bdigest (dKeys r ++ dShape r)

/-- `d_queue`: the cons chain over the pending items. -/
def dQueue (r : RestB) : Bytes := chainR id (pendQ r.1)

/-- `d_move`: the moving part's digest. -/
def dMove (r : RestB) : Bytes := bdigest (Ser.enc (restMove r))

/-- **The incremental remainder encoding**: `d_static ‖ d_queue ‖ d_move`. -/
def encRestI (r : RestB) : Bytes := dStatic r ++ (dQueue r ++ dMove r)

/-- Popping the queue's head costs one hash of the tail digest and the item. -/
theorem chainR_cons (a : Bytes) (l : List Bytes) : chainR id (a :: l) = bdigest (chainR id l ++ a) :=
  rfl

/-! ## Reconstruction -/

theorem map_enc_inj {α : Type} [Ser α] : ∀ (l l' : List α), l.map Ser.enc = l'.map Ser.enc → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Ser.pf.inj h.1, map_enc_inj l l' h.2]

/-- **The key list, the queue and the blanked component determine the component.** -/
theorem stv_recon (a b : StV) (hk : keysOf a = keysOf b) (hq : pendQ a = pendQ b)
    (hb : blankQ a = blankQ b) : a = b := by
  cases a with
  | none => cases b <;> simp_all [blankQ]
  | fin o => cases b <;> simp_all [blankQ]
  | eng p st =>
    cases b with
    | none => simp [blankQ] at hb
    | fin o => simp [blankQ] at hb
    | eng p' st' =>
      obtain ⟨r, K, o0⟩ := st
      obtain ⟨r', K', o0'⟩ := st'
      simp only [keysOf] at hk
      subst hk
      simp only [blankQ, StV.eng.injEq, EngSt.mk.injEq, true_and] at hb
      obtain ⟨hp, rfl, rfl⟩ := hb
      cases p <;> cases p' <;> simp_all [blankP, pendQ] <;> exact map_enc_inj _ _ hq

theorem opt_recon {α β : Type} (a b : Option (α × β)) (h1 : a.map (·.1) = b.map (·.1))
    (h2 : a.map (·.2) = b.map (·.2)) : a = b := by
  cases a <;> cases b <;> simp_all [Prod.ext_iff]

/-- **The static part, the queue and the moving part determine the remainder.** -/
theorem restRecon (a b : RestB) (hs : restStatic a = restStatic b) (hq : pendQ a.1 = pendQ b.1)
    (hm : restMove a = restMove b) : a = b := by
  obtain ⟨v, o⟩ := a
  obtain ⟨v', o'⟩ := b
  simp only [restStatic, restMove, Prod.mk.injEq] at hs hm
  rw [stv_recon v v' hs.1 hq hm.1, opt_recon o o' hs.2 hm.2]

/-! ## Binding -/

theorem coll_or_eq {m m' : Bytes} (h : bdigest m = bdigest m') : Sha384Coll ∨ m = m' := by
  classical
  by_cases e : m = m'
  · exact .inr e
  · exact .inl ⟨m, m', e, h⟩

/-- `d_static` is binding: equal static digests give equal static parts, or a collision. -/
theorem dStatic_bind (a b : RestB) (h : dStatic a = dStatic b) : Sha384Coll ∨ restStatic a = restStatic b := by
  unfold dStatic at h
  rcases coll_or_eq h with c | h
  · exact .inl c
  obtain ⟨hk, hs⟩ := List.append_inj h (by simp only [dKeys, bdigest_length])
  unfold dKeys at hk
  unfold dShape at hs
  rcases coll_or_eq hk with c | hk
  · exact .inl c
  rcases coll_or_eq hs with c | hs
  · exact .inl c
  have e1 : restKeys a = restKeys b := Ser.pf.inj hk
  have e2 : restShape a = restShape b := Ser.pf.inj hs
  exact .inr (by simp only [restStatic]; simp only [restKeys, restShape] at e1 e2; rw [e1, e2])

/-- **`encRestI` is binding**: equal encodings give equal remainders, or a `bdigest` collision. -/
theorem encRestI_bind (a b : RestB) (h : encRestI a = encRestI b) : Sha384Coll ∨ a = b := by
  unfold encRestI at h
  obtain ⟨h1, h⟩ := List.append_inj h (by simp only [dStatic, bdigest_length])
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp only [dQueue, chainR_length])
  rcases dStatic_bind a b h1 with c | e1
  · exact .inl c
  rcases chainR_binding id (fun _ _ h => h) _ _ h2 with e2 | c
  · unfold dMove at h3
    rcases coll_or_eq h3 with c | e3
    · exact .inl c
    exact .inr (restRecon a b e1 e2 (Ser.pf.inj e3))
  · exact .inl c

/-- **Lane B's parameters with the incremental remainder.** -/
def stViewParams_BI : StViewParams :=
  { stViewParams_B stViewE with
    encRest := encRestI
    encRest_bind := fun _ _ _ _ h => encRestI_bind _ _ h }

/-- **The state commitment with the incremental remainder is binding.** -/
theorem stD_binding_BI (h : Coll (stD stViewParams_BI)) : Sha384Coll ∨ Sha256Coll ∨ LeafColl :=
  stD_binding _ h

/-- The remainder's preimage is 126 bytes (three digests). -/
theorem encRestI_length (r : RestB) : (encRestI r).length = 3 * digestLen := by
  simp only [encRestI, dStatic, dQueue, dMove, List.length_append, bdigest_length, chainR_length]; omega

/-! ## E2E-M14: the position tag and the opening interface

### The tag (`StateView.posTag`)

`tagOf (.eng p _) = posTag p` separates the positions (`start` 1, `done` 3, `txs` 4, `locals` 5,
`delayed` 6, `incoming` 7, `yields _ _ 0` 8 — the finalize precondition — other `yields` 9). It is a
function of the state component, so `stD` stays a function and `stD_binding_BI` is unchanged: the
tag is one more field `proj_inj` is given as a hypothesis, and `ser_ne_raw` needs only `tagOf ≤ 9 <
255`. It is also a function of the moving part (`tagOf_restMove`), so it adds no information to the
commitment; it makes the position class readable from one byte of the `STC` opening
(`tag_sound`), which is what a leaf needs to know *which* step it proves before opening `rest`
(`finPos_of_tag`, `incoming_of_tag`, `done_of_tag`). -/

theorem posTag_eposMap (f : RS → RS) (p : EPos) : posTag (eposMap f p) = posTag p := by
  cases p with
  | yields yf yn fu i k rs => cases fu <;> rfl
  | _ => rfl

theorem posTag_blankP (p : EPos) : posTag (blankP p) = posTag p := by
  cases p with
  | yields yf yn fu i k rs => cases fu <;> rfl
  | _ => rfl

theorem tagOf_strip (v : StV) : tagOf (strip v) = tagOf v := by
  cases v with
  | eng p st =>
    cases p with
    | start => rfl
    | _ => simp only [strip, setOvl, tagOf]; exact posTag_eposMap _ _
  | _ => rfl

theorem tagOf_blankQ (v : StV) : tagOf (blankQ v) = tagOf v := by
  cases v with
  | eng p st => exact posTag_blankP p
  | _ => rfl

/-- **The tag is a function of the moving part** (`d_move`'s preimage carries the position). -/
theorem tagOf_restMove (v : StV) : tagOf (restMove (restOfB v)).1 = tagOf v := by
  simp only [restMove, restOfB, tagOf_blankQ, tagOf_strip]

/-- The view's state component carries the configuration's position tag. -/
theorem tagOf_stOfI (κ : Intake → List Bytes) (I : Intake) (c : EConf) :
    tagOf (stOfI κ I c) = posTag c.pos := posTag_eposMap _ _

theorem posTag_eq8 {p : EPos} (h : posTag p = 8) : ∃ yf yn i k rs, p = .yields yf yn 0 i k rs := by
  cases p with
  | yields yf yn fu i k rs => cases fu with
    | zero => exact ⟨yf, yn, i, k, rs, rfl⟩
    | succ => simp [posTag] at h
  | _ => simp [posTag] at h

theorem posTag_eq7 {p : EPos} (h : posTag p = 7) : ∃ l rs, p = .incoming l rs := by
  cases p with
  | incoming l rs => exact ⟨l, rs, rfl⟩
  | yields yf yn fu i k rs => cases fu <;> simp [posTag] at h
  | _ => simp [posTag] at h

theorem posTag_eq5 {p : EPos} (h : posTag p = 5) : ∃ l rs, p = .locals l rs := by
  cases p with
  | locals l rs => exact ⟨l, rs, rfl⟩
  | yields yf yn fu i k rs => cases fu <;> simp [posTag] at h
  | _ => simp [posTag] at h

theorem posTag_eq4 {p : EPos} (h : posTag p = 4) : ∃ l acc rs, p = .txs l acc rs := by
  cases p with
  | txs l acc rs => exact ⟨l, acc, rs, rfl⟩
  | yields yf yn fu i k rs => cases fu <;> simp [posTag] at h
  | _ => simp [posTag] at h

theorem posTag_eq3 {p : EPos} (h : posTag p = 3) : ∃ out, p = .done out := by
  cases p with
  | done out => exact ⟨out, rfl⟩
  | yields yf yn fu i k rs => cases fu <;> simp [posTag] at h
  | _ => simp [posTag] at h

theorem ser_ne_255 (c : StCommit) (ht : c.tag < 255) (r : Bytes) : c.ser ≠ (255 : UInt8) :: r := by
  rw [ser_cons]; intro h; simp only [List.cons.injEq] at h
  have h1 := congrArg UInt8.toNat h.1
  have h255 : (255 : UInt8).toNat = 255 := rfl
  rw [StateM5a.SerInj.ofNat_toNat, h255] at h1
  have : c.tag % 256 = c.tag := Nat.mod_eq_of_lt (by omega)
  omega

/-- **An opening is the state's commitment** (any `StViewParams`): a well-formed opening `c` of
`stD P v` (tag `< 255`) is `v`'s circuit-form commitment — or there is a collision. -/
theorem tag_sound (P : StViewParams) (v : StV) (c : StCommit) (hw : c.WF) (ht : c.tag < 255)
    (hd : bdigest c.ser = stD P v) : Sha384Coll ∨ (P.fits v = true ∧ c = commitOf P v) := by
  classical
  cases hf : P.fits v
  · simp only [stD, hf, Bool.false_eq_true, ite_false] at hd
    exact .inl ⟨_, _, ser_ne_255 c ht _, hd⟩
  · simp only [stD, hf, ite_true] at hd
    by_cases hs : c.ser = (commitOf P v).ser
    · exact .inr ⟨rfl, ser_inj _ _ hw (commitOf_wf P v hf) hs⟩
    · exact .inl ⟨_, _, hs, hd⟩

/-- **The tag of an opening is the state's tag.** -/
theorem tag_eq (P : StViewParams) (v : StV) (c : StCommit) (hw : c.WF) (ht : c.tag < 255)
    (hd : bdigest c.ser = stD P v) : Sha384Coll ∨ c.tag = tagOf v := by
  rcases tag_sound P v c hw ht hd with h | ⟨-, rfl⟩
  · exact .inl h
  · exact .inr rfl

/-- **The finalize precondition from one byte**: an opening with tag 8 of the view's `stRoot` of
`c` makes `c.pos = yields _ _ 0 _ _ _` (`GlueFin.FinPre`'s position), or there is a collision. Lane
B's finalize `STC` row checks `tag_in = 8`, `tag_out = 3`. -/
theorem finPos_of_tag (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (c : EConf)
    (cm : StCommit) (hw : cm.WF) (ht : cm.tag = 8) (hd : bdigest cm.ser = stD P (stOfI κ I c)) :
    Sha384Coll ∨ ∃ yf yn i k rs, c.pos = .yields yf yn 0 i k rs := by
  rcases tag_eq P _ cm hw (by omega) hd with h | h
  · exact .inl h
  · rw [tagOf_stOfI, ht] at h
    exact .inr (posTag_eq8 h.symm)

/-- An opening with tag 7: the configuration is at an `incoming` position. -/
theorem incoming_of_tag (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (c : EConf)
    (cm : StCommit) (hw : cm.WF) (ht : cm.tag = 7) (hd : bdigest cm.ser = stD P (stOfI κ I c)) :
    Sha384Coll ∨ ∃ l rs, c.pos = .incoming l rs := by
  rcases tag_eq P _ cm hw (by omega) hd with h | h
  · exact .inl h
  · rw [tagOf_stOfI, ht] at h
    exact .inr (posTag_eq7 h.symm)

/-- An opening with tag 3: the configuration is `done`. -/
theorem done_of_tag (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (c : EConf)
    (cm : StCommit) (hw : cm.WF) (ht : cm.tag = 3) (hd : bdigest cm.ser = stD P (stOfI κ I c)) :
    Sha384Coll ∨ ∃ out, c.pos = .done out := by
  rcases tag_eq P _ cm hw (by omega) hd with h | h
  · exact .inl h
  · rw [tagOf_stOfI, ht] at h
    exact .inr (posTag_eq3 h.symm)

/-! ### The opening interface (lanes B and F)

What a leaf witnesses and checks to step from a state component `v` whose `stRoot` its `STC` row
opened (`StHalfC.st_step` gives `metaOf P v = mi`, so `mi.rest = bdigest (encRestI (restOfB v))`):

| check (in-circuit) | lemma | gives |
|---|---|---|
| `bdigest (dS ‖ dQ ‖ dM) = mi.rest` (126 B), each part 42 B | `rest_open` | `dS = dStatic`, `dQ = dQueue`, `dM = dMove` of `restOfB v` |
| `bdigest (Ser.enc x) = dM` (`x` witnessed: the blanked position, the receipt state without overlay / outputs / queue, the recorder; the committed key order, prospective changes, removal count) | `move_open` | `x = restMove (restOfB v)` |
| pop: `bdigest (dT ‖ a) = dQ` (`|dT| = 42`) | `queue_pop` | `pendQ v = a :: tl`, `chainR id tl = dT` |
| `a = Ser.enc y` (`y` witnessed, serialised in-circuit) | `incoming_head` / `locals_head` / `txs_head` (+ `Ser.pf.inj`) | `y` is the position's next item |
| empty: `dQ = bdigest []` | `queue_empty` | `pendQ v = []` (the `[]` case of `stepM`) |
| static (lane B's IF / the finalize step): `bdigest (dK ‖ dSh) = dS`, `bdigest (Ser.enc K) = dK` | `static_open`, `keys_open` | `dK = bdigest (Ser.enc (κ I))`, `K = κ I` |
| output: `mo.rest = bdigest (dS' ‖ dQ' ‖ bdigest (Ser.enc x'))`, `dS' = dS` (copied; finalize: `bdigest (dK ‖ bdigest (Ser.enc none))`), `dQ' = dT` or a new chain, `x'` the stepped moving part | `rest_close` | `mo = metaOf P v'` for the stepped `v'` (`StHalfC.StepRel`'s last conjunct) |

`open_pop` is the composition a step that consumes one item uses. -/

theorem bdigest_ne_nil_of (m : Bytes) (h : m ≠ []) : bdigest m = bdigest [] → Sha384Coll :=
  fun e => ⟨m, [], h, e⟩

/-- **Opening `rest`** into its three digests. -/
theorem rest_open (r : RestB) (dS dQ dM : Bytes) (h1 : dS.length = digestLen)
    (h2 : dQ.length = digestLen) (h : bdigest (dS ++ (dQ ++ dM)) = bdigest (encRestI r)) :
    Sha384Coll ∨ (dS = dStatic r ∧ dQ = dQueue r ∧ dM = dMove r) := by
  rcases coll_or_eq h with c | h
  · exact .inl c
  unfold encRestI at h
  obtain ⟨e1, h⟩ := List.append_inj h (by rw [h1]; simp only [dStatic, bdigest_length])
  obtain ⟨e2, e3⟩ := List.append_inj h (by rw [h2]; simp only [dQueue, chainR_length])
  exact .inr ⟨e1, e2, e3⟩

/-- **Opening `d_static`** into `d_keys ‖ d_shape`. -/
theorem static_open (r : RestB) (dK dSh : Bytes) (hk : dK.length = digestLen)
    (h : bdigest (dK ++ dSh) = dStatic r) : Sha384Coll ∨ (dK = dKeys r ∧ dSh = dShape r) := by
  unfold dStatic at h
  rcases coll_or_eq h with c | h
  · exact .inl c
  obtain ⟨e1, e2⟩ := List.append_inj h (by rw [hk]; simp only [dKeys, bdigest_length])
  exact .inr ⟨e1, e2⟩

/-- **Opening `d_keys`**: a witnessed key list hashing to it is the component's key list. -/
theorem keys_open (r : RestB) (K : List Bytes) (h : bdigest (Ser.enc K) = dKeys r) :
    Sha384Coll ∨ K = restKeys r := by
  unfold dKeys at h
  rcases coll_or_eq h with c | h
  · exact .inl c
  · exact .inr (Ser.pf.inj h)

/-- **Opening `d_move`**: a witnessed moving part hashing to it is the component's. -/
theorem move_open (r : RestB) (x : StV × Option (List Bytes × List (Bytes × Option Bytes) × Nat))
    (h : bdigest (Ser.enc x) = dMove r) : Sha384Coll ∨ x = restMove r := by
  unfold dMove at h
  rcases coll_or_eq h with c | h
  · exact .inl c
  · exact .inr (Ser.pf.inj h)

/-- **Popping `d_queue`**: `bdigest (dT ‖ a) = chainR id l` makes `a` the head of `l` and `dT` the
tail's chain. -/
theorem queue_pop (l : List Bytes) (dT a : Bytes) (hT : dT.length = digestLen)
    (h : bdigest (dT ++ a) = chainR id l) : Sha384Coll ∨ ∃ tl, l = a :: tl ∧ chainR id tl = dT := by
  cases l with
  | nil =>
    refine .inl (bdigest_ne_nil_of _ ?_ h)
    intro e; have := congrArg List.length e; simp [hT, digestLen] at this
  | cons b tl =>
    simp only [chainR] at h
    rcases coll_or_eq h with c | h
    · exact .inl c
    obtain ⟨e1, e2⟩ := List.append_inj h (by rw [hT, chainR_length])
    exact .inr ⟨tl, by rw [e2]; rfl, e1.symm⟩

/-- **An empty `d_queue`**: `bdigest [] = chainR id l` makes `l = []`. -/
theorem queue_empty (l : List Bytes) (h : bdigest [] = chainR id l) : Sha384Coll ∨ l = [] := by
  rcases chainR_binding id (fun _ _ h => h) [] l h with e | c
  · exact .inr e.symm
  · exact .inl c

/-- The pending queue does not see the overlay. -/
theorem pendQ_strip (v : StV) : pendQ (strip v) = pendQ v := by
  cases v with
  | eng p st => cases p <;> rfl
  | _ => rfl

/-- **The queue head of an `incoming` position** is a serialised receipt, the position's next one. -/
theorem incoming_head {p : EPos} {st : EngSt} {a : Bytes} {tl : List Bytes}
    (h : pendQ (.eng p st) = a :: tl) (hp : posTag p = 7) :
    ∃ r rest rs, p = .incoming (r :: rest) rs ∧ Ser.enc r = a ∧ rest.map Ser.enc = tl := by
  obtain ⟨l, rs, rfl⟩ := posTag_eq7 hp
  cases l with
  | nil => simp [pendQ] at h
  | cons r rest =>
    simp only [pendQ, List.map_cons, List.cons.injEq] at h
    exact ⟨r, rest, rs, rfl, h.1, h.2⟩

/-- The same for `locals`. -/
theorem locals_head {p : EPos} {st : EngSt} {a : Bytes} {tl : List Bytes}
    (h : pendQ (.eng p st) = a :: tl) (hp : posTag p = 5) :
    ∃ r rest rs, p = .locals (r :: rest) rs ∧ Ser.enc r = a ∧ rest.map Ser.enc = tl := by
  obtain ⟨l, rs, rfl⟩ := posTag_eq5 hp
  cases l with
  | nil => simp [pendQ] at h
  | cons r rest =>
    simp only [pendQ, List.map_cons, List.cons.injEq] at h
    exact ⟨r, rest, rs, rfl, h.1, h.2⟩

/-- The same for `txs`. -/
theorem txs_head {p : EPos} {st : EngSt} {a : Bytes} {tl : List Bytes}
    (h : pendQ (.eng p st) = a :: tl) (hp : posTag p = 4) :
    ∃ x rest acc rs, p = .txs (x :: rest) acc rs ∧ Ser.enc x = a ∧ rest.map Ser.enc = tl := by
  obtain ⟨l, acc, rs, rfl⟩ := posTag_eq4 hp
  cases l with
  | nil => simp [pendQ] at h
  | cons x rest =>
    simp only [pendQ, List.map_cons, List.cons.injEq] at h
    exact ⟨x, rest, acc, rs, rfl, h.1, h.2⟩

/-- **Closing**: the output `rest` from the copied static digest, the queue digest and the stepped
moving part (definitional; the leaf computes the right-hand side). -/
theorem rest_close (r r' : RestB) (dT : Bytes)
    (x' : StV × Option (List Bytes × List (Bytes × Option Bytes) × Nat))
    (hs : dStatic r' = dStatic r) (hq : dQueue r' = dT) (hm : restMove r' = x') :
    bdigest (encRestI r') = bdigest (dStatic r ++ (dT ++ bdigest (Ser.enc x'))) := by
  rw [← hs, ← hq, ← hm]; rfl

/-- The meta (`StHalfC.metaOf`) of lane B's parameters with `encRestI`. -/
theorem metaOf_BI (v : StV) :
    StateM5a.StHalfC.metaOf stViewParams_BI v = ⟨tagOf v, bdigest (encRestI (restOfB v))⟩ := rfl

/-- **The composed opening of a step that pops one item** (lane F's VM-free / receipt rows): from the
`STC` row's input meta `mi = metaOf v` and the leaf's checks, the witnessed moving part is `v`'s, the
popped item is the head of `v`'s queue, and the tail digest is the tail's — or a collision. -/
theorem open_pop (v : StV) (mi : StateM5a.StHalfC.StMeta)
    (hmi : StateM5a.StHalfC.metaOf stViewParams_BI v = mi)
    (dS dQ dM dT a : Bytes) (x : StV × Option (List Bytes × List (Bytes × Option Bytes) × Nat))
    (h1 : dS.length = digestLen) (h2 : dQ.length = digestLen) (hT : dT.length = digestLen)
    (hr : bdigest (dS ++ (dQ ++ dM)) = mi.rest) (hm : bdigest (Ser.enc x) = dM)
    (hp : bdigest (dT ++ a) = dQ) :
    Sha384Coll ∨ (mi.tag = tagOf v ∧ dS = dStatic (restOfB v) ∧ x = restMove (restOfB v) ∧
      ∃ tl, pendQ v = a :: tl ∧ chainR id tl = dT) := by
  subst hmi
  rcases rest_open _ dS dQ dM h1 h2 hr with c | ⟨e1, e2, e3⟩
  · exact .inl c
  rcases move_open (restOfB v) x (by rw [hm, e3]; rfl) with c | ex
  · exact .inl c
  rcases queue_pop (pendQ (restOfB v).1) dT a hT (by rw [hp, e2]; rfl) with c | ⟨tl, hl, ht⟩
  · exact .inl c
  refine .inr ⟨rfl, e1, ex, tl, ?_, ht⟩
  rw [← pendQ_strip]; exact hl

end LaneE.RestI

#print axioms LaneE.RestI.stv_recon
#print axioms LaneE.RestI.restRecon
#print axioms LaneE.RestI.encRestI_bind
#print axioms LaneE.RestI.stD_binding_BI
#print axioms LaneE.RestI.encRestI_length
#print axioms LaneE.RestI.dStatic_bind
#print axioms LaneE.RestI.tagOf_restMove
#print axioms LaneE.RestI.tag_sound
#print axioms LaneE.RestI.finPos_of_tag
#print axioms LaneE.RestI.incoming_of_tag
#print axioms LaneE.RestI.done_of_tag
#print axioms LaneE.RestI.rest_open
#print axioms LaneE.RestI.static_open
#print axioms LaneE.RestI.keys_open
#print axioms LaneE.RestI.move_open
#print axioms LaneE.RestI.queue_pop
#print axioms LaneE.RestI.queue_empty
#print axioms LaneE.RestI.incoming_head
#print axioms LaneE.RestI.locals_head
#print axioms LaneE.RestI.txs_head
#print axioms LaneE.RestI.rest_close
#print axioms LaneE.RestI.open_pop
