
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
| `d_static` | `bdigest (Ser.enc (keys, erase trie))` — the chunk's key list and the trie's reveal shape (`restStatic`) | never (the trie is never modified; `κ I` is constant) | 0 (opened as 42 B, copied) |
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

/-- **The incremental remainder encoding.** -/
def encRestI (r : RestB) : Bytes :=
  bdigest (Ser.enc (restStatic r)) ++ (chainR id (pendQ r.1) ++ bdigest (Ser.enc (restMove r)))

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

/-- **`encRestI` is binding**: equal encodings give equal remainders, or a `bdigest` collision. -/
theorem encRestI_bind (a b : RestB) (h : encRestI a = encRestI b) : Sha384Coll ∨ a = b := by
  unfold encRestI at h
  obtain ⟨h1, h⟩ := List.append_inj h (by rw [bdigest_length, bdigest_length])
  obtain ⟨h2, h3⟩ := List.append_inj h (by rw [chainR_length, chainR_length])
  rcases coll_or_eq h1 with c | e1
  · exact .inl c
  rcases chainR_binding id (fun _ _ h => h) _ _ h2 with e2 | c
  · rcases coll_or_eq h3 with c | e3
    · exact .inl c
    exact .inr (restRecon a b (Ser.pf.inj e1) e2 (Ser.pf.inj e3))
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
  simp only [encRestI, List.length_append, bdigest_length, chainR_length]; omega

end LaneE.RestI

#print axioms LaneE.RestI.stv_recon
#print axioms LaneE.RestI.restRecon
#print axioms LaneE.RestI.encRestI_bind
#print axioms LaneE.RestI.stD_binding_BI
#print axioms LaneE.RestI.encRestI_length
