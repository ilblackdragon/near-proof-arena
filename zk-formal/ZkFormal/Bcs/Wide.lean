import ZkFormal.Bcs.Log
import ZkFormal.Collision

/-!
# ZkFormal.Bcs.Wide — wide digests, oracle-query encodings, binding and non-inversion

**Encodings** (all oracle inputs of the protocol; DESIGN.md §4, amended in
`docs/zk-formal/L2-NOTES.md`):

* wide hash `WH(m) = H(0x01 ‖ m) ‖ H(0x02 ‖ m)` (64 bytes; `whq m j` is the
  `j`-th half query), where every hashed message `m` starts with a tag byte:
  `INIT` (transcript start), `ABS` (absorb a round message), `NODE`
  (Merkle node), `LEAF` (Merkle leaf);
* query-phase chunk `H(0x03 ‖ d ‖ be4 j)`.

**Slots.** `slots x` lists the 64-byte digests that the query `x` *uses*
(children of a node, the previous state and the committed roots of an
absorb, the final state of a query chunk).  It is bounded:
`(slots x).length ≤ 256`.

**Deterministic facts proved here.**

* `wh_unique`: without a wide collision, a digest has at most one preimage
  in a well-formed log.
* `noInv_of`: if no entry of the log is an *inversion* (`InvBad`: the second
  of the two halves of some `WH(m)` is answered so that `WH(m)` equals a
  digest already used by an earlier query, or by this query), then every
  digest that a query uses and that the final log produces was already
  produced **before** that query (`NoInv`).  This is what makes the objects
  committed in a transcript well defined at the time of the query.
-/

set_option linter.unusedSimpArgs false

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-! ## Encodings -/

def tagInit : UInt8 := 0x10
def tagAbs : UInt8 := 0x11
def tagNode : UInt8 := 0x12
def tagLeaf : UInt8 := 0x13
def tagChunk : UInt8 := 0x03

/-- Half `j` (`j < 2`) of the wide hash of `m`. -/
def whq (m : Bytes) (j : Nat) : Bytes := (if j = 0 then (1 : UInt8) else 2) :: m

def whDec : Bytes → Option (Bytes × Nat)
  | b :: m => if b = 1 then some (m, 0) else if b = 2 then some (m, 1) else none
  | [] => none

theorem whDec_whq (m : Bytes) (j : Nat) (hj : j < 2) : whDec (whq m j) = some (m, j) := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · simp [whq, whDec]
  · simp [whq, whDec]

theorem whq_ne (m m' : Bytes) : whq m 0 ≠ whq m' 1 := by
  unfold whq; simp

theorem whq_inj {m m' : Bytes} {j j' : Nat} (hj : j < 2) (hj' : j' < 2) (h : whq m j = whq m' j') :
    m = m' ∧ j = j' := enc_inj (k := 2) (dec := whDec) (fun m j hj => whDec_whq m j hj) hj hj' h

/-- `u = WH(m)` according to the log. -/
def WHin (tbl : Table) (m u : Bytes) : Prop :=
  ∃ a b, tbl.lookup (whq m 0) = some a ∧ tbl.lookup (whq m 1) = some b ∧ u = a ++ b

/-- The wide hash as a query tree. -/
def wh (m : Bytes) : OracleComp hashSpec Bytes :=
  .query (whq m 0) fun a => .query (whq m 1) fun b => .pure (a ++ b)

theorem evalT_wh (tbl : Table) (m u : Bytes) : evalT tbl (wh m) = some u ↔ WHin tbl m u := by
  unfold wh WHin
  simp only [evalT]
  constructor
  · intro h
    cases ha : tbl.lookup (whq m 0) with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h; simp only at h
      cases hb : tbl.lookup (whq m 1) with
      | none => rw [hb] at h; cases h
      | some b => rw [hb] at h; simp only [Option.some.injEq] at h; exact ⟨a, b, rfl, rfl, h.symm⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [ha]; simp only; rw [hb]

theorem WHin.suffix {pre hist : Table} (hnd : ((pre ++ hist).map Prod.fst).Nodup) {m u : Bytes}
    (h : WHin hist m u) : WHin (pre ++ hist) m u := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact ⟨a, b, lookup_suffix hnd ha, lookup_suffix hnd hb, rfl⟩

theorem WHin.length {tbl : Table} (wf : TableWF tbl) {m u : Bytes} (h : WHin tbl m u) : u.length = 64 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  rw [List.length_append, wf.lookup_length ha, wf.lookup_length hb]

theorem WHin.mem_keys {tbl : Table} {m u : Bytes} (h : WHin tbl m u) (j : Nat) (hj : j < 2) :
    whq m j ∈ tbl.map Prod.fst := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact mem_keys_of_lookup ha
  · exact mem_keys_of_lookup hb

/-- **Binding.**  Without a wide collision, preimages are unique. -/
theorem wh_unique {tbl : Table} (wf : TableWF tbl) (hcol : ¬ WideCollision 2 whq tbl)
    {m m' u : Bytes} (h : WHin tbl m u) (h' : WHin tbl m' u) : m = m' := by
  classical
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  obtain ⟨a', b', ha', hb', e⟩ := h'
  have hl := (List.append_inj e (by rw [wf.lookup_length ha, wf.lookup_length ha']))
  obtain ⟨rfl, rfl⟩ := hl
  refine Classical.byContradiction fun hne => ?_
  apply hcol
  refine ⟨m, m', hne, fun j hj => ?_⟩
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact ⟨a, ha, ha'⟩
  · exact ⟨b, hb, hb'⟩

/-! ## Messages and slots -/

/-- `n` consecutive 64-byte pieces of `b`. -/
def chunks64 (b : Bytes) (n : Nat) : List Bytes :=
  (List.range n).map fun i => (b.drop (64 * i)).take 64

/-- Digests used by a hashed message. -/
def slotsMsg : Bytes → List Bytes
  | t :: rest =>
    if t = tagNode then chunks64 rest 3
    else if t = tagAbs then rest.take 64 :: chunks64 (rest.drop 65) (rest.getD 64 0).toNat
    else []
  | [] => []

/-- Digests used by an oracle query. -/
def slots : Bytes → List Bytes
  | b :: m => if b = 1 ∨ b = 2 then slotsMsg m else if b = tagChunk then [m.take 64] else []
  | [] => []

theorem slots_whq (m : Bytes) (j : Nat) : slots (whq m j) = slotsMsg m := by
  by_cases hj : j = 0 <;> simp [whq, slots, hj]

theorem slots_length_le (x : Bytes) : (slots x).length ≤ 256 := by
  unfold slots
  split
  · rename_i b m
    split
    · unfold slotsMsg
      split
      · rename_i t rest
        split
        · simp [chunks64]
        · split
          · simp only [chunks64, List.length_cons, List.length_map, List.length_range]
            have := (rest.getD 64 0).toNat_lt
            omega
          · simp
      · simp
    · split <;> simp
  · simp

/-- Absorb message: previous state `d`, committed roots, clear message. -/
def absMsg (d : Bytes) (roots : List Bytes) (clear : Bytes) : Bytes :=
  tagAbs :: (d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear)))

def parseAbs (rest : Bytes) : Bytes × List Bytes × Bytes :=
  (rest.take 64, chunks64 (rest.drop 65) (rest.getD 64 0).toNat,
    (rest.drop 65).drop (64 * (rest.getD 64 0).toNat))

def initMsg (ctx cb : Bytes) : Bytes := tagInit :: (ctx ++ cb)

def nodeMsg (l r : Bytes) : Bytes := tagNode :: (l ++ r)

def leafMsg (v : Bytes) : Bytes := tagLeaf :: v

/-- Query-phase chunk `j` of final state `d`. -/
def chunkQ (d : Bytes) (j : Nat) : Bytes := tagChunk :: (d ++ Bytes.beN 4 j)

def chunkDec : Bytes → Option (Bytes × Nat)
  | b :: rest => if b = tagChunk then some (rest.take 64, Bytes.beToNat (rest.drop 64)) else none
  | [] => none

theorem chunkDec_chunkQ (d : Bytes) (hd : d.length = 64) (j : Nat) (hj : j < 2 ^ 32) :
    chunkDec (chunkQ d j) = some (d, j) := by
  simp only [chunkQ, chunkDec, if_true, List.take_left' hd, List.drop_left' hd, Bytes.beToNat_beN]
  rw [Nat.mod_eq_of_lt (by simpa using hj)]

theorem slots_chunkQ (d : Bytes) (hd : d.length = 64) (j : Nat) : d ∈ slots (chunkQ d j) := by
  simp [chunkQ, slots, tagChunk, List.take_left' hd]

theorem chunks64_flatten : ∀ (roots : List Bytes) (c : Bytes), (∀ r ∈ roots, r.length = 64) →
    chunks64 (roots.flatten ++ c) roots.length = roots
  | [], _, _ => rfl
  | r :: rs, c, h => by
    have hr : r.length = 64 := h r List.mem_cons_self
    have ih := chunks64_flatten rs c (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    unfold chunks64 at ih ⊢
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.flatten_cons, List.append_assoc, Nat.mul_zero,
      List.drop_zero, List.take_left' hr]
    congr 1
    refine Eq.trans ?_ ih
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.mul_succ]
    rw [Nat.add_comm, ← List.drop_drop, List.drop_left' hr]

theorem flatten_length64 : ∀ (roots : List Bytes), (∀ r ∈ roots, r.length = 64) →
    roots.flatten.length = 64 * roots.length
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h r List.mem_cons_self, flatten_length64 rs (fun r' h' => h r' (List.mem_cons_of_mem _ h'))]
    omega

theorem parseAbs_absMsg (d : Bytes) (roots : List Bytes) (clear : Bytes) (hd : d.length = 64)
    (hr : ∀ r ∈ roots, r.length = 64) (hn : roots.length < 256) :
    parseAbs (d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))) = (d, roots, clear) := by
  have hn' : (roots.length.toUInt8).toNat = roots.length := by
    exact UInt8.toNat_ofNat_of_lt' hn
  have h64 : (d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))).getD 64 0 = roots.length.toUInt8 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hd]; simp
  have hdrop : (d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))).drop 65 = roots.flatten ++ clear := by
    rw [show 65 = 64 + 1 by rfl, ← List.drop_drop, List.drop_left' hd]; rfl
  have hflat := flatten_length64 roots hr
  simp only [parseAbs, h64, hn', hdrop, List.take_left' hd, chunks64_flatten roots clear hr,
    List.drop_left' hflat]

theorem slots_absMsg (d : Bytes) (roots : List Bytes) (clear : Bytes) (hd : d.length = 64)
    (hr : ∀ r ∈ roots, r.length = 64) (hn : roots.length < 256) (j : Nat) :
    d ∈ slots (whq (absMsg d roots clear) j) ∧ ∀ r ∈ roots, r ∈ slots (whq (absMsg d roots clear) j) := by
  have hp := parseAbs_absMsg d roots clear hd hr hn
  simp only [parseAbs, Prod.mk.injEq] at hp
  have hs : slots (whq (absMsg d roots clear) j) =
      (d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))).take 64 ::
        chunks64 ((d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))).drop 65)
          ((d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear))).getD 64 0).toNat := by
    rw [slots_whq]; simp [absMsg, slotsMsg, tagAbs, tagNode]
  rw [hs, hp.1, hp.2.1]
  exact ⟨List.mem_cons_self, fun r hrm => List.mem_cons_of_mem _ hrm⟩

theorem slots_nodeMsg (l r : Bytes) (hl : l.length = 64) (j : Nat) :
    l ∈ slots (whq (nodeMsg l r) j) ∧ (r.length = 64 → r ∈ slots (whq (nodeMsg l r) j)) := by
  rw [slots_whq]
  simp only [nodeMsg, slotsMsg, tagNode, if_true, chunks64]
  refine ⟨?_, fun hr => ?_⟩
  · simp only [List.range_succ, List.range_zero]
    simp [List.take_left' hl]
  · simp only [List.range_succ, List.range_zero]
    simp [List.drop_left' hl, List.take_of_length_le (by omega : r.length ≤ 64)]

/-! ## Inversion events -/

/-- The digest assembled from half `j`'s answer `y` and the other half's `y'`. -/
def mkWide (j : Nat) (y y' : Bytes) : Bytes := if j = 0 then y ++ y' else y' ++ y

/-- **Inversion.**  The fresh answer `y` to `x = whq m j`, completing `WH(m)`
(the other half being already recorded), makes `WH(m)` equal to a digest
used by an earlier query or by `x` itself. -/
def InvBad (hist : Table) (x y : Bytes) : Prop :=
  ∃ m j y' u, j < 2 ∧ x = whq m j ∧ hist.lookup (whq m (1 - j)) = some y' ∧
    (u ∈ slots x ∨ ∃ e ∈ hist, u ∈ slots e.1) ∧ u = mkWide j y y'

/-- Deterministic consequence of "no inversion": a digest used by a query
and produced by the final log was produced before that query. -/
def NoInv (tbl : Table) : Prop :=
  ∀ pre x y hist, tbl = pre ++ (x, y) :: hist → ∀ u ∈ slots x, ∀ m, WHin tbl m u → WHin hist m u

theorem first_split {α : Type} (P : α → Prop) :
    ∀ (l : List α), (∃ a ∈ l, P a) → ∃ l1 a l2, l = l1 ++ a :: l2 ∧ P a ∧ ∀ b ∈ l1, ¬ P b
  | [], ⟨_, h, _⟩ => by simp at h
  | a :: l, ⟨b, hb, hPb⟩ => by
    classical
    by_cases ha : P a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd hPb ha
      · obtain ⟨l1, c, l2, e, hc, hl1⟩ := first_split P l ⟨b, hb, hPb⟩
        refine ⟨a :: l1, c, l2, by rw [e]; rfl, hc, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ha
        · exact hl1 d hd

/-- **No inversion ⇒ produced-before-use.** -/
theorem noInv_of {tbl : Table} (wf : TableWF tbl) (hno : ¬ BadHist InvBad tbl) : NoInv tbl := by
  classical
  intro pre x y hist hsplit u hu m hm
  obtain ⟨a, b, ha, hb, rfl⟩ := hm
  -- the newest of the two half queries
  obtain ⟨l1, ⟨z, yz⟩, l2, e, hz, hl1⟩ := first_split (fun e : Bytes × Bytes => e.1 = whq m 0 ∨ e.1 = whq m 1)
    tbl ⟨(whq m 0, a), lookup_mem_pair ha, Or.inl rfl⟩
  have hnd : ((l1 ++ (z, yz) :: l2).map Prod.fst).Nodup := e ▸ wf.1
  have hyz : tbl.lookup z = some yz := by rw [e]; exact lookup_split hnd
  -- the other half lies in `l2`
  have other : ∀ j, j < 2 → z = whq m j → ∃ y', l2.lookup (whq m (1 - j)) = some y' ∧
      tbl.lookup (whq m (1 - j)) = some y' := by
    intro j hj hzj
    have hk : whq m (1 - j) ∈ tbl.map Prod.fst := by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact mem_keys_of_lookup hb
      · exact mem_keys_of_lookup ha
    have hne : whq m (1 - j) ≠ z := by
      rw [hzj]; intro h; have := (whq_inj (by omega) hj h).2; omega
    have hk2 : whq m (1 - j) ∈ l2.map Prod.fst := by
      rw [e] at hk
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hk
      rcases hk with hk | hk | hk
      · exfalso
        obtain ⟨⟨k, v⟩, hkv, hk'⟩ := List.mem_map.mp hk
        simp only at hk'
        apply hl1 _ hkv
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · exact Or.inr hk'
        · exact Or.inl hk'
      · exact absurd hk hne
      · exact hk
    obtain ⟨y', hy'⟩ := lookup_of_mem_keys hk2
    refine ⟨y', hy', ?_⟩
    rw [e, show l1 ++ (z, yz) :: l2 = (l1 ++ [(z, yz)]) ++ l2 by simp]
    exact lookup_suffix (by simpa using hnd) hy'
  -- if the newest half is `x` or newer than `x`, the log contains an inversion
  have bad : (z = x ∨ ∃ e ∈ l2, (a ++ b) ∈ slots e.1) → False := by
    intro hpos
    apply hno
    rw [e]
    apply badHist_of_split
    have hj : ∃ j, j < 2 ∧ z = whq m j := by
      rcases hz with hz | hz
      · exact ⟨0, by omega, hz⟩
      · exact ⟨1, by omega, hz⟩
    obtain ⟨j, hj2, hzj⟩ := hj
    obtain ⟨y', hl2, htb⟩ := other j hj2 hzj
    refine ⟨m, j, y', a ++ b, hj2, hzj, hl2, ?_, ?_⟩
    · rcases hpos with rfl | h
      · exact Or.inl hu
      · exact Or.inr h
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [← hzj] at ha; rw [hyz] at ha; cases ha
        simp only [Nat.sub_zero] at htb; rw [hb] at htb; cases htb
        simp [mkWide]
      · rw [← hzj] at hb; rw [hyz] at hb; cases hb
        simp only [show 1 - 1 = 0 by rfl] at htb; rw [ha] at htb; cases htb
        simp [mkWide]
  -- compare the two splits of the log
  rw [hsplit] at e
  rcases List.append_eq_append_iff.mp e with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h2
      exact bad (Or.inl h2.1.1.symm)
    | cons c as' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      -- both halves are recorded in `hist`
      have hnd' : (((pre ++ [(x, y)]) ++ hist).map Prod.fst).Nodup := by
        have := wf.1; rw [hsplit] at this; simpa using this
      have htb : tbl = (pre ++ [(x, y)]) ++ hist := by rw [hsplit]; simp
      have hzh : z ∈ hist.map Prod.fst := by rw [h2.2]; simp
      have hz2 : ∀ k, k ∈ l2.map Prod.fst → k ∈ hist.map Prod.fst := by
        intro k hk; rw [h2.2]; simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inr hk)
      have hkeys : whq m 0 ∈ hist.map Prod.fst ∧ whq m 1 ∈ hist.map Prod.fst := by
        rcases hz with hz | hz
        · obtain ⟨y', hy', _⟩ := other 0 (by omega) hz
          exact ⟨hz ▸ hzh, hz2 _ (mem_keys_of_lookup hy')⟩
        · obtain ⟨y', hy', _⟩ := other 1 (by omega) hz
          exact ⟨hz2 _ (mem_keys_of_lookup hy'), hz ▸ hzh⟩
      rw [htb] at ha hb
      exact ⟨a, b, lookup_suffix' hnd' ha hkeys.1, lookup_suffix' hnd' hb hkeys.2, rfl⟩
  · exfalso
    cases bs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h2
      exact bad (Or.inl h2.1.1)
    | cons c bs' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      exact bad (Or.inr ⟨(x, y), by rw [h2.2]; simp, hu⟩)

end ZkFormal.Bcs
