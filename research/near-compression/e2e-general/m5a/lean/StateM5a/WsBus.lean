import StateM5a.WsCost
import StateM5a.Merkle
import StateM5a.Traffic

/-!
# StateM5a.WsBus — the M5a-3 working-set segment at the bus level (record level)

Decoded messages of the working-set tables (`Ws.lean`) on the three buses of a segment's update,
and the bus-level assembly of the per-row facts (`WsCost`) into the two segment statements:

* **`WM` (offline memory checking).**  A `WSL` row (one per touched entry `(seg, kd)`) sends
  `WM(seg, kd, cur, 0)` and receives `WM(seg, kd, ncur, idl)`; a `WSA` row (one write access at
  time `t`) receives `WM(seg, kd, old, idp)` and sends `WM(seg, kd, new, t)`.  From balance, the
  per-row gap `idp < t` (`WsCost.wsa_gap`) and distinct `(seg, kd)` among the `WSL` rows:
  - `wm_orphan`: every access belongs to the chain of some `WSL` row (no write can bypass the tree);
  - `wm_chain`: for every `WSL` row, its entry's accesses sorted by time (latest first) have
    strictly decreasing times, each read the value written just before it (the opening value for
    the first), and the row closes with the latest written value — exactly the premise and the
    conclusion of `WsCost.chain_sound_any`.
* **`PT` / `RCH` (the batched path update).**  A `WSL` row sends `PT(seg, 0, i, dgO, dgN)`; an
  active `WSP` row at `(seg, lvl, idx)` receives `PT(seg, lvl, 2idx, lo, ln)` (if `tl`) and
  `PT(seg, lvl, 2idx+1, ro, rn)` (if `tr`) and sends `PT(seg, lvl+1, idx, oo, on)` (if not
  `top`); the top row (`lvl + 1 = D`, `idx = 0`) receives `RCH(seg, oo)` and sends
  `RCH(seg+1, on)`.  From balance and the row facts (`WspOK`: untouched child kept, `oo = H lo ro`,
  `on = H ln rn`):
  - `rch_tops`: at most one top row per segment (and `rch_link`: the segment chain);
  - `pt_rows_le_one`, `pt_sends_le_one`, `wsl_unique`: one row per node position (a counting argument as
    `Traffic.walk_unique`: open `PT` messages above level `D` cannot be absorbed, and every row at
    `(L, j)` is absorbed by the unique row at `(L+1, j/2)`);
  - `seg_update`: the top row's digests are the old / new digest of an `Upd` description that
    fits depth `D`, whose touched leaves are exactly the segment's `WSL` rows at their indices
    (`LeavesIn`, and `Has` for every row, with `i < 2^D`);
  - `seg_root`: with that, `Merkle.batch_update_sound` (no collision of `H`, a named hypothesis):
    if `RCH(seg)` is the root of the working set `ws`, every `WSL` row's old leaf is `ws`'s leaf at
    its index (`Agrees`) and `RCH(seg+1)` is the root of `ws` with the touched leaves replaced;
  - `seg_root_leaves`: the same without `Upd`: `RCH(seg+1) = root ws'` where, index by index, `ws'`
    holds the `WSL` row's new digest at a touched index (whose old digest is `ws`'s leaf) and
    `ws`'s leaf elsewhere.

Per-row facts are premises (their field-level derivations are `WsCost.wsa_gap`, `wsp_keep`,
`wsp_off`, and the `IF384` contract in `Sha512If` for the hashes).
-/

namespace StateM5a.WsBus

open StateM5a.WsCost (Acc lastVal lastT Reads chain_sound_any)
open StateM5a.Merkle (Upd root batch_update_sound)

/-! ## Generic list helpers -/

theorem filter_key_single {β κ : Type} [DecidableEq κ] (f : β → κ) :
    ∀ {L : List β} {x : β}, (L.map f).Nodup → x ∈ L → L.filter (fun y => decide (f y = f x)) = [x]
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: ys, x, hn, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hx with rfl | hx'
    · have : ys.filter (fun y' => decide (f y' = f x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha h
        exact hn.1 (List.mem_map.2 ⟨a, ha, by simpa using h⟩)
      simp only [List.filter_cons, decide_true, ↓reduceIte, this]
    · have hne : f y ≠ f x := fun e => hn.1 (e ▸ List.mem_map.2 ⟨x, hx', rfl⟩)
      simp only [List.filter_cons, hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_single f hn.2 hx'

theorem exists_max {β : Type} (g : β → Nat) :
    ∀ {L : List β} {x : β}, x ∈ L → ∃ y ∈ L, ∀ z ∈ L, g z ≤ g y
  | [], _, hx => absurd hx List.not_mem_nil
  | y :: ys, _, _ => by
    cases ys with
    | nil => exact ⟨y, by simp, fun z hz => by simp at hz; subst hz; exact Nat.le_refl _⟩
    | cons y' ys' =>
      obtain ⟨m, hm, hmax⟩ := exists_max g (L := y' :: ys') (List.mem_cons_self ..)
      by_cases h : g y ≤ g m
      · refine ⟨m, List.mem_cons_of_mem _ hm, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact hmax z hz
      · refine ⟨y, List.mem_cons_self .., fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact Nat.le_refl _
        · have := hmax z hz; omega

theorem countP_add_le {β : Type} {p q r : β → Bool} :
    ∀ {l : List β}, (∀ x ∈ l, (p x).toNat + (q x).toNat ≤ (r x).toNat) →
      l.countP p + l.countP q ≤ l.countP r
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    simp only [List.countP_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := countP_add_le (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p x <;> cases hq : q x <;> cases hr : r x <;> simp_all <;> omega

/-! ## Records -/

/-- A decoded `WM` message `(seg, kd, value, id)` (`value` = `(cp, cl, cv16, wr)`). -/
structure WM (Kd V : Type) where
  seg : Nat
  kd : Kd
  val : V
  id : Nat

/-- An active `WSA` row: the access at time `t` of segment `seg` to entry `kd`. -/
structure WsaRow (Kd V : Type) where
  seg : Nat
  t : Nat
  kd : Kd
  old : V
  idp : Nat
  new : V

/-- An active `WSL` row: touched leaf `i` of segment `seg`, entry `kd`; it opens the entry's chain
with `cur`, closes it with `ncur` at `idl`; `dgO` / `dgN` are the old / new leaf digests. -/
structure WslRow (Kd V α : Type) where
  seg : Nat
  i : Nat
  kd : Kd
  cur : V
  ncur : V
  idl : Nat
  dgO : α
  dgN : α

/-- A decoded `PT` message `(seg, lvl, idx, old, new)`. -/
structure PT (α : Type) where
  seg : Nat
  lvl : Nat
  idx : Nat
  o : α
  n : α

/-- An active `WSP` row (inactive rows have no multiplicity: `WsCost.wsp_off`). -/
structure WspRow (α : Type) where
  seg : Nat
  lvl : Nat
  idx : Nat
  top : Bool
  tl : Bool
  tr : Bool
  lo : α
  ln : α
  ro : α
  rn : α
  oo : α
  on : α

section WMBus
variable {Kd V α : Type} [DecidableEq Kd]

def WM.key (m : WM Kd V) : Nat × Kd := (m.seg, m.kd)
def WM.vi (m : WM Kd V) : V × Nat := (m.val, m.id)
def WsaRow.key (a : WsaRow Kd V) : Nat × Kd := (a.seg, a.kd)
def WsaRow.rcvM (a : WsaRow Kd V) : WM Kd V := ⟨a.seg, a.kd, a.old, a.idp⟩
def WsaRow.sndM (a : WsaRow Kd V) : WM Kd V := ⟨a.seg, a.kd, a.new, a.t⟩
def WsaRow.acc (a : WsaRow Kd V) : Acc V := ⟨a.t, a.idp, a.old, a.new⟩
def WslRow.key (l : WslRow Kd V α) : Nat × Kd := (l.seg, l.kd)
def WslRow.openM (l : WslRow Kd V α) : WM Kd V := ⟨l.seg, l.kd, l.cur, 0⟩
def WslRow.closeM (l : WslRow Kd V α) : WM Kd V := ⟨l.seg, l.kd, l.ncur, l.idl⟩

/-- `WM` sends: the `WSL` openings and the `WSA` written values. -/
def wmSends (wsl : List (WslRow Kd V α)) (wsa : List (WsaRow Kd V)) : List (WM Kd V) :=
  wsl.map WslRow.openM ++ wsa.map WsaRow.sndM

/-- `WM` receives: the `WSL` closings and the `WSA` reads. -/
def wmRecvs (wsl : List (WslRow Kd V α)) (wsa : List (WsaRow Kd V)) : List (WM Kd V) :=
  wsl.map WslRow.closeM ++ wsa.map WsaRow.rcvM

/-- The accesses of entry `k = (seg, kd)`. -/
def accOf (wsa : List (WsaRow Kd V)) (k : Nat × Kd) : List (Acc V) :=
  (wsa.filter fun a => decide (a.key = k)).map WsaRow.acc

theorem wm_filter (wsl : List (WslRow Kd V α)) (wsa : List (WsaRow Kd V)) (k : Nat × Kd) :
    ((wmSends wsl wsa).filter fun m => decide (m.key = k)) =
      (wsl.filter fun l => decide (l.key = k)).map WslRow.openM ++
        (wsa.filter fun a => decide (a.key = k)).map WsaRow.sndM ∧
    ((wmRecvs wsl wsa).filter fun m => decide (m.key = k)) =
      (wsl.filter fun l => decide (l.key = k)).map WslRow.closeM ++
        (wsa.filter fun a => decide (a.key = k)).map WsaRow.rcvM := by
  simp only [wmSends, wmRecvs, List.filter_append, List.filter_map]
  exact ⟨rfl, rfl⟩

/-- **No orphan write**: every write access belongs to the chain of a touched leaf of its
segment (an entry without a `WSL` row would leave its latest write unabsorbed). -/
theorem wm_orphan {wsl : List (WslRow Kd V α)} {wsa : List (WsaRow Kd V)}
    (hbal : (wmSends wsl wsa).Perm (wmRecvs wsl wsa)) (hgap : ∀ a ∈ wsa, a.idp < a.t) :
    ∀ a ∈ wsa, ∃ l ∈ wsl, l.key = a.key := by
  intro a ha
  refine Classical.byContradiction fun hno => ?_
  have hnil : (wsl.filter fun l => decide (l.key = a.key)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro l hl h
    exact hno ⟨l, hl, by simpa using h⟩
  have hf := hbal.filter (fun m => decide (m.key = a.key))
  obtain ⟨e1, e2⟩ := wm_filter wsl wsa a.key
  rw [e1, e2, hnil] at hf
  simp only [List.map_nil, List.nil_append] at hf
  let F := wsa.filter fun b => decide (b.key = a.key)
  have haF : a ∈ F := List.mem_filter.2 ⟨ha, by simp⟩
  obtain ⟨b, hbF, hmax⟩ := exists_max (fun b : WsaRow Kd V => b.t) haF
  have hm : b.sndM ∈ F.map WsaRow.rcvM := hf.subset (List.mem_map.2 ⟨b, hbF, rfl⟩)
  obtain ⟨c, hcF, hc⟩ := List.mem_map.1 hm
  simp only [WsaRow.rcvM, WsaRow.sndM, WM.mk.injEq] at hc
  have h1 := hgap c (List.mem_filter.1 hcF).1
  have h2 := hmax c hcF
  omega

/-- **The entry's memory chain from `WM` balance.**  For a touched leaf `l` (distinct `(seg, kd)`
among the `WSL` rows), the accesses of its entry, sorted latest first, have strictly decreasing
times, each read its predecessor's value (`Reads`, from `l.cur` at time `0`), and `l` closes with
the latest written value at the latest time. -/
theorem wm_chain {wsl : List (WslRow Kd V α)} {wsa : List (WsaRow Kd V)}
    (hbal : (wmSends wsl wsa).Perm (wmRecvs wsl wsa)) (hgap : ∀ a ∈ wsa, a.idp < a.t)
    (hdist : (wsl.map WslRow.key).Nodup) {l : WslRow Kd V α} (hl : l ∈ wsl) :
    ∃ s : List (Acc V), s.Perm (accOf wsa l.key) ∧ s.Pairwise (fun a b => b.t < a.t) ∧
      l.ncur = lastVal l.cur s ∧ l.idl = lastT s ∧ Reads l.cur s := by
  have hf := (hbal.filter (fun m => decide (m.key = l.key))).map WM.vi
  obtain ⟨e1, e2⟩ := wm_filter wsl wsa l.key
  rw [e1, e2, filter_key_single WslRow.key hdist hl] at hf
  have hp : List.Perm ((l.cur, 0) :: (accOf wsa l.key).map Acc.snd)
      ((l.ncur, l.idl) :: (accOf wsa l.key).map Acc.rcv) := by
    simpa [accOf, List.map_map, Function.comp_def, WM.vi, WslRow.openM, WslRow.closeM,
      WsaRow.sndM, WsaRow.rcvM, WsaRow.acc, Acc.snd, Acc.rcv] using hf
  refine chain_sound_any l.cur (accOf wsa l.key) l.ncur l.idl ?_ hp
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact hgap a (List.mem_filter.1 ha).1

end WMBus

/-! ## `RCH`: one top row per segment -/

section RCH
variable {α : Type}

def topsOf (wsp : List (WspRow α)) : List (WspRow α) := wsp.filter (·.top)

/-- `RCH` sends: `WSN`'s INTAKE root `(0, r0)` and each top row's `(seg + 1, on)`. -/
def rchSends (r0 : α) (wsp : List (WspRow α)) : List (Nat × α) :=
  (0, r0) :: (topsOf wsp).map fun r => (r.seg + 1, r.on)

/-- `RCH` receives: `WSN`'s FINAL root `(nw, rF)` and each top row's `(seg, oo)`. -/
def rchRecvs (nw : Nat) (rF : α) (wsp : List (WspRow α)) : List (Nat × α) :=
  (nw, rF) :: (topsOf wsp).map fun r => (r.seg, r.oo)

/-- **One top row per segment.** -/
theorem rch_tops {r0 rF : α} {nw : Nat} {wsp : List (WspRow α)}
    (h : (rchSends r0 wsp).Perm (rchRecvs nw rF wsp)) :
    ∀ s, (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ 1 := by
  have hc : ∀ s, (rchSends r0 wsp).countP (fun m => decide (m.1 = s)) =
      (rchRecvs nw rF wsp).countP (fun m => decide (m.1 = s)) := fun s => h.countP_eq _
  simp only [rchSends, rchRecvs, List.countP_cons, List.countP_map, Function.comp_def] at hc
  intro s
  induction s with
  | zero =>
    have := hc 0
    have hz : (topsOf wsp).countP (fun r => decide (r.seg + 1 = 0)) = 0 :=
      List.countP_eq_zero.2 (by simp)
    rw [hz] at this
    simp only [decide_true, ↓reduceIte] at this
    split at this <;> omega
  | succ s ih =>
    have := hc (s + 1)
    have he : (topsOf wsp).countP (fun r => decide (r.seg + 1 = s + 1)) =
        (topsOf wsp).countP (fun r => decide (r.seg = s)) :=
      List.countP_congr (fun r _ => by simp)
    rw [he] at this
    simp only [show (0 = s + 1) = False from by simp, decide_false, Bool.false_eq_true,
      ↓reduceIte] at this
    split at this <;> omega

/-- **The segment chain**: the top row of segment `0` takes `r0`; the top row of segment `s + 1`
takes what a top row of segment `s` sent; `rF` is what the top row of segment `nw − 1` sent (or
`r0` when `nw = 0`). -/
theorem rch_link {r0 rF : α} {nw : Nat} {wsp : List (WspRow α)}
    (h : (rchSends r0 wsp).Perm (rchRecvs nw rF wsp)) :
    (∀ r ∈ topsOf wsp, r.seg = 0 → r.oo = r0) ∧
    (∀ r ∈ topsOf wsp, ∀ s, r.seg = s + 1 → ∃ q ∈ topsOf wsp, q.seg = s ∧ q.on = r.oo) ∧
    ((nw = 0 ∧ rF = r0) ∨ ∃ q ∈ topsOf wsp, q.seg + 1 = nw ∧ q.on = rF) := by
  have hm : ∀ x, x ∈ rchRecvs nw rF wsp → x ∈ rchSends r0 wsp := fun x hx => h.mem_iff.2 hx
  refine ⟨fun r hr h0 => ?_, fun r hr s hs => ?_, ?_⟩
  · have := hm (r.seg, r.oo) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨r, hr, rfl⟩))
    simp only [rchSends, List.mem_cons, List.mem_map, Prod.mk.injEq] at this
    rcases this with ⟨-, e⟩ | ⟨q, -, e, -⟩
    · exact e
    · omega
  · have := hm (r.seg, r.oo) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨r, hr, rfl⟩))
    simp only [rchSends, List.mem_cons, List.mem_map, Prod.mk.injEq] at this
    rcases this with ⟨e, -⟩ | ⟨q, hq, e1, e2⟩
    · omega
    · exact ⟨q, hq, by omega, e2⟩
  · have := hm (nw, rF) (List.mem_cons_self ..)
    simp only [rchSends, List.mem_cons, List.mem_map, Prod.mk.injEq] at this
    rcases this with ⟨e1, e2⟩ | ⟨q, hq, e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨q, hq, e1, e2⟩

end RCH

/-! ## `PT`: one row per node position -/

section PTBus
variable {Kd V α : Type}

def WspRow.inL (r : WspRow α) : PT α := ⟨r.seg, r.lvl, 2 * r.idx, r.lo, r.ln⟩
def WspRow.inR (r : WspRow α) : PT α := ⟨r.seg, r.lvl, 2 * r.idx + 1, r.ro, r.rn⟩
def WspRow.outM (r : WspRow α) : PT α := ⟨r.seg, r.lvl + 1, r.idx, r.oo, r.on⟩
def WslRow.ptM (l : WslRow Kd V α) : PT α := ⟨l.seg, 0, l.i, l.dgO, l.dgN⟩

/-- `PT` sends: each touched leaf at level `0`, each non-top path node to its parent. -/
def ptSends (wsl : List (WslRow Kd V α)) (wsp : List (WspRow α)) : List (PT α) :=
  wsl.map WslRow.ptM ++ (wsp.filter fun r => !r.top).map WspRow.outM

/-- `PT` receives: each path node's touched children. -/
def ptRecvs (wsp : List (WspRow α)) : List (PT α) :=
  (wsp.filter (·.tl)).map WspRow.inL ++ (wsp.filter (·.tr)).map WspRow.inR

/-- The row facts of an active `WSP` row (`WsCost.wsp_keep`, the top row's position, and the two
compressions: `Sha512If.comp_node`). -/
structure WspOK (H : α → α → α) (D : Nat) (r : WspRow α) : Prop where
  keepL : r.tl = false → r.lo = r.ln
  keepR : r.tr = false → r.ro = r.rn
  hO : r.oo = H r.lo r.ro
  hN : r.on = H r.ln r.rn
  topLvl : r.top = true → r.lvl + 1 = D
  topIdx : r.top = true → r.idx = 0

variable (wsl : List (WslRow Kd V α)) (wsp : List (WspRow α)) (s : Nat)

def atP (L j : Nat) (m : PT α) : Bool := decide (m.seg = s ∧ m.lvl = L ∧ m.idx = j)

/-- `PT` messages sent at `(s, L, j)`. -/
def sendsAt (L j : Nat) : Nat := (ptSends wsl wsp).countP (atP s L j)

/-- `WSP` rows of segment `s` whose node is at `(L, j)` (children at level `L − 1`). -/
def rowsAt (L j : Nat) : Nat := wsp.countP fun r => decide (r.seg = s ∧ r.lvl + 1 = L ∧ r.idx = j)

def topsAt (L j : Nat) : Nat :=
  wsp.countP fun r => decide (r.top = true ∧ r.seg = s ∧ r.lvl + 1 = L ∧ r.idx = j)

/-- A bound on the rows' node levels. -/
def lvlBound : Nat := wsp.foldr (fun r acc => max (r.lvl + 1) acc) 0

variable {wsl wsp s}

theorem le_lvlBound : ∀ {wsp : List (WspRow α)} {r}, r ∈ wsp → r.lvl + 1 ≤ lvlBound wsp
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, r, h => by
    simp only [lvlBound, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := le_lvlBound h'; simp only [lvlBound] at this; omega

theorem rows_eq (L j : Nat) (hL : 1 ≤ L) :
    rowsAt wsp s L j = sendsAt wsl wsp s L j + topsAt wsp s L j := by
  have h0 : (wsl.map WslRow.ptM).countP (atP s L j) = 0 := by
    rw [List.countP_eq_zero]; intro m hm
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hm
    intro h; unfold atP at h; simp [WslRow.ptM] at h; have := of_decide_eq_true h; omega
  simp only [sendsAt, ptSends, List.countP_append, h0, Nat.zero_add, List.countP_map,
    List.countP_filter, rowsAt, topsAt]
  apply Eq.symm
  have := Traffic.countP_add_congr (l := wsp)
    (p := fun r => (atP s L j ∘ WspRow.outM) r && !r.top)
    (q := fun r => decide (r.top = true ∧ r.seg = s ∧ r.lvl + 1 = L ∧ r.idx = j))
    (p' := fun r => decide (r.seg = s ∧ r.lvl + 1 = L ∧ r.idx = j)) (q' := fun _ => false)
    (fun r _ => by
      cases ht : r.top <;> by_cases h : r.seg = s ∧ r.lvl + 1 = L ∧ r.idx = j <;>
        simp [atP, WspRow.outM, h] <;> omega)
  have hz : wsp.countP (fun _ => false) = 0 := List.countP_eq_zero.2 (by simp)
  omega

theorem sends_eq_recvs (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (L j : Nat) :
    sendsAt wsl wsp s L j = (ptRecvs wsp).countP (atP s L j) := hbal.countP_eq _

theorem sends_le_rows (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (L j : Nat) :
    sendsAt wsl wsp s L j ≤ rowsAt wsp s (L + 1) (j / 2) := by
  rw [sends_eq_recvs hbal]
  simp only [ptRecvs, List.countP_append, List.countP_map, List.countP_filter, rowsAt]
  apply countP_add_le
  intro r _
  have e1 : (atP s L j ∘ WspRow.inL) r = decide (r.seg = s ∧ r.lvl = L ∧ 2 * r.idx = j) := rfl
  have e2 : (atP s L j ∘ WspRow.inR) r = decide (r.seg = s ∧ r.lvl = L ∧ 2 * r.idx + 1 = j) := rfl
  rw [e1, e2]
  by_cases h : r.seg = s ∧ r.lvl = L ∧ 2 * r.idx = j
  · have h' : ¬(r.seg = s ∧ r.lvl = L ∧ 2 * r.idx + 1 = j) := by omega
    have h'' : r.seg = s ∧ r.lvl + 1 = L + 1 ∧ r.idx = j / 2 := by omega
    simp only [decide_eq_true h, decide_eq_false h', decide_eq_true h'']
    cases r.tl <;> simp
  · by_cases hh : r.seg = s ∧ r.lvl = L ∧ 2 * r.idx + 1 = j
    · have h'' : r.seg = s ∧ r.lvl + 1 = L + 1 ∧ r.idx = j / 2 := by omega
      simp only [decide_eq_false h, decide_eq_true hh, decide_eq_true h'']
      cases r.tr <;> simp
    · simp [decide_eq_false h, decide_eq_false hh]

theorem tops_zero {D : Nat} (hok : ∀ r ∈ wsp, ∃ H, WspOK (α := α) H D r) (L j : Nat) (hL : L ≠ D) :
    topsAt wsp s L j = 0 := by
  rw [topsAt, List.countP_eq_zero]
  intro r hr h
  obtain ⟨H, hk⟩ := hok r hr
  simp only [decide_eq_true_eq] at h
  exact hL (h.2.2.1 ▸ hk.topLvl h.1)

theorem tops_le (htop : (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ 1) (L j : Nat) :
    topsAt wsp s L j ≤ 1 := by
  refine Nat.le_trans ?_ htop
  rw [topsOf, List.countP_filter]
  apply List.countP_mono_left
  intro r _ h
  simp only [decide_eq_true_eq] at h
  simp [h.1, h.2.1]

theorem rows_zero (L j : Nat) (hL : lvlBound wsp < L) : rowsAt wsp s L j = 0 := by
  rw [rowsAt, List.countP_eq_zero]
  intro r hr h
  have := le_lvlBound hr
  simp only [decide_eq_true_eq] at h
  omega

section Count
variable {D : Nat} (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp))
  (hok : ∀ r ∈ wsp, ∃ H, WspOK (α := α) H D r)
  (htop : (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ 1)
include hbal hok

/-- No `PT` message at or above the root level `D` (it could never be absorbed). -/
theorem sends_high : ∀ n L j, lvlBound wsp < L + n → D ≤ L → sendsAt wsl wsp s L j = 0
  | 0, L, j, hb, _ => by
    have h1 : 1 ≤ L := by omega
    have := rows_eq (wsl := wsl) (wsp := wsp) (s := s) L j h1
    have := rows_zero (wsp := wsp) (s := s) L j (by omega)
    omega
  | n + 1, L, j, hb, hD => by
    have h1 := sends_le_rows (s := s) hbal L j
    have h2 := rows_eq (wsl := wsl) (wsp := wsp) (s := s) (L + 1) (j / 2) (by omega)
    have h3 := sends_high n (L + 1) (j / 2) (by omega) (by omega)
    have h4 := tops_zero (s := s) hok (L + 1) (j / 2) (by omega)
    omega

theorem send_lt {m : PT α} (hm : m ∈ ptSends wsl wsp) : m.lvl < D := by
  refine Nat.lt_of_not_le fun hD => ?_
  have h0 := sends_high (s := m.seg) hbal hok (lvlBound wsp + 1) m.lvl m.idx (by omega) hD
  have : 0 < sendsAt wsl wsp m.seg m.lvl m.idx :=
    List.countP_pos_iff.2 ⟨m, hm, by simp [atP]⟩
  omega

include htop

theorem sends_low : ∀ n L j, L + n = D → sendsAt wsl wsp s L j + topsAt wsp s L j ≤ 1
  | 0, L, j, hL => by
    have := sends_high (s := s) (j := j) hbal hok (lvlBound wsp + 1) L (by omega) (by omega)
    have := tops_le (s := s) htop L j
    omega
  | n + 1, L, j, hL => by
    have h1 := sends_le_rows (s := s) hbal L j
    have h2 := rows_eq (wsl := wsl) (wsp := wsp) (s := s) (L + 1) (j / 2) (by omega)
    have h3 := sends_low n (L + 1) (j / 2) (by omega)
    have h4 := tops_zero (s := s) hok L j (by omega)
    omega

/-- **One `WSP` row per node position** (segment `s`). -/
theorem pt_rows_le_one (L j : Nat) : rowsAt wsp s (L + 1) j ≤ 1 := by
  have h2 := rows_eq (wsl := wsl) (wsp := wsp) (s := s) (L + 1) j (by omega)
  by_cases hD : L + 1 ≤ D
  · have := sends_low hbal hok htop (D - (L + 1)) (L + 1) j (by omega)
    omega
  · have := sends_high (s := s) (j := j) hbal hok (lvlBound wsp + 1) (L + 1) (by omega) (by omega)
    have := tops_zero (s := s) hok (L + 1) j (by omega)
    omega

/-- **One `PT` message per position** (segment `s`). -/
theorem pt_sends_le_one (L j : Nat) : sendsAt wsl wsp s L j ≤ 1 :=
  Nat.le_trans (sends_le_rows hbal L j) (pt_rows_le_one hbal hok htop L (j / 2))

theorem row_unique {r r' : WspRow α} (hr : r ∈ wsp) (hr' : r' ∈ wsp) (hs : r.seg = s)
    (hs' : r'.seg = s) (hl : r.lvl = r'.lvl) (hi : r.idx = r'.idx) : r = r' :=
  Traffic.countP_le_one (pt_rows_le_one hbal hok htop r.lvl r.idx) hr hr'
    (by simp [hs]) (by simp [hs', hl, hi])

theorem send_unique {m m' : PT α} (hm : m ∈ ptSends wsl wsp) (hm' : m' ∈ ptSends wsl wsp)
    (hs : m.seg = s) (hs' : m'.seg = s) (hl : m.lvl = m'.lvl) (hi : m.idx = m'.idx) : m = m' :=
  Traffic.countP_le_one (pt_sends_le_one hbal hok htop m.lvl m.idx) hm hm'
    (by simp [atP, hs]) (by simp [atP, hs', hl, hi])

/-- **One `WSL` row per leaf index** (segment `s`). -/
theorem wsl_unique {l l' : WslRow Kd V α} (hl : l ∈ wsl) (hl' : l' ∈ wsl) (hs : l.seg = s)
    (hs' : l'.seg = s) (hi : l.i = l'.i) : l = l' := by
  have hc : wsl.countP (fun x => decide (x.seg = s ∧ x.i = l'.i)) ≤ 1 := by
    refine Nat.le_trans ?_ (pt_sends_le_one hbal hok htop 0 l'.i)
    simp only [sendsAt, ptSends, List.countP_append, List.countP_map]
    refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun x _ => ?_)) (Nat.le_add_right _ _)
    simp [atP, WslRow.ptM]
  exact Traffic.countP_le_one hc hl hl' (by simp [hs, hi]) (by simp [hs'])

end Count

/-- Every sent `PT` message is absorbed by a path node at the parent position. -/
theorem pt_recv (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) {m : PT α}
    (hm : m ∈ ptSends wsl wsp) :
    ∃ r ∈ wsp, (r.tl = true ∧ r.inL = m) ∨ (r.tr = true ∧ r.inR = m) := by
  have := hbal.subset hm
  simp only [ptRecvs, List.mem_append, List.mem_map, List.mem_filter] at this
  rcases this with ⟨r, ⟨hr, ht⟩, e⟩ | ⟨r, ⟨hr, ht⟩, e⟩
  · exact ⟨r, hr, Or.inl ⟨ht, e⟩⟩
  · exact ⟨r, hr, Or.inr ⟨ht, e⟩⟩

/-- **Ancestors**: a touched leaf of segment `s` has a `PT` message at every level below the
root, at its ancestor's index. -/
theorem pt_anc {D : Nat} (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp))
    (hok : ∀ r ∈ wsp, ∃ H, WspOK (α := α) H D r) {l : WslRow Kd V α} (hl : l ∈ wsl) :
    ∀ L, L < D → ∃ m ∈ ptSends wsl wsp, m.seg = l.seg ∧ m.lvl = L ∧ m.idx = l.i / 2 ^ L
  | 0, _ => ⟨l.ptM, List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩), rfl, rfl, by simp [WslRow.ptM]⟩
  | L + 1, hL => by
    obtain ⟨m, hm, e1, e2, e3⟩ := pt_anc hbal hok hl L (by omega)
    obtain ⟨r, hr, hc⟩ := pt_recv hbal hm
    obtain ⟨H, hk⟩ := hok r hr
    have hpos : r.seg = m.seg ∧ r.lvl = m.lvl ∧ r.idx = m.idx / 2 := by
      rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [WspRow.inL, WspRow.inR] <;> omega
    cases ht : r.top with
    | true => have := hk.topLvl ht; omega
    | false =>
      refine ⟨r.outM, List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simp [ht]⟩, rfl⟩),
        by simp [WspRow.outM, hpos.1, e1], by simp [WspRow.outM, hpos.2.1, e2], ?_⟩
      simp only [WspRow.outM, hpos.2.2, e3, Nat.pow_succ, Nat.div_div_eq_div_mul]

end PTBus

/-! ## The segment's `Upd` description -/

section Build
variable {Kd V α : Type}

/-- Every touched leaf of the description (absolute index `j` at level `L`) satisfies `P`. -/
def LeavesIn (P : Nat → α → α → Prop) : Nat → Nat → Upd α → Prop
  | _, _, .keep _ => True
  | 0, j, .leaf o n => P j o n
  | L + 1, j, .node a b => LeavesIn P L (2 * j) a ∧ LeavesIn P L (2 * j + 1) b
  | _, _, _ => False

/-- The description touches leaf `i` with old / new digest `(o, n)`. -/
def Has (i : Nat) (o n : α) : Nat → Nat → Upd α → Prop
  | 0, j, .leaf o' n' => j = i ∧ o' = o ∧ n' = n
  | L + 1, j, .node a b => Has i o n L (2 * j) a ∨ Has i o n L (2 * j + 1) b
  | _, _, _ => False

theorem leavesIn_keep (P : Nat → α → α → Prop) (L j : Nat) (h : α) : LeavesIn P L j (.keep h) := by
  cases L <;> trivial

theorem fits_keep (L : Nat) (h : α) : (Upd.keep h).Fits L := by
  cases L <;> trivial

/-! ### Reading the leaves of a description -/

theorem has_pos {i : Nat} {o n : α} : ∀ (L j : Nat) (u : Upd α), Has i o n L j u → i / 2 ^ L = j
  | 0, j, .leaf _ _, h => by simp only [Has] at h; simp [h.1]
  | L + 1, j, .node a b, h => by
    have e : i / 2 ^ (L + 1) = i / 2 ^ L / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rcases h with h | h <;> (have := has_pos L _ _ h; omega)
  | 0, _, .keep _, h => by simp [Has] at h
  | 0, _, .node _ _, h => by simp [Has] at h
  | _ + 1, _, .keep _, h => by simp [Has] at h
  | _ + 1, _, .leaf _ _, h => by simp [Has] at h

theorem leavesIn_has {P : Nat → α → α → Prop} {i : Nat} {o n : α} :
    ∀ (L j : Nat) (u : Upd α), LeavesIn P L j u → Has i o n L j u → P i o n
  | 0, j, .leaf o' n', hl, h => by
    simp only [Has] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact hl
  | L + 1, j, .node a b, hl, h => by
    rcases h with h | h
    · exact leavesIn_has L _ a hl.1 h
    · exact leavesIn_has L _ b hl.2 h
  | 0, _, .keep _, _, h => by simp [Has] at h
  | 0, _, .node _ _, _, h => by simp [Has] at h
  | _ + 1, _, .keep _, _, h => by simp [Has] at h
  | _ + 1, _, .leaf _ _, _, h => by simp [Has] at h

theorem mod_left {i L j : Nat} (h : i / 2 ^ L = 2 * j) : i % 2 ^ (L + 1) = i % 2 ^ L := by
  rw [Nat.mod_pow_succ, h]; simp

theorem mod_right {i L j : Nat} (h : i / 2 ^ L = 2 * j + 1) :
    i % 2 ^ (L + 1) = 2 ^ L + i % 2 ^ L := by
  rw [Nat.mod_pow_succ, h]; simp [Nat.add_mod]; omega

/-- A touched leaf's old digest is the list's leaf at its position (`Agrees`). -/
theorem agrees_has {i : Nat} {o n : α} :
    ∀ (L j : Nat) (u : Upd α) (l : List α), u.Agrees L l → Has i o n L j u → l[i % 2 ^ L]? = some o
  | 0, j, .leaf o' n', l, ha, h => by
    simp only [Has] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Upd.Agrees] at ha; subst ha; simp [Nat.mod_one]
  | L + 1, j, .node a b, l, ha, h => by
    simp only [Upd.Agrees] at ha
    rcases h with h | h
    · have hp := has_pos L _ _ h
      have := agrees_has L _ a _ ha.1 h
      rw [List.getElem?_take] at this
      simp only [Nat.mod_lt _ (Nat.two_pow_pos L), ↓reduceIte] at this
      rw [mod_left hp]; exact this
    · have hp := has_pos L _ _ h
      have := agrees_has L _ b _ ha.2 h
      rw [List.getElem?_drop] at this
      rw [mod_right hp]; exact this
  | 0, _, .keep _, _, _, h => by simp [Has] at h
  | 0, _, .node _ _, _, _, h => by simp [Has] at h
  | _ + 1, _, .keep _, _, _, h => by simp [Has] at h
  | _ + 1, _, .leaf _ _, _, _, h => by simp [Has] at h

theorem take_len {l : List α} {L : Nat} (hl : l.length = 2 ^ (L + 1)) :
    (l.take (2 ^ L)).length = 2 ^ L := by
  simp [hl, Nat.pow_succ]; omega

theorem drop_len {l : List α} {L : Nat} (hl : l.length = 2 ^ (L + 1)) :
    (l.drop (2 ^ L)).length = 2 ^ L := by
  simp [hl, Nat.pow_succ]; omega

/-- A touched leaf's position holds its new digest after `apply`. -/
theorem apply_has {i : Nat} {o n : α} :
    ∀ (L j : Nat) (u : Upd α) (l : List α), u.Fits L → l.length = 2 ^ L → Has i o n L j u →
      (u.apply L l)[i % 2 ^ L]? = some n
  | 0, j, .leaf o' n', l, _, _, h => by
    simp only [Has] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Upd.apply, Nat.mod_one]
  | L + 1, j, .node a b, l, hf, hl, h => by
    simp only [Upd.Fits] at hf
    have la := Merkle.Upd.apply_length L a _ hf.1 (take_len hl)
    simp only [Upd.apply]
    rcases h with h | h
    · have hp := has_pos L _ _ h
      rw [mod_left hp, List.getElem?_append_left (by rw [la]; exact Nat.mod_lt _ (Nat.two_pow_pos L))]
      exact apply_has L _ a _ hf.1 (take_len hl) h
    · have hp := has_pos L _ _ h
      rw [mod_right hp, List.getElem?_append_right (by rw [la]; omega), la, Nat.add_sub_cancel_left]
      exact apply_has L _ b _ hf.2 (drop_len hl) h
  | 0, _, .keep _, _, _, _, h => by simp [Has] at h
  | 0, _, .node _ _, _, _, _, h => by simp [Has] at h
  | _ + 1, _, .keep _, _, _, _, h => by simp [Has] at h
  | _ + 1, _, .leaf _ _, _, _, _, h => by simp [Has] at h

/-- An untouched position keeps its leaf after `apply`. -/
theorem apply_not {i : Nat} :
    ∀ (L j : Nat) (u : Upd α) (l : List α), u.Fits L → l.length = 2 ^ L → i / 2 ^ L = j →
      (∀ o n, ¬ Has i o n L j u) → (u.apply L l)[i % 2 ^ L]? = l[i % 2 ^ L]?
  | L, j, .keep _, l, _, _, _, _ => by cases L <;> rfl
  | 0, j, .leaf o' n', l, _, _, hp, hn => by
    exfalso; apply hn o' n'; show j = i ∧ o' = o' ∧ n' = n'; simp at hp; exact ⟨hp.symm, rfl, rfl⟩
  | L + 1, j, .node a b, l, hf, hl, hp, hn => by
    simp only [Upd.Fits] at hf
    have la := Merkle.Upd.apply_length L a _ hf.1 (take_len hl)
    have e : i / 2 ^ (L + 1) = i / 2 ^ L / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    simp only [Upd.apply]
    by_cases hev : i / 2 ^ L = 2 * j
    · rw [mod_left hev, List.getElem?_append_left (by rw [la]; exact Nat.mod_lt _ (Nat.two_pow_pos L))]
      rw [apply_not L _ a _ hf.1 (take_len hl) hev (fun o n h => hn o n (Or.inl h)),
        List.getElem?_take]
      simp only [Nat.mod_lt _ (Nat.two_pow_pos L), ↓reduceIte]
    · have hod : i / 2 ^ L = 2 * j + 1 := by omega
      rw [mod_right hod, List.getElem?_append_right (by rw [la]; omega), la, Nat.add_sub_cancel_left]
      rw [apply_not L _ b _ hf.2 (drop_len hl) hod (fun o n h => hn o n (Or.inr h)),
        List.getElem?_drop]
  | 0, _, .node _ _, _, hf, _, _, _ => by simp [Upd.Fits] at hf
  | _ + 1, _, .leaf _ _, _, hf, _, _, _ => by simp [Upd.Fits] at hf

/-- A touched leaf of segment `s`: some `WSL` row of `s` at index `i` with digests `(o, n)`. -/
def LeafP (wsl : List (WslRow Kd V α)) (s i : Nat) (o n : α) : Prop :=
  ∃ l ∈ wsl, l.seg = s ∧ l.i = i ∧ l.dgO = o ∧ l.dgN = n

/-- Every `WSL` row of segment `s` under position `(L, j)` is touched by the description. -/
def CoversAt (wsl : List (WslRow Kd V α)) (s L j : Nat) (u : Upd α) : Prop :=
  ∀ l ∈ wsl, l.seg = s → l.i / 2 ^ L = j → Has l.i l.dgO l.dgN L j u

/-- What a `PT` message at `(s, L, j)` describes. -/
def Built (H : α → α → α) (wsl : List (WslRow Kd V α)) (s L j : Nat) (o n : α) : Prop :=
  ∃ u : Upd α, u.Fits L ∧ u.old H = o ∧ u.new H = n ∧ LeavesIn (LeafP wsl s) L j u ∧
    CoversAt wsl s L j u

variable {wsl : List (WslRow Kd V α)} {wsp : List (WspRow α)} {s D : Nat} {H : α → α → α}
  (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (hok : ∀ r ∈ wsp, WspOK H D r)
  (htop : (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ 1)
include hbal hok htop

omit hbal htop in
theorem hok' : ∀ r ∈ wsp, ∃ H', WspOK (α := α) H' D r := fun r hr => ⟨H, hok r hr⟩

/-- **The node step**: a path node of segment `s` below the root, whose children's messages are
described, is described. -/
theorem node_step {r : WspRow α} (hr : r ∈ wsp) (hs : r.seg = s) (hlt : r.lvl < D)
    (ih : ∀ j o n, (⟨s, r.lvl, j, o, n⟩ : PT α) ∈ ptSends wsl wsp → Built H wsl s r.lvl j o n) :
    Built H wsl s (r.lvl + 1) r.idx r.oo r.on := by
  have hk := hok r hr
  have hm : ∀ {m : PT α}, m ∈ ptRecvs wsp → m ∈ ptSends wsl wsp := fun h => hbal.mem_iff.2 h
  -- left child
  have cl : ∃ ua : Upd α, ua.Fits r.lvl ∧ ua.old H = r.lo ∧ ua.new H = r.ln ∧
      LeavesIn (LeafP wsl s) r.lvl (2 * r.idx) ua ∧
      (r.tl = true → CoversAt wsl s r.lvl (2 * r.idx) ua) := by
    cases ht : r.tl with
    | true =>
      have := hm (List.mem_append_left _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, ht⟩, rfl⟩))
      rw [WspRow.inL, hs] at this
      obtain ⟨u, h1, h2, h3, h4, h5⟩ := ih _ _ _ this
      exact ⟨u, h1, h2, h3, h4, fun _ => h5⟩
    | false =>
      exact ⟨.keep r.lo, fits_keep _ _, rfl, hk.keepL ht, leavesIn_keep _ _ _ _, fun h => by simp at h⟩
  have cr : ∃ ub : Upd α, ub.Fits r.lvl ∧ ub.old H = r.ro ∧ ub.new H = r.rn ∧
      LeavesIn (LeafP wsl s) r.lvl (2 * r.idx + 1) ub ∧
      (r.tr = true → CoversAt wsl s r.lvl (2 * r.idx + 1) ub) := by
    cases ht : r.tr with
    | true =>
      have := hm (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, ht⟩, rfl⟩))
      rw [WspRow.inR, hs] at this
      obtain ⟨u, h1, h2, h3, h4, h5⟩ := ih _ _ _ this
      exact ⟨u, h1, h2, h3, h4, fun _ => h5⟩
    | false =>
      exact ⟨.keep r.ro, fits_keep _ _, rfl, hk.keepR ht, leavesIn_keep _ _ _ _, fun h => by simp at h⟩
  obtain ⟨ua, a1, a2, a3, a4, a5⟩ := cl
  obtain ⟨ub, b1, b2, b3, b4, b5⟩ := cr
  refine ⟨.node ua ub, ⟨a1, b1⟩, by simp [Upd.old, a2, b2, hk.hO],
    by simp [Upd.new, a3, b3, hk.hN], ⟨a4, b4⟩, ?_⟩
  -- coverage: the leaf's ancestor message at level `lvl` is absorbed by `r` itself
  intro l hl hls hli
  obtain ⟨m, hmS, e1, e2, e3⟩ := pt_anc hbal (hok' hok) hl r.lvl hlt
  obtain ⟨r', hr', hc⟩ := pt_recv hbal hmS
  have hq : l.i / 2 ^ r.lvl / 2 = r.idx := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; exact hli
  have hpos : r'.seg = s ∧ r'.lvl = r.lvl ∧ r'.idx = r.idx := by
    rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [WspRow.inL, WspRow.inR] at e1 e2 e3 ⊢ <;> omega
  have := row_unique hbal (hok' hok) htop hr' hr hpos.1 hs hpos.2.1 hpos.2.2
  subst this
  rcases hc with ⟨ht, rfl⟩ | ⟨ht, rfl⟩
  · simp only [WspRow.inL] at e3
    exact Or.inl (a5 ht l hl hls e3.symm)
  · simp only [WspRow.inR] at e3
    exact Or.inr (b5 ht l hl hls e3.symm)

/-- **Every `PT` message of segment `s` is described** (by induction on the level). -/
theorem pt_built : ∀ L j o n, (⟨s, L, j, o, n⟩ : PT α) ∈ ptSends wsl wsp → Built H wsl s L j o n
  | 0, j, o, n, hm => by
    have hm' := hm
    simp only [ptSends, List.mem_append, List.mem_map, List.mem_filter] at hm'
    rcases hm' with ⟨l0, hl0, e⟩ | ⟨r, -, e⟩
    · simp only [WslRow.ptM, PT.mk.injEq] at e
      obtain ⟨e1, -, e3, e4, e5⟩ := e
      refine ⟨.leaf o n, trivial, rfl, rfl, ⟨l0, hl0, e1, e3, e4, e5⟩, ?_⟩
      intro l hl hls hli
      simp only [Nat.pow_zero, Nat.div_one] at hli
      have := send_unique hbal (hok' hok) htop
        (List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩)) hm hls rfl rfl
        (by simp [WslRow.ptM, hli])
      simp only [WslRow.ptM, PT.mk.injEq] at this
      exact ⟨hli.symm, this.2.2.2.1.symm, this.2.2.2.2.symm⟩
    · simp [WspRow.outM] at e
  | L + 1, j, o, n, hm => by
    have hm' := hm
    simp only [ptSends, List.mem_append, List.mem_map, List.mem_filter] at hm'
    rcases hm' with ⟨l0, -, e⟩ | ⟨r, ⟨hr, -⟩, e⟩
    · simp [WslRow.ptM] at e
    · simp only [WspRow.outM, PT.mk.injEq] at e
      obtain ⟨e1, e2, e3, e4, e5⟩ := e
      have hlt := send_lt hbal (hok' hok) hm
      simp only at hlt
      have := node_step hbal hok htop hr e1 (by omega) (by
        rw [show r.lvl = L by omega]; exact pt_built L)
      rw [show r.lvl = L by omega, e3, e4, e5] at this
      exact this

/-- **The segment's update from its traffic.**  The top row of segment `s` is the root of an
`Upd` description of depth `D` whose touched leaves are `WSL` rows of `s` (`LeavesIn`) and which
touches every `WSL` row of `s` at its index `i < 2^D` with its `(dgO, dgN)`. -/
theorem seg_update {r : WspRow α} (hr : r ∈ wsp) (ht : r.top = true) (hs : r.seg = s) :
    ∃ u : Upd α, u.Fits D ∧ u.old H = r.oo ∧ u.new H = r.on ∧ LeavesIn (LeafP wsl s) D 0 u ∧
      ∀ l ∈ wsl, l.seg = s → l.i < 2 ^ D ∧ Has l.i l.dgO l.dgN D 0 u := by
  have hk := hok r hr
  have hD := hk.topLvl ht
  have hI := hk.topIdx ht
  obtain ⟨u, h1, h2, h3, h4, h5⟩ := node_step hbal hok htop hr hs (by omega) (pt_built hbal hok htop r.lvl)
  rw [hD] at h1 h4 h5
  rw [hI] at h4 h5
  refine ⟨u, h1, h2, h3, h4, fun l hl hls => ?_⟩
  have hlt : l.i < 2 ^ D := by
    obtain ⟨m, hmS, e1, e2, e3⟩ := pt_anc hbal (hok' hok) hl r.lvl (by omega)
    obtain ⟨r', hr', hc⟩ := pt_recv hbal hmS
    have hk' := hok r' hr'
    have hpos : r'.seg = m.seg ∧ r'.lvl = m.lvl ∧ (m.idx = 2 * r'.idx ∨ m.idx = 2 * r'.idx + 1) := by
      rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [WspRow.inL, WspRow.inR]
    cases ht' : r'.top with
    | false =>
      have := send_lt hbal (hok' hok)
        (List.mem_append_right _ (List.mem_map.2 ⟨r', List.mem_filter.2 ⟨hr', by simp [ht']⟩, rfl⟩))
      simp only [WspRow.outM] at this
      omega
    | true =>
      have := hk'.topIdx ht'
      have hq : l.i / 2 ^ r.lvl < 2 := by omega
      have hp : 2 ^ D = 2 ^ r.lvl * 2 := by rw [← hD, Nat.pow_succ]
      have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r.lvl)).1 hq
      rw [hp]; omega
  exact ⟨hlt, h5 l hl hls (Nat.div_eq_of_lt hlt)⟩

/-- **The segment's root step** (`Merkle.batch_update_sound`, no collision of `H` as a named
hypothesis): if the top row's incoming `RCH(s, oo)` is the root of the working set `ws`, every
touched leaf's old digest is `ws`'s leaf at its index and the outgoing `RCH(s+1, on)` is the root
of `ws` with exactly the touched leaves replaced by their new digests. -/
theorem seg_root (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) {r : WspRow α} (hr : r ∈ wsp)
    (ht : r.top = true) (hs : r.seg = s) (ws : List α) (hlen : ws.length = 2 ^ D)
    (hroot : root H D ws = some r.oo) :
    ∃ u : Upd α, u.Fits D ∧ LeavesIn (LeafP wsl s) D 0 u ∧
      (∀ l ∈ wsl, l.seg = s → l.i < 2 ^ D ∧ Has l.i l.dgO l.dgN D 0 u) ∧
      u.Agrees D ws ∧ root H D (u.apply D ws) = some r.on := by
  obtain ⟨u, h1, h2, h3, h4, h5⟩ := seg_update hbal hok htop hr ht hs
  rw [← h2] at hroot
  obtain ⟨a1, a2⟩ := batch_update_sound H hinj D u ws h1 hlen hroot
  exact ⟨u, h1, h4, h5, a1, h3 ▸ a2⟩

/-- **The segment's root step, leaf by leaf.**  Under the hypotheses of `seg_root`, there is a
working set `ws'` with `RCH(s+1) = root ws'` such that at every index `i < 2^D`: a `WSL` row of
segment `s` at `i` has old digest `ws[i]` and new digest `ws'[i]`; with no `WSL` row of `s` at
`i`, `ws'[i] = ws[i]` (and there is at most one `WSL` row of `s` per index: `wsl_unique`).  So the
segment rewrites exactly its touched leaves. -/
theorem seg_root_leaves (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) {r : WspRow α}
    (hr : r ∈ wsp) (ht : r.top = true) (hs : r.seg = s) (ws : List α) (hlen : ws.length = 2 ^ D)
    (hroot : root H D ws = some r.oo) :
    ∃ ws' : List α, ws'.length = 2 ^ D ∧ root H D ws' = some r.on ∧
      (∀ l ∈ wsl, l.seg = s → l.i < 2 ^ D ∧ ws[l.i]? = some l.dgO ∧ ws'[l.i]? = some l.dgN) ∧
      ∀ i, i < 2 ^ D → (∀ l ∈ wsl, l.seg = s → l.i ≠ i) → ws'[i]? = ws[i]? := by
  obtain ⟨u, hf, hlv, hcov, hag, hrt⟩ := seg_root hbal hok htop hinj hr ht hs ws hlen hroot
  refine ⟨u.apply D ws, Merkle.Upd.apply_length D u ws hf hlen, hrt, fun l hl hls => ?_, ?_⟩
  · obtain ⟨hlt, hh⟩ := hcov l hl hls
    have h1 := agrees_has D 0 u ws hag hh
    have h2 := apply_has D 0 u ws hf hlen hh
    rw [Nat.mod_eq_of_lt hlt] at h1 h2
    exact ⟨hlt, h1, h2⟩
  · intro i hi hno
    have := apply_not D 0 u ws hf hlen (Nat.div_eq_of_lt hi) (fun o n h => by
      obtain ⟨l, hl, hls, hli, -, -⟩ := leavesIn_has D 0 u hlv h
      exact hno l hl hls hli)
    rwa [Nat.mod_eq_of_lt hi] at this

end Build

end StateM5a.WsBus
