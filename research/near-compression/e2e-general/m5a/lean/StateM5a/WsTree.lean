import StateM5a.WsSeg

/-!
# StateM5a.WsTree — a full tree build on a `PT`-shaped bus (record level; the `WSN` build)

`WSN` builds the INTAKE and FINAL trees on the `TREE` bus.  It has the shape of `WsBus`'s `PT`
traffic: `WSB` sends one leaf message `(ph, 0, i, dg)` per row, like `WSL`, and an active `WSN`
row at `(ph, lvl, idx)` always receives both children (`tl = tr = true`) and sends
`(ph, lvl + 1, idx, H l r)` unless it is the top row.  So the segment `seg` of `WsBus` is the phase
here, and old and new digests coincide.  With `lv s i` the leaf digest of phase `s` at index `i`:

* `tree_msg`: every message at `(s, L, j)` carries the root of the leaves `j·2^L … (j+1)·2^L − 1`
  (`slice`; by induction on `L` with `Merkle.root_succ_split`; no collision resistance needed);
* `tree_top`: a top row's digest is the root of its phase's `2^D` leaves;
* `tree_tops_le`: with one leaf message per `(phase, index)`, there is at most one top row per
  phase (counting up from the leaves: the rows at `(L + 1, j)` each absorb the message at
  `(L, 2j)`, and there is at most one of those);
* `tree_root`: so a phase with a leaf message has exactly one top row, and its digest is
  the phase's root.
-/

namespace StateM5a.WsTree

open StateM5a.WsBus StateM5a.Merkle

variable {Kd V α : Type}

/-- The leaves `j·2^L … (j+1)·2^L − 1` of phase `s`. -/
def slice (lv : Nat → Nat → α) (s L j : Nat) : List α :=
  (List.range (2 ^ L)).map fun k => lv s (j * 2 ^ L + k)

theorem slice_length (lv : Nat → Nat → α) (s L j : Nat) : (slice lv s L j).length = 2 ^ L := by
  simp [slice]

theorem slice_take (lv : Nat → Nat → α) (s L j : Nat) :
    (slice lv s (L + 1) j).take (2 ^ L) = slice lv s L (2 * j) := by
  apply List.ext_getElem?
  intro k
  simp only [slice, List.getElem?_take, List.getElem?_map]
  by_cases hk : k < 2 ^ L
  · have h2 : k < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
    simp only [hk, ↓reduceIte, List.getElem?_range h2, List.getElem?_range hk, Option.map_some]
    congr 2
    rw [Nat.pow_succ, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2]
  · simp only [hk, ↓reduceIte]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem slice_drop (lv : Nat → Nat → α) (s L j : Nat) :
    (slice lv s (L + 1) j).drop (2 ^ L) = slice lv s L (2 * j + 1) := by
  apply List.ext_getElem?
  intro k
  simp only [slice, List.getElem?_drop, List.getElem?_map]
  by_cases hk : k < 2 ^ L
  · have h2 : 2 ^ L + k < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
    simp only [List.getElem?_range h2, List.getElem?_range hk, Option.map_some]
    congr 2
    rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2]
    omega
  · rw [List.getElem?_eq_none (by simp [Nat.pow_succ]; omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem single_of_mem {β : Type} {q : β} : ∀ {L : List β}, q ∈ L → L.length ≤ 1 → L = [q]
  | [x], hm, _ => by rw [List.mem_singleton.1 hm]
  | [], hm, _ => absurd hm List.not_mem_nil
  | _ :: _ :: _, _, hl => by simp at hl

section
variable {wsl : List (WslRow Kd V α)} {wsp : List (WspRow α)} {D : Nat} {H : α → α → α}
  {lv : Nat → Nat → α}
  (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (hok : ∀ r ∈ wsp, WspOK H D r)
  (hfull : ∀ r ∈ wsp, r.tl = true ∧ r.tr = true)
  (hleaf : ∀ l ∈ wsl, l.dgO = lv l.seg l.i)
include hbal hok hfull hleaf

/-- **Every tree message carries the root of its leaves.** -/
theorem tree_msg (s : Nat) : ∀ L j o n, (⟨s, L, j, o, n⟩ : PT α) ∈ ptSends wsl wsp →
    root H L (slice lv s L j) = some o
  | 0, j, o, n, hm => by
    simp only [ptSends, List.mem_append, List.mem_map, List.mem_filter] at hm
    rcases hm with ⟨l, hl, e⟩ | ⟨r, -, e⟩
    · simp only [WslRow.ptM, PT.mk.injEq] at e
      obtain ⟨e1, -, e3, e4, -⟩ := e
      simp only [slice, Nat.pow_zero, List.range_one, List.map_cons, List.map_nil, Nat.mul_one,
        Nat.add_zero, root]
      rw [← e4, hleaf l hl, e1, e3]
    · simp [WspRow.outM] at e
  | L + 1, j, o, n, hm => by
    simp only [ptSends, List.mem_append, List.mem_map, List.mem_filter] at hm
    rcases hm with ⟨l, -, e⟩ | ⟨r, ⟨hr, -⟩, e⟩
    · simp [WslRow.ptM] at e
    · simp only [WspRow.outM, PT.mk.injEq] at e
      obtain ⟨e1, e2, e3, e4, -⟩ := e
      have hk := hok r hr
      obtain ⟨htl, htr⟩ := hfull r hr
      have mL : (⟨s, L, 2 * j, r.lo, r.ln⟩ : PT α) ∈ ptSends wsl wsp := by
        have := hbal.mem_iff.2 (List.mem_append_left _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, htl⟩, rfl⟩))
        simpa [WspRow.inL, e1, show r.lvl = L by omega, e3] using this
      have mR : (⟨s, L, 2 * j + 1, r.ro, r.rn⟩ : PT α) ∈ ptSends wsl wsp := by
        have := hbal.mem_iff.2 (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, htr⟩, rfl⟩))
        simpa [WspRow.inR, e1, show r.lvl = L by omega, e3] using this
      have a := tree_msg s L (2 * j) _ _ mL
      have b := tree_msg s L (2 * j + 1) _ _ mR
      rw [root_succ_split H L _ (by rw [slice_length]), slice_take, slice_drop, a, b, ← e4, hk.hO]
      rfl

/-- **A top row's digest is its phase's root.** -/
theorem tree_top {q : WspRow α} (hq : q ∈ wsp) (ht : q.top = true) :
    root H D (slice lv q.seg D 0) = some q.oo := by
  have hk := hok q hq
  obtain ⟨htl, htr⟩ := hfull q hq
  have hD := hk.topLvl ht
  have hI := hk.topIdx ht
  have mL : (⟨q.seg, q.lvl, 0, q.lo, q.ln⟩ : PT α) ∈ ptSends wsl wsp := by
    have := hbal.mem_iff.2 (List.mem_append_left _ (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, htl⟩, rfl⟩))
    simpa [WspRow.inL, hI] using this
  have mR : (⟨q.seg, q.lvl, 1, q.ro, q.rn⟩ : PT α) ∈ ptSends wsl wsp := by
    have := hbal.mem_iff.2 (List.mem_append_right _ (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, htr⟩, rfl⟩))
    simpa [WspRow.inR, hI] using this
  have a := tree_msg hbal hok hfull hleaf q.seg _ _ _ _ mL
  have b := tree_msg hbal hok hfull hleaf q.seg _ _ _ _ mR
  rw [← hD, root_succ_split H q.lvl _ (by rw [slice_length]), slice_take, slice_drop, a, b, hk.hO]
  rfl

omit hleaf in
/-- **At most one top row per phase** (one leaf message per `(phase, index)`). -/
theorem tree_tops_le (hdist : ∀ s i, wsl.countP (fun l => decide (l.seg = s ∧ l.i = i)) ≤ 1) (s : Nat) :
    (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ 1 := by
  -- rows at `(L + 1, j)` absorb the message at `(L, 2j)`
  have hrow : ∀ L j, rowsAt wsp s (L + 1) j ≤ sendsAt wsl wsp s L (2 * j) := by
    intro L j
    rw [sends_eq_recvs hbal]
    simp only [ptRecvs, List.countP_append, List.countP_map, List.countP_filter, rowsAt]
    refine Nat.le_trans ?_ (Nat.le_add_right _ _)
    apply List.countP_mono_left
    intro r hr h
    simp only [decide_eq_true_eq] at h
    simp [atP, WspRow.inL, (hfull r hr).1, h.1, show r.lvl = L by omega, h.2.2]
  have hs : ∀ L j, sendsAt wsl wsp s L j ≤ 1 := by
    intro L
    induction L with
    | zero =>
      intro j
      have h0 : ((wsp.filter fun r => !r.top).map WspRow.outM).countP (atP s 0 j) = 0 := by
        rw [List.countP_eq_zero]
        intro m hm
        obtain ⟨r, -, rfl⟩ := List.mem_map.1 hm
        simp [atP, WspRow.outM]
      simp only [sendsAt, ptSends, List.countP_append, h0, Nat.add_zero, List.countP_map]
      refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun l _ => ?_)) (hdist s j)
      simp [atP, WslRow.ptM]
    | succ L ih =>
      intro j
      have h1 := rows_eq (wsl := wsl) (wsp := wsp) (s := s) (L + 1) j (by omega)
      have h2 := hrow L j
      have h3 := ih (2 * j)
      omega
  have htops : (topsOf wsp).countP (fun r => decide (r.seg = s)) ≤ topsAt wsp s D 0 := by
    rw [topsOf, List.countP_filter, topsAt]
    apply List.countP_mono_left
    intro r hr h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hk := hok r hr
    simp [h.1, h.2, hk.topLvl h.2, hk.topIdx h.2]
  by_cases hD : D = 0
  · have : topsAt wsp s D 0 = 0 := by
      rw [topsAt, List.countP_eq_zero]
      intro r hr h
      simp only [decide_eq_true_eq] at h
      have := (hok r hr).topLvl h.1
      omega
    omega
  · obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
    have h1 := rows_eq (wsl := wsl) (wsp := wsp) (s := s) (E + 1) 0 (by omega)
    have h2 := hrow E 0
    have h3 := hs E (2 * 0)
    omega

/-- **One root per phase**: a phase with a leaf message has exactly one top row, and its digest is
the root of the phase's `2^D` leaves. -/
theorem tree_root (hdist : ∀ s i, wsl.countP (fun l => decide (l.seg = s ∧ l.i = i)) ≤ 1)
    {l : WslRow Kd V α} (hl : l ∈ wsl) :
    ∃ q ∈ wsp, (wsp.filter fun r => r.top && decide (r.seg = l.seg)) = [q] ∧
      root H D (slice lv l.seg D 0) = some q.oo := by
  obtain ⟨q, hq, hs⟩ := WsSeg.wsl_top hbal hok hl
  obtain ⟨hqm, hqt⟩ := List.mem_filter.1 hq
  have hc := tree_tops_le hbal hok hfull hdist l.seg
  rw [topsOf, List.countP_filter] at hc
  have hmem : q ∈ wsp.filter fun r => r.top && decide (r.seg = l.seg) :=
    List.mem_filter.2 ⟨hqm, by simp [hs, by simpa using hqt]⟩
  have hlen : (wsp.filter fun r => r.top && decide (r.seg = l.seg)).length ≤ 1 := by
    rw [← List.countP_eq_length_filter]
    refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun r _ => ?_)) hc
    cases r.top <;> simp
  refine ⟨q, hqm, ?_, hs ▸ tree_top hbal hok hfull hleaf hqm (by simpa using hqt)⟩
  exact single_of_mem hmem hlen

end

end StateM5a.WsTree
