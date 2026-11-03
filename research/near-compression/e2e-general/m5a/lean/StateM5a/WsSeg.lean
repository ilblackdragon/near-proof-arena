import StateM5a.WsBus

/-!
# StateM5a.WsSeg — composing the segments along the `RCH` chain (record level)

`WsBus.seg_root_leaves` is one segment: if `RCH(s)` is the root of a working set `ws`, then
`RCH(s+1)` is the root of `ws` with exactly segment `s`'s touched leaves replaced.  Here the
segments are chained from the INTAKE root `RCH(0) = r0` to the FINAL root `RCH(nw) = rF`
(`WsBus.rch_link`):

* `segApply wsl s w`: `w` with every `WSL` row of segment `s` writing its new digest at its index;
  `wsAt wsl ws0 s`: the working set after segments `0 … s−1`;
* `seg_chain`: every root on the `RCH` chain is the root of the corresponding `wsAt`;
* `tops_lt`: every top row's segment is `< nw` (an `RCH` message above `nw` would never be
  absorbed); `wsl_top`: every `WSL` row's segment has a top row;
* **`ws_compose`**: `root (wsAt nw) = rF`, and every `WSL` row `l` has `l.seg < nw`, `l.i < 2^D`,
  its old digest at its index in `wsAt l.seg` and its new digest there in `wsAt (l.seg + 1)`;
* `wsAt_untouched`, `wsAt_last`: index by index, `wsAt s` holds `ws0`'s leaf if no segment below
  `s` touched it, else the new digest of the touching row with the largest segment;
* `root_inj`: with a collision-free node hash, a root determines the leaf list;
* **`ws_final`**: if the FINAL leaf list `wsF` has root `rF`, then `wsF = wsAt nw`, and at every
  index `wsF` holds `ws0`'s leaf (never touched) or the new digest of the last touching row, and
  that row closes its entry's memory chain with the entry's latest written value of its segment
  (`WsBus.wm_chain`: accesses sorted latest first, each reading its predecessor).

Premises: `PT` / `RCH` / `WM` balance of the decoded rows, `WspOK` per path row, the node hash
collision-free (`hinj`), `root ws0 = r0` (the `WSN` INTAKE build), the per-access gap
`idp < t`, and `hkd` (two touched leaves of one segment with the same key are at the same
position; true when the working set's keys are distinct and the leaf digest binds the key).
-/

namespace StateM5a.WsSeg

open StateM5a.WsBus StateM5a.Merkle
open StateM5a.WsCost (Acc lastVal lastT Reads)

variable {Kd V α : Type}

/-! ## Applying a segment -/

/-- The new digest a `WSL` row of segment `s` writes at index `i`, if any. -/
def touch (wsl : List (WslRow Kd V α)) (s i : Nat) : Option α :=
  (wsl.find? fun l => decide (l.seg = s ∧ l.i = i)).map (·.dgN)

def segApply (wsl : List (WslRow Kd V α)) (s : Nat) (w : List α) : List α :=
  w.mapIdx fun i a => (touch wsl s i).getD a

/-- The working set after segments `0 … s − 1`. -/
def wsAt (wsl : List (WslRow Kd V α)) (ws0 : List α) : Nat → List α
  | 0 => ws0
  | s + 1 => segApply wsl s (wsAt wsl ws0 s)

section
variable {wsl : List (WslRow Kd V α)}

theorem touch_some {l : WslRow Kd V α} (hl : l ∈ wsl)
    (hu : ∀ l' ∈ wsl, l'.seg = l.seg → l'.i = l.i → l' = l) : touch wsl l.seg l.i = some l.dgN := by
  unfold touch
  cases h : wsl.find? (fun x => decide (x.seg = l.seg ∧ x.i = l.i)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h l hl)
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    rw [hu x hx hp.1 hp.2]; rfl

theorem touch_none {s i : Nat} (h : ∀ l ∈ wsl, l.seg = s → l.i ≠ i) : touch wsl s i = none := by
  unfold touch
  rw [List.find?_eq_none.2 (fun l hl => by simpa using h l hl)]
  rfl

theorem segApply_get (s i : Nat) (w : List α) :
    (segApply wsl s w)[i]? = w[i]?.map fun a => (touch wsl s i).getD a := by
  simp [segApply]

theorem wsAt_length {ws0 : List α} {n : Nat} (h0 : ws0.length = n) : ∀ s, (wsAt wsl ws0 s).length = n
  | 0 => h0
  | s + 1 => by simp [wsAt, segApply, wsAt_length h0 s]

end

/-! ## Roots determine leaves -/

theorem root_inj (H : α → α → α) (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) :
    ∀ (D : Nat) (a b : List α) (x : α), a.length = 2 ^ D → b.length = 2 ^ D →
      root H D a = some x → root H D b = some x → a = b
  | 0, a, b, x, ha, hb, h1, h2 => by
    match a, b, ha, hb with
    | [u], [v], _, _ =>
      simp only [root, Option.some.injEq] at h1 h2
      rw [h1, h2]
    | [], _, h, _ => simp at h
    | _ :: _ :: _, _, h, _ => simp at h
    | [_], [], _, h => simp at h
    | [_], _ :: _ :: _, _, h => simp at h
  | D + 1, a, b, x, ha, hb, h1, h2 => by
    have e : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
    have lt : ∀ l : List α, l.length = 2 ^ (D + 1) → (l.take (2 ^ D)).length = 2 ^ D := fun l hl => by
      simp [hl, e]
    have ld : ∀ l : List α, l.length = 2 ^ (D + 1) → (l.drop (2 ^ D)).length = 2 ^ D := fun l hl => by
      simp [hl, e]
    rw [root_succ_split H D a ha] at h1
    rw [root_succ_split H D b hb] at h2
    cases a1 : root H D (a.take (2 ^ D)) <;> cases a2 : root H D (a.drop (2 ^ D)) <;>
      cases b1 : root H D (b.take (2 ^ D)) <;> cases b2 : root H D (b.drop (2 ^ D)) <;>
      simp only [a1, a2, b1, b2, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
        reduceCtorEq, Option.some.injEq] at h1 h2
    rename_i u1 u2 v1 v2
    obtain ⟨e1, e2⟩ := hinj _ _ _ _ (h1.trans h2.symm)
    subst e1 e2
    have t := root_inj H hinj D _ _ _ (lt a ha) (lt b hb) a1 b1
    have d := root_inj H hinj D _ _ _ (ld a ha) (ld b hb) a2 b2
    rw [← List.take_append_drop (2 ^ D) a, ← List.take_append_drop (2 ^ D) b, t, d]

/-! ## The chain -/

section
variable {wsl : List (WslRow Kd V α)} {wsp : List (WspRow α)} {D nw : Nat} {H : α → α → α}
  {r0 rF : α} {ws0 : List α}
  (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (hok : ∀ r ∈ wsp, WspOK H D r)
  (hrch : (rchSends r0 wsp).Perm (rchRecvs nw rF wsp))
  (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d)
  (hlen0 : ws0.length = 2 ^ D) (hroot0 : root H D ws0 = some r0)

include hbal hok hrch hinj hlen0 in
/-- One segment applied, given its incoming root. -/
theorem seg_step {q : WspRow α} (hq : q ∈ topsOf wsp) {s : Nat} (hs : q.seg = s)
    (hr : root H D (wsAt wsl ws0 s) = some q.oo) :
    root H D (wsAt wsl ws0 (s + 1)) = some q.on ∧
      ∀ l ∈ wsl, l.seg = s → l.i < 2 ^ D ∧ (wsAt wsl ws0 s)[l.i]? = some l.dgO ∧
        (wsAt wsl ws0 (s + 1))[l.i]? = some l.dgN := by
  obtain ⟨hqm, hqt⟩ := List.mem_filter.1 hq
  have htop := rch_tops hrch s
  have hlen := wsAt_length (wsl := wsl) hlen0 s
  obtain ⟨ws', hl', hr', hT, hU⟩ :=
    seg_root_leaves hbal hok htop hinj hqm (by simpa using hqt) hs _ hlen hr
  have huniq : ∀ l ∈ wsl, l.seg = s → ∀ l' ∈ wsl, l'.seg = l.seg → l'.i = l.i → l' = l :=
    fun l hl hls l' hl' e1 e2 => wsl_unique hbal (hok' hok) htop hl' hl (e1.trans hls) hls e2
  have hws : ws' = wsAt wsl ws0 (s + 1) := by
    apply List.ext_getElem?
    intro i
    show ws'[i]? = (segApply wsl s (wsAt wsl ws0 s))[i]?
    rw [segApply_get]
    by_cases hi : i < 2 ^ D
    · by_cases ht : ∃ l ∈ wsl, l.seg = s ∧ l.i = i
      · obtain ⟨l, hl, hls, hli⟩ := ht
        have := touch_some hl (huniq l hl hls)
        rw [hls] at this
        subst hli
        rw [this, (hT l hl hls).2.2, (hT l hl hls).2.1]; rfl
      · have hn : ∀ l ∈ wsl, l.seg = s → l.i ≠ i := fun l hl hls hli => ht ⟨l, hl, hls, hli⟩
        rw [touch_none hn, hU i hi hn]
        cases (wsAt wsl ws0 s)[i]? <;> rfl
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
  refine ⟨hws ▸ hr', fun l hl hls => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT l hl hls
  exact ⟨h1, h2, hws ▸ h3⟩

include hbal hok hrch hinj hlen0 hroot0 in
/-- **Every root on the chain is the root of the working set so far.** -/
theorem seg_chain : ∀ s x, ((x = r0 ∧ s = 0) ∨ ∃ q ∈ topsOf wsp, q.seg + 1 = s ∧ q.on = x) →
    root H D (wsAt wsl ws0 s) = some x
  | 0, x, h => by
    rcases h with ⟨rfl, -⟩ | ⟨q, -, e, -⟩
    · exact hroot0
    · omega
  | s + 1, x, h => by
    rcases h with ⟨-, e⟩ | ⟨q, hq, e, rfl⟩
    · omega
    · have hs : q.seg = s := by omega
      obtain ⟨link0, linkS, -⟩ := rch_link hrch
      have hin : root H D (wsAt wsl ws0 s) = some q.oo := by
        apply seg_chain s q.oo
        cases s with
        | zero => exact Or.inl ⟨link0 q hq hs, rfl⟩
        | succ s' =>
          obtain ⟨q', hq', e1, e2⟩ := linkS q hq s' hs
          exact Or.inr ⟨q', hq', by omega, e2⟩
      exact (seg_step hbal hok hrch hinj hlen0 hq hs hin).1

include hrch in
/-- **Every top row is below `nw`.** -/
theorem tops_lt : ∀ q ∈ topsOf wsp, q.seg < nw := by
  intro q hq
  refine Classical.byContradiction fun hge => ?_
  obtain ⟨m, hm, hmax⟩ := exists_max (fun r : WspRow α => r.seg) hq
  have hmq : q.seg ≤ m.seg := hmax q hq
  have hsend : (m.seg + 1, m.on) ∈ rchSends r0 wsp := List.mem_cons_of_mem _ (List.mem_map.2 ⟨m, hm, rfl⟩)
  have := hrch.subset hsend
  simp only [rchRecvs, List.mem_cons, List.mem_map, Prod.mk.injEq] at this
  rcases this with ⟨e, -⟩ | ⟨r, hr, e, -⟩
  · omega
  · have : r.seg ≤ m.seg := hmax r hr
    omega

include hbal hok in
/-- **Every touched leaf's segment has a top row.** -/
theorem wsl_top {l : WslRow Kd V α} (hl : l ∈ wsl) : ∃ q ∈ topsOf wsp, q.seg = l.seg := by
  have hD : 0 < D := send_lt hbal (hok' hok) (List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩))
  obtain ⟨m, hm, e1, e2, -⟩ := pt_anc hbal (hok' hok) hl (D - 1) (by omega)
  obtain ⟨r, hr, hc⟩ := pt_recv hbal hm
  have hpos : r.seg = m.seg ∧ r.lvl = m.lvl := by
    rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [WspRow.inL, WspRow.inR]
  cases ht : r.top with
  | true => exact ⟨r, List.mem_filter.2 ⟨hr, by simp [ht]⟩, hpos.1.trans e1⟩
  | false =>
    have := send_lt hbal (hok' hok)
      (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simp [ht]⟩, rfl⟩))
    simp only [WspRow.outM] at this
    omega

include hbal hok hrch hinj hlen0 hroot0 in
/-- **The segments compose**: the working set after all `nw` segments has root `rF`, and every
touched leaf is in a segment `< nw`, at a tree position, with its old digest the working set's
leaf before its segment and its new digest the leaf after it. -/
theorem ws_compose :
    (wsAt wsl ws0 nw).length = 2 ^ D ∧ root H D (wsAt wsl ws0 nw) = some rF ∧
      ∀ l ∈ wsl, l.seg < nw ∧ l.i < 2 ^ D ∧ (wsAt wsl ws0 l.seg)[l.i]? = some l.dgO ∧
        (wsAt wsl ws0 (l.seg + 1))[l.i]? = some l.dgN := by
  obtain ⟨link0, linkS, linkF⟩ := rch_link hrch
  refine ⟨wsAt_length hlen0 nw, ?_, fun l hl => ?_⟩
  · apply seg_chain hbal hok hrch hinj hlen0 hroot0
    rcases linkF with ⟨h1, h2⟩ | ⟨q, hq, e1, e2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨q, hq, e1, e2⟩
  · obtain ⟨q, hq, hs⟩ := wsl_top hbal hok hl
    have hin : root H D (wsAt wsl ws0 l.seg) = some q.oo := by
      apply seg_chain hbal hok hrch hinj hlen0 hroot0
      cases h : l.seg with
      | zero => exact Or.inl ⟨link0 q hq (hs.trans h), rfl⟩
      | succ s' =>
        obtain ⟨q', hq', e1, e2⟩ := linkS q hq s' (hs.trans h)
        exact Or.inr ⟨q', hq', by omega, e2⟩
    obtain ⟨-, hT⟩ := seg_step hbal hok hrch hinj hlen0 hq hs hin
    exact ⟨hs ▸ tops_lt hrch q hq, hT l hl rfl⟩

end

/-! ## Index by index: the last touch wins -/

section
variable {wsl : List (WslRow Kd V α)} {ws0 : List α}
  (huniq : ∀ l ∈ wsl, ∀ l' ∈ wsl, l.seg = l'.seg → l.i = l'.i → l = l')

theorem wsAt_untouched (i : Nat) : ∀ s, (∀ l ∈ wsl, l.i = i → s ≤ l.seg) →
    (wsAt wsl ws0 s)[i]? = ws0[i]?
  | 0, _ => rfl
  | s + 1, h => by
    show (segApply wsl s (wsAt wsl ws0 s))[i]? = _
    rw [segApply_get, touch_none (fun l hl hls hli => by have := h l hl hli; omega),
      wsAt_untouched i s (fun l hl hli => by have := h l hl hli; omega)]
    cases ws0[i]? <;> rfl

include huniq in
theorem wsAt_last {n : Nat} (hlen : ws0.length = n) {l : WslRow Kd V α} (hl : l ∈ wsl) (hi : l.i < n) :
    ∀ s, l.seg < s → (∀ l' ∈ wsl, l'.i = l.i → l'.seg < s → l'.seg ≤ l.seg) →
      (wsAt wsl ws0 s)[l.i]? = some l.dgN
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | s + 1, h, hmax => by
    show (segApply wsl s (wsAt wsl ws0 s))[l.i]? = _
    rw [segApply_get]
    have hsome : ∃ a, (wsAt wsl ws0 s)[l.i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [wsAt_length hlen]; exact hi)⟩
    by_cases hs : l.seg = s
    · obtain ⟨a, ha⟩ := hsome
      rw [ha, ← hs, touch_some hl (fun l' hl' e1 e2 => huniq l' hl' l hl e1 e2)]
      rfl
    · have hn : ∀ l' ∈ wsl, l'.seg = s → l'.i ≠ l.i := fun l' hl' e1 e2 => by
        have := hmax l' hl' e2 (by omega); omega
      rw [touch_none hn, wsAt_last hlen hl hi s (by omega)
        (fun l' hl' e1 e2 => hmax l' hl' e1 (by omega))]
      rfl

end

/-! ## The final working set -/

section
variable [DecidableEq Kd]
variable {wsl : List (WslRow Kd V α)} {wsp : List (WspRow α)} {wsa : List (WsaRow Kd V)} {D nw : Nat}
  {H : α → α → α} {r0 rF : α} {ws0 wsF : List α}

/-- **The final working set.**  From `PT` / `RCH` / `WM` balance and the row facts: the FINAL
leaf list `wsF` (root `rF`) is the INTAKE list `ws0` (root `r0`) with, at every index, either the
INTAKE leaf (no segment touched it) or the new digest of the touching `WSL` row of the largest
segment; that row closes its entry's chain with the entry's latest written value of the segment
(accesses sorted latest first, strictly decreasing times, each reading its predecessor). -/
theorem ws_final
    (hbal : (ptSends wsl wsp).Perm (ptRecvs wsp)) (hok : ∀ r ∈ wsp, WspOK H D r)
    (hrch : (rchSends r0 wsp).Perm (rchRecvs nw rF wsp))
    (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d)
    (hlen0 : ws0.length = 2 ^ D) (hroot0 : root H D ws0 = some r0)
    (hlenF : wsF.length = 2 ^ D) (hrootF : root H D wsF = some rF)
    (hwm : (wmSends wsl wsa).Perm (wmRecvs wsl wsa)) (hgap : ∀ a ∈ wsa, a.idp < a.t)
    (hkd : ∀ l ∈ wsl, ∀ l' ∈ wsl, l.seg = l'.seg → l.kd = l'.kd → l.i = l'.i) :
    wsF = wsAt wsl ws0 nw ∧
    (∀ l ∈ wsl, l.seg < nw ∧ l.i < 2 ^ D ∧ (wsAt wsl ws0 l.seg)[l.i]? = some l.dgO ∧
        (wsAt wsl ws0 (l.seg + 1))[l.i]? = some l.dgN) ∧
    (∀ i, i < 2 ^ D → (∀ l ∈ wsl, l.i ≠ i) → wsF[i]? = ws0[i]?) ∧
    (∀ l ∈ wsl, (∀ l' ∈ wsl, l'.i = l.i → l'.seg ≤ l.seg) → wsF[l.i]? = some l.dgN) ∧
    (∀ l ∈ wsl, ∃ s : List (Acc V), s.Perm (accOf wsa l.key) ∧ s.Pairwise (fun a b => b.t < a.t) ∧
      l.ncur = lastVal l.cur s ∧ l.idl = lastT s ∧ Reads l.cur s) ∧
    (∀ a ∈ wsa, ∃ l ∈ wsl, l.key = a.key) := by
  obtain ⟨-, hrt, hT⟩ := ws_compose hbal hok hrch hinj hlen0 hroot0 (wsl := wsl)
  have hF : wsF = wsAt wsl ws0 nw :=
    root_inj H hinj D _ _ _ hlenF (wsAt_length hlen0 nw) hrootF hrt
  have huniq : ∀ l ∈ wsl, ∀ l' ∈ wsl, l.seg = l'.seg → l.i = l'.i → l = l' := by
    intro l hl l' hl' e1 e2
    exact wsl_unique hbal (hok' hok) (rch_tops hrch l.seg) hl hl' rfl e1.symm e2
  have hcnt : ∀ l ∈ wsl, wsl.countP (fun x => decide (x.seg = l.seg ∧ x.i = l.i)) ≤ 1 := by
    intro l _
    refine Nat.le_trans ?_ (pt_sends_le_one hbal (hok' hok) (rch_tops hrch l.seg) 0 l.i)
    simp only [sendsAt, ptSends, List.countP_append, List.countP_map]
    refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun x _ => ?_)) (Nat.le_add_right _ _)
    simp [atP, WslRow.ptM]
  have hdist : (wsl.map WslRow.key).Nodup := by
    rw [List.nodup_iff_count]
    intro k
    rw [List.count_eq_countP, List.countP_map]
    by_cases hk : ∃ l ∈ wsl, l.key = k
    · obtain ⟨l, hl, rfl⟩ := hk
      refine Nat.le_trans (List.countP_mono_left fun x hx h => ?_) (hcnt l hl)
      simp only [Function.comp_def, beq_iff_eq, WslRow.key, Prod.mk.injEq] at h
      simp [h.1, hkd x hx l hl h.1 h.2]
    · rw [List.countP_eq_zero.2]
      · omega
      · intro x hx h
        simp only [Function.comp_def, beq_iff_eq] at h
        exact hk ⟨x, hx, h⟩
  refine ⟨hF, hT, fun i hi hn => ?_, fun l hl hmax => ?_, fun l hl => wm_chain hwm hgap hdist hl,
    wm_orphan hwm hgap⟩
  · rw [hF]; exact wsAt_untouched i nw (fun l hl hli => absurd hli (hn l hl))
  · rw [hF]
    exact wsAt_last huniq hlen0 hl (hT l hl).2.1 nw (hT l hl).1 (fun l' hl' e _ => hmax l' hl' e)

end

end StateM5a.WsSeg
