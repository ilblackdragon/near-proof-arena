import StateM5a.WsLeafF

/-!
# StateM5a.WsEntries — the final working set as entries: INTAKE entries with their latest writes

Unpacking the digest-level `WsKey.ws_decoded_final3` with `WsLeafF.content_eq` (equal leaf
blocks ⇒ equal key, pre-value and current value) under `LeafCR`:

* **`ws_entries`** (from `Holds`): for every touched leaf (`WSL` row `r`, entry index `i`):
  - its key and pre-value are the INTAKE entry's (`WSB` phase-0 row `i`) — they never change;
  - opened by the first touching segment: its opening value `(cp, cl, cv, wr)` is the INTAKE
    entry's current value, which is its pre-value, not written (`WsLeafF.wsb_ph0_cur`);
  - opened by a later segment: its opening value is the closing value of the last earlier
    touching segment;
  and for every real index `i < wsLen` the FINAL leaf (`WSB` phase-1 row `2^D + i`) has the INTAKE
  key and pre-value, and its current value is the closing value of the last touching segment, or
  the INTAKE value if no segment touched `i`.  With `WsKey.ws_decoded_final3`'s memory chains (each
  closing value is the latest write of its segment, accesses in time order), that is the final
  working set = the INTAKE entries with their latest writes.

Premises as `ws_decoded_final3`, plus `LeafCR` (already there) and `WsLeafF.WsbKdRange`.
-/

namespace StateM5a.WsEntries

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4 StateM5a.WsKey StateM5a.WsBus
open StateM5a.WsRaw StateM5a.Merkle StateM5a.WsSeg StateM5a.WsTree StateM5a.WsLeafF

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem wsl_mem {tr : Trace Fp} {pub : List Fp} {r : Nat} (hr : r < tr.height 10)
    (hA : (Wsl.c "act").eval tr 10 r pub = 1) : wslRow tr pub r ∈ wsl tr pub :=
  List.mem_filterMap.2 ⟨r, List.mem_range.2 hr, by simp [hA]⟩

/-- **The final working set: INTAKE entries with their latest writes.** -/
theorem ws_entries {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
    {compress : List Nat → List Nat → List Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR compress) (hLCR : LeafCR compress)
    (hdist0 : IntakeKeysDistinct compress (wsLeaves tr pub D 0) (WsLen.wsLen pub))
    (hW : WsbKdRange tr pub) :
    -- touched leaves
    (∀ r, r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      (wslOldE.kdV tr pub 10 r = wsbE.kdV tr pub 5 (wslRow tr pub r).i ∧
        wslOldE.preV tr pub 10 r = wsbE.preV tr pub 5 (wslRow tr pub r).i) ∧
      ((∀ l' ∈ wsl tr pub, l'.i = (wslRow tr pub r).i → (wslRow tr pub r).seg ≤ l'.seg) →
        (wslRow tr pub r).cur = wsbE.curV tr pub 5 (wslRow tr pub r).i) ∧
      (∀ r', r' < tr.height 10 → (Wsl.c "act").eval tr 10 r' pub = 1 →
        (wslRow tr pub r').i = (wslRow tr pub r).i → (wslRow tr pub r').seg < (wslRow tr pub r).seg →
        (∀ l'' ∈ wsl tr pub, l''.i = (wslRow tr pub r).i → l''.seg < (wslRow tr pub r).seg →
          l''.seg ≤ (wslRow tr pub r').seg) →
        (wslRow tr pub r).cur = (wslRow tr pub r').ncur)) ∧
    -- the INTAKE and FINAL entries
    (∀ i, i < WsLen.wsLen pub →
      wsbE.curV tr pub 5 i = wsbE.preV tr pub 5 i ++ [0] ∧
      wsbE.kdV tr pub 5 (2 ^ D + i) = wsbE.kdV tr pub 5 i ∧
      wsbE.preV tr pub 5 (2 ^ D + i) = wsbE.preV tr pub 5 i ∧
      ((∀ l ∈ wsl tr pub, l.i ≠ i) → wsbE.curV tr pub 5 (2 ^ D + i) = wsbE.curV tr pub 5 i) ∧
      (∀ r, r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 → (wslRow tr pub r).i = i →
        (∀ l' ∈ wsl tr pub, l'.i = i → l'.seg ≤ (wslRow tr pub r).seg) →
        wsbE.curV tr pub 5 (2 ^ D + i) = (wslRow tr pub r).ncur)) ∧
    -- each closing value is the latest write of its segment
    (∀ l ∈ wsl tr pub, ∃ s : List (WsCost.Acc (List Nat)), s.Perm (accOf (wsa tr pub) l.key) ∧
      s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = WsCost.lastVal l.cur s ∧ WsCost.Reads l.cur s) := by
  -- the context
  have hx4 : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG :=
    fun T hT i hi => ⟨(hx T hT i hi).1, (hx T hT i hi).2.1, (hx T hT i hi).2.2.1, (hx T hT i hi).2.2.2.1⟩
  have hxt : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE := fun T hT i hi => (hx T hT i hi).2.2.2.2
  obtain ⟨⟨r0, hs0, hr0⟩, ⟨nw', rF, hq0, hrF⟩⟩ := wsn_roots hH hxt hcomp hC hD1 hD
  obtain ⟨hpt, hok, -, -, hwl, hrch⟩ := ws_decoded hH hx4 hcomp hC hD1 hD
  have huniq : ∀ l ∈ wsl tr pub, ∀ l' ∈ wsl tr pub, l.seg = l'.seg → l.i = l'.i → l = l' :=
    fun l hl l' hl' e1 e2 => wsl_unique hpt (hok' hok) (rch_tops (hrch r0 rF nw' hs0 hq0) l.seg) hl hl' rfl
      e1.symm e2
  obtain ⟨nw, F1, F2, F3, F4, F5, -, F7⟩ :=
    ws_decoded_final3 hH hx hcomp hC hD1 hD hCR hLCR hdist0
  have hcW := holds_constr hH (t := 5) (by decide) (full_wsb (D := D))
  have hlogW := holds_log hH (t := 5) (by decide) (full_wsb (D := D))
  have hWle := WsLen.wsb_wsLen_le hcW hlogW (by omega) (pub := pub)
  have hLD : ∀ b b', GoodB b → GoodB b' → digest6 (compress IV384 b) = digest6 (compress IV384 b') → b = b' :=
    fun b b' g g' e => hLCR b b' g g' e
  -- a real index's two `WSB` rows
  have rowW : ∀ ph i, ph ≤ 1 → i < WsLen.wsLen pub → ph * 2 ^ D + i < tr.height 5 ∧
      ev tr 5 (ph * 2 ^ D + i) pub (Wsb.c "ph") = ph ∧
      (Wsb.c "real").eval tr 5 (ph * 2 ^ D + i) pub = 1 := by
    intro ph i hph hi
    obtain ⟨hr, hp, hix⟩ := WsLen.wsb_pos hcW hlogW (by omega) ph i hph (by omega)
    refine ⟨hr, hp, ev_one_eval ?_⟩
    exact (WsLen.wsb_real_iff hcW hlogW (by omega) hr).2.2 (by rw [hix]; exact hi)
  -- the leaf of a real `WSB` row
  have leafW : ∀ ph i, ph ≤ 1 → i < WsLen.wsLen pub → wsbE.OK tr pub 5 (ph * 2 ^ D + i) ∧
      ∃ bw, GoodB bw ∧ wsbE.blk.map (dec3 tr 5 (ph * 2 ^ D + i) pub) = bw.map wlimbs ∧
        (wsLeaves tr pub D ph)[i]? = some (digest6 (compress IV384 bw)) := by
    intro ph i hph hi
    obtain ⟨hr, -, hR⟩ := rowW ph i hph hi
    obtain ⟨hok5, bw, g, eB, eD⟩ := wsb_leaf hH hx4 hcomp hC hW hr hR
    exact ⟨hok5, bw, g, eB, by rw [wslLD tr pub D ph i (by omega), eD]⟩
  -- the leaves of a `WSL` row
  have leafL : ∀ r, r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      wslOldE.OK tr pub 10 r ∧ wslNewE.OK tr pub 10 r ∧
      (∃ bw, GoodB bw ∧ wslOldE.blk.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
        (wslRow tr pub r).dgO = digest6 (compress IV384 bw)) ∧
      (∃ bw, GoodB bw ∧ wslNewE.blk.map (dec3 tr 10 r pub) = bw.map wlimbs ∧
        (wslRow tr pub r).dgN = digest6 (compress IV384 bw)) := by
    intro r hr hA
    obtain ⟨⟨bo, lo, wo, eo, dO⟩, ⟨bn, ln, wn, en, dN⟩, -, -⟩ := wsl_leaf hH hx4 hcomp hC hr hA
    obtain ⟨k1, k2⟩ := wsl_okE hH hx4 hcomp hC hr hA
    exact ⟨k1, k2, ⟨bo, ⟨lo, wo⟩, eo, dO⟩, ⟨bn, ⟨ln, wn⟩, en, dN⟩⟩
  -- first opening
  have first : ∀ r, r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      (∀ l' ∈ wsl tr pub, l'.i = (wslRow tr pub r).i → (wslRow tr pub r).seg ≤ l'.seg) →
      wslOldE.kdV tr pub 10 r = wsbE.kdV tr pub 5 (wslRow tr pub r).i ∧
      wslOldE.preV tr pub 10 r = wsbE.preV tr pub 5 (wslRow tr pub r).i ∧
      (wslRow tr pub r).cur = wsbE.curV tr pub 5 (wslRow tr pub r).i := by
    intro r hr hA hfirst
    have hl := wsl_mem hr hA
    have hi := F7 _ hl
    obtain ⟨okO, -, ⟨bo, go, eo, dO⟩, -⟩ := leafL r hr hA
    obtain ⟨okW, bw, gw, eW, dW⟩ := leafW 0 _ (by omega) hi
    have h1 := (F2 _ hl).2.2.1
    rw [wsAt_untouched _ _ hfirst, dW, dO] at h1
    have hb := hLD _ _ go gw (Option.some.inj h1).symm
    simp only [Nat.zero_mul, Nat.zero_add] at okW eW
    rw [hb] at eo
    have := content_eq okO okW (eo.trans eW.symm)
    exact ⟨this.1, this.2.1, this.2.2⟩
  -- a later opening
  have later : ∀ r r', r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      r' < tr.height 10 → (Wsl.c "act").eval tr 10 r' pub = 1 →
      (wslRow tr pub r').i = (wslRow tr pub r).i → (wslRow tr pub r').seg < (wslRow tr pub r).seg →
      (∀ l'' ∈ wsl tr pub, l''.i = (wslRow tr pub r).i → l''.seg < (wslRow tr pub r).seg →
        l''.seg ≤ (wslRow tr pub r').seg) →
      wslOldE.kdV tr pub 10 r = wslOldE.kdV tr pub 10 r' ∧
      wslOldE.preV tr pub 10 r = wslOldE.preV tr pub 10 r' ∧
      (wslRow tr pub r).cur = (wslRow tr pub r').ncur := by
    intro r r' hr hA hr' hA' hi hs hlast
    have hl := wsl_mem hr hA
    have hl' := wsl_mem hr' hA'
    obtain ⟨okO, -, ⟨bo, go, eo, dO⟩, -⟩ := leafL r hr hA
    obtain ⟨-, okN', -, ⟨bn, gn, en, dN⟩⟩ := leafL r' hr' hA'
    have hb := open_eq_close (G := GoodB) (LD := fun b => digest6 (compress IV384 b)) hLD huniq
      (slice_length _ _ _ _) (fun l hl => (F2 l hl).2.2.1) hl hl' hi hs hlast (F2 _ hl).2.1 go gn dO dN
    rw [hb] at eo
    have := content_eq okO okN' (eo.trans en.symm)
    exact ⟨this.1.trans wslNew_kd, this.2.1.trans wslNew_pre, this.2.2⟩
  -- key and pre-value never change
  have never' : ∀ n r, (wslRow tr pub r).seg < n → r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      wslOldE.kdV tr pub 10 r = wsbE.kdV tr pub 5 (wslRow tr pub r).i ∧
      wslOldE.preV tr pub 10 r = wsbE.preV tr pub 5 (wslRow tr pub r).i := by
    intro n
    induction n with
    | zero => intro r hn; omega
    | succ n ih =>
      intro r hn hr hA
      by_cases hf : ∀ l' ∈ wsl tr pub, l'.i = (wslRow tr pub r).i → (wslRow tr pub r).seg ≤ l'.seg
      · obtain ⟨a, b, -⟩ := first r hr hA hf
        exact ⟨a, b⟩
      · simp only [Classical.not_forall, Classical.not_imp, Nat.not_le] at hf
        obtain ⟨l1, hl1, hi1, hs1⟩ := hf
        let L := (wsl tr pub).filter fun l => decide (l.i = (wslRow tr pub r).i ∧ l.seg < (wslRow tr pub r).seg)
        have hl1L : l1 ∈ L := List.mem_filter.2 ⟨hl1, by simp [hi1, hs1]⟩
        obtain ⟨l2, hl2L, hmax⟩ := exists_max (fun l : WslRow (List Nat) (List Nat) Dig => l.seg) hl1L
        obtain ⟨hl2, hc2⟩ := List.mem_filter.1 hl2L
        simp only [decide_eq_true_eq] at hc2
        obtain ⟨r2, hr2, hA2, rfl⟩ := actRows_mem hl2
        have hlast : ∀ l'' ∈ wsl tr pub, l''.i = (wslRow tr pub r).i → l''.seg < (wslRow tr pub r).seg →
            l''.seg ≤ (wslRow tr pub r2).seg := fun l'' h1 h2 h3 =>
          hmax l'' (List.mem_filter.2 ⟨h1, by simp [h2, h3]⟩)
        obtain ⟨a, b, -⟩ := later r r2 hr hA hr2 hA2 hc2.1 hc2.2 hlast
        obtain ⟨a', b'⟩ := ih r2 (by omega) hr2 hA2
        rw [hc2.1] at a' b'
        exact ⟨a.trans a', b.trans b'⟩
  have never : ∀ n r, (wslRow tr pub r).seg = n → r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 →
      wslOldE.kdV tr pub 10 r = wsbE.kdV tr pub 5 (wslRow tr pub r).i ∧
      wslOldE.preV tr pub 10 r = wsbE.preV tr pub 5 (wslRow tr pub r).i :=
    fun n r hn => never' (n + 1) r (by omega)
  refine ⟨fun r hr hA => ⟨never _ r rfl hr hA, fun hf => (first r hr hA hf).2.2,
    fun r' hr' hA' hi hs hlast => (later r r' hr hA hr' hA' hi hs hlast).2.2⟩, fun i hi => ?_,
    fun l hl => ?_⟩
  · -- the entries at a real index
    obtain ⟨hr0, hp0, -⟩ := rowW 0 i (by omega) hi
    obtain ⟨okI, bI, gI, eI, dI⟩ := leafW 0 i (by omega) hi
    obtain ⟨okF, bF, gF, eF, dF⟩ := leafW 1 i (by omega) hi
    simp only [Nat.zero_mul, Nat.zero_add] at hr0 hp0 okI eI
    simp only [Nat.one_mul] at okF eF
    have hcur0 := wsb_ph0_cur (hcW i hr0) hp0
    have untouched : (∀ l ∈ wsl tr pub, l.i ≠ i) →
        wsbE.kdV tr pub 5 (2 ^ D + i) = wsbE.kdV tr pub 5 i ∧
        wsbE.preV tr pub 5 (2 ^ D + i) = wsbE.preV tr pub 5 i ∧
        wsbE.curV tr pub 5 (2 ^ D + i) = wsbE.curV tr pub 5 i := by
      intro hn
      have h := F3 i (by omega) hn
      rw [dF, dI] at h
      have hb := hLD _ _ gF gI (Option.some.inj h)
      rw [hb] at eF
      exact content_eq okF okI (eF.trans eI.symm)
    have touched : ∀ r, r < tr.height 10 → (Wsl.c "act").eval tr 10 r pub = 1 → (wslRow tr pub r).i = i →
        (∀ l' ∈ wsl tr pub, l'.i = i → l'.seg ≤ (wslRow tr pub r).seg) →
        wsbE.kdV tr pub 5 (2 ^ D + i) = wsbE.kdV tr pub 5 i ∧
        wsbE.preV tr pub 5 (2 ^ D + i) = wsbE.preV tr pub 5 i ∧
        wsbE.curV tr pub 5 (2 ^ D + i) = (wslRow tr pub r).ncur := by
      intro r hr hA hri hmax
      have hl := wsl_mem hr hA
      obtain ⟨-, okN, -, ⟨bn, gn, en, dN⟩⟩ := leafL r hr hA
      have h := F4 _ hl (fun l' hl' e => hmax l' hl' (e.trans hri))
      rw [hri, dF, dN] at h
      have hb := hLD _ _ gF gn (Option.some.inj h)
      rw [hb] at eF
      obtain ⟨a, b, c⟩ := content_eq okF okN (eF.trans en.symm)
      obtain ⟨a', b'⟩ := never _ r rfl hr hA
      rw [hri] at a' b'
      exact ⟨a.trans (wslNew_kd.trans a'), b.trans (wslNew_pre.trans b'), c⟩
    have kp : wsbE.kdV tr pub 5 (2 ^ D + i) = wsbE.kdV tr pub 5 i ∧
        wsbE.preV tr pub 5 (2 ^ D + i) = wsbE.preV tr pub 5 i := by
      by_cases hn : ∀ l ∈ wsl tr pub, l.i ≠ i
      · obtain ⟨a, b, -⟩ := untouched hn
        exact ⟨a, b⟩
      · simp only [Classical.not_forall, Classical.not_imp, Classical.not_not] at hn
        obtain ⟨l1, hl1, hi1⟩ := hn
        let L := (wsl tr pub).filter fun l => decide (l.i = i)
        have hl1L : l1 ∈ L := List.mem_filter.2 ⟨hl1, by simp [hi1]⟩
        obtain ⟨l2, hl2L, hmax⟩ := exists_max (fun l : WslRow (List Nat) (List Nat) Dig => l.seg) hl1L
        obtain ⟨hl2, hc2⟩ := List.mem_filter.1 hl2L
        simp only [decide_eq_true_eq] at hc2
        obtain ⟨r2, hr2, hA2, rfl⟩ := actRows_mem hl2
        obtain ⟨a, b, -⟩ := touched r2 hr2 hA2 hc2 (fun l' hl' e =>
          hmax l' (List.mem_filter.2 ⟨hl', by simp [e]⟩))
        exact ⟨a, b⟩
    exact ⟨hcur0, kp.1, kp.2, fun hn => (untouched hn).2.2,
      fun r hr hA hri hmax => (touched r hr hA hri hmax).2.2⟩
  · obtain ⟨s, h1, h2, h3, -, h5⟩ := F5 l hl
    exact ⟨s, h1, h2, h3, h5⟩

end StateM5a.WsEntries
