import ZkFormal.NearV3.Link.Walk3Trie

/-!
# ZkFormal.NearV3.Link.Walk3 — walks compute `find` / absent on the record trie

`R := recsOf f vs`, `T n := fullTree R V n`.  For a walk `wv` (rows `0 … L-1`, `L ≥ 2`),
row `0` is the `START` row, the last row has symbol `END`, and the key is
`wv.key3 = [σ₁, …, σ_{L-2}]` (`key3_eq`: the symbols after `START`, without the final `END`).

* `walk3_pos` (**per-position invariant**): if rows `0 … i-1` are steps (mode 0), then
  `Pos f vs V X N I (restAt wv i)` at the position `(N, I) = (e[0], e[1])` of row `i`:
  `X := (T h.rid).find key` equals the lookup in the subtrie of record `N` of
  `(key N).take I ++ rest` (`rest` = symbols `σ_i … σ_{L-2}`).  Entering a kid goes to
  its `res` target, which answers `find` as the kid (`res_find`).
* `walk3_find` (**the walk link**): there is a head `h` with `h.tau = wv.tau`, and
  `fk = FK_VAL → (T h.rid).find key = some (some (valOf V (f wv.k)))`,
  `fk = FK_ABS → (T h.rid).find key = some none`.

Hypotheses beyond the task statement (discharged upstream; see the comments at `walk3_find`;
key lengths `< p` are derived here from `NodeWf3.rows`, `klen_of_rows`):
`hT` (total walk rows `< p`, as v1's `WalkLen` from `KEYNIB`) and `hsym` (walk symbols after `START` are
not `SYM_START`, from `KEYNIB`: the key provider sends nibbles and `END`).  Without
`hsym` a mid-walk row could take another head's `START` edge.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace ZkFormal.NearV3.Walk3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3 ZkFormal.NearV3.Link3
open NearSpec

/-- The walk's key: symbols of rows `1 … L-2`. -/
def _root_.ZkFormal.NearV3.WalkR.key3 (wv : WalkR) : List Nat :=
  (List.range (wv.steps.length - 2)).map fun t => (wv.step (t + 1)).sym

/-- Remaining symbols at row `i`: rows `i … L-2`. -/
def restAt (wv : WalkR) (i : Nat) : List Nat :=
  (List.range (wv.steps.length - 1 - i)).map fun t => (wv.step (i + t)).sym

theorem step_eq (wv : WalkR) {i : Nat} (hi : i < wv.steps.length) : wv.step i = wv.steps[i] := by
  simp [WalkR.step, List.getD_eq_getElem?_getD, hi]

theorem key3_eq (wv : WalkR) : wv.key3 = ((wv.steps.drop 1).dropLast).map (·.sym) := by
  apply List.ext_getElem
  · simp [WalkR.key3]; omega
  · intro t h1 h2
    simp only [WalkR.key3, List.length_map, List.length_range] at h1
    simp only [WalkR.key3, List.getElem_map, List.getElem_range, List.getElem_dropLast, List.getElem_drop]
    rw [step_eq wv (by omega)]
    congr 2; omega

theorem restAt_succ (wv : WalkR) {i : Nat} (h : i + 1 < wv.steps.length) :
    restAt wv i = (wv.step i).sym :: restAt wv (i + 1) := by
  unfold restAt
  have e : wv.steps.length - 1 - i = (wv.steps.length - 1 - (i + 1)) + 1 := by omega
  rw [e, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left; intro t _
  simp only [Function.comp]
  congr 2; omega

theorem restAt_last (wv : WalkR) : restAt wv (wv.steps.length - 1) = [] := by
  simp [restAt]

theorem restAt_one (wv : WalkR) : restAt wv 1 = wv.key3 := by
  unfold restAt WalkR.key3
  rw [show wv.steps.length - 1 - 1 = wv.steps.length - 2 by omega]
  apply List.map_congr_left; intro t _
  rw [Nat.add_comm]

theorem six : ∀ (e : List Nat), e.length = 6 →
    e = [e.getD 0 0, e.getD 1 0, e.getD 2 0, e.getD 3 0, e.getD 4 0, e.getD 5 0]
  | [_, _, _, _, _, _], _ => rfl
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | [_, _, _, _], h => by simp at h
  | [_, _, _, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem chain_getD {e e' : List Nat} (h : e.length = 6) (h' : e'.length = 6)
    (hc : e'.take 2 = (e.drop 3).take 2) : e'.getD 0 0 = e.getD 3 0 ∧ e'.getD 1 0 = e.getD 4 0 := by
  rw [six e h, six e' h'] at hc
  simp at hc
  exact hc

section Walk
variable {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3} {hs : List HeadE} {ws : List WalkR}

/-- All hypotheses of the walk link (internal form). -/
structure WalkHyp (f : Nat → Nat) (vs : List NodeS3) (V : List ValRec3) (hs : List HeadE)
    (ws : List WalkR) : Prop where
  node : NodeWf3 vs
  head : HeadWf hs
  walk : WalkWf3 ws
  balE : BusBal vs hs ws B_EDGE
  balB : BusBal vs hs ws B_BMAP
  rowsP : (ws.flatMap (·.steps)).length < P
  klen : ∀ s ∈ vs, klen3 s.v < P
  sym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START
  trie : TrieHyp f vs V
  hd : ∀ h ∈ hs, ∃ s : NodeS3, vs[h.rid]? = some s ∧ s.res = h.rres

theorem row_ok (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {i : Nat}
    (hi : i < wv.steps.length) : StepOk (wv.step i) (i + 1 == wv.steps.length) := by
  rw [step_eq wv hi]; exact G.walk.rows wv hw i hi

theorem row_mem {wv : WalkR} {i : Nat} (hi : i < wv.steps.length) : wv.step i ∈ wv.steps := by
  rw [step_eq wv hi]; exact List.getElem_mem hi

/-- A row's edge provided by a node record (when it is not a `START` edge). -/
theorem node_edge (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {i : Nat}
    (hi : i < wv.steps.length) (hm : (wv.step i).mode ≤ 1)
    (hnh : (wv.step i).e.getD 2 0 ≠ SYM_START ∨ (wv.step i).e.getD 5 0 ≠ EK_DOWN) :
    ∃ s, vs[(wv.step i).e.getD 0 0]? = some s ∧
      [(wv.step i).e.getD 0 0, (wv.step i).e.getD 1 0, (wv.step i).e.getD 2 0, (wv.step i).e.getD 3 0,
        (wv.step i).e.getD 4 0, (wv.step i).e.getD 5 0] ∈ edgesOf3 ((wv.step i).e.getD 0 0) s := by
  have hl := (row_ok G hw hi).elen
  rcases edge_provided3 G.node G.head G.walk G.balE G.rowsP G.klen hw (row_mem hi) hm with
    ⟨n, hn, he⟩ | ⟨h, hh, he⟩
  · have hsm := List.getElem_mem hn
    have hc := edges3_canon n vs[n] (by have := G.node.count; have := P_big; omega)
      (G.node.canon _ hsm) (G.klen _ hsm) (G.node.wf _ hsm) _ he
    have hmem := he
    rw [six _ hl] at hmem
    rw [hc.2.2.1] at hmem ⊢
    exact ⟨vs[n], List.getElem?_eq_getElem hn, hmem⟩
  · exfalso
    rw [he] at hnh
    simp at hnh

theorem start_head (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧ (wv.step 0).e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] := by
  have hL := G.walk.len wv hw
  obtain ⟨hm0, hs0, ht0⟩ := G.walk.start wv hw
  have hok := row_ok G hw (i := 0) (by omega)
  have hsym0 := (hok.stepE hm0).1
  rcases edge_provided3 G.node G.head G.walk G.balE G.rowsP G.klen hw (row_mem (i := 0) (by omega))
    (by omega) with ⟨n, hn, he⟩ | ⟨h, hh, he⟩
  · exfalso
    have hsm := List.getElem_mem hn
    have hc := edges3_canon n vs[n] (by have := G.node.count; have := P_big; omega)
      (G.node.canon _ hsm) (G.klen _ hsm) (G.node.wf _ hsm) _ he
    have := hc.2.2.2
    rw [hsym0, hs0] at this
    exact absurd this (by decide)
  · refine ⟨h, hh, ?_, he⟩
    rw [he] at ht0; simpa using ht0

/-- One step: a mode-0 row that is not the last moves the invariant to the next row. -/
theorem row_step (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {X : Option (Option Bytes)}
    {i : Nat} (h1 : 1 ≤ i) (hi : i + 1 < wv.steps.length) (hm : (wv.step i).mode = 0)
    (hp : Pos f vs V X ((wv.step i).e.getD 0 0) ((wv.step i).e.getD 1 0) (restAt wv i)) :
    Pos f vs V X ((wv.step (i + 1)).e.getD 0 0) ((wv.step (i + 1)).e.getD 1 0) (restAt wv (i + 1)) := by
  have hok := row_ok G hw (i := i) (by omega)
  have hnl : (i + 1 == wv.steps.length) = false := by simp; omega
  obtain ⟨hsy, hk, -⟩ := hok.stepE hm
  have hk := hk hnl
  have hsS := G.sym wv hw i h1 (by omega)
  obtain ⟨s, hs, he⟩ := node_edge G hw (i := i) (by omega) (by omega) (Or.inl (by rw [hsy]; exact hsS))
  rw [restAt_succ wv hi] at hp
  rw [hsy] at he
  have hn := pos_step G.trie hp hs he hk
  obtain ⟨e0, e1⟩ := chain_getD hok.elen (row_ok G hw hi).elen ((G.walk.chain wv hw i hi).1 hm).1
  rw [e0, e1]; exact hn

/-- **Per-position invariant**: rows `1 … L-1` reached through steps. -/
theorem walk3_pos (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧ ∀ i, 1 ≤ i → i < wv.steps.length → (∀ j < i, (wv.step j).mode = 0) →
      Pos f vs V ((fullTree (recsOf f vs) V h.rid).find wv.key3)
        ((wv.step i).e.getD 0 0) ((wv.step i).e.getD 1 0) (restAt wv i) := by
  obtain ⟨h, hh, ht, he0⟩ := start_head G hw
  refine ⟨h, hh, ht, ?_⟩
  have hL := G.walk.len wv hw
  intro i h1 hi hall
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- row 1: the head's `res` target
      obtain ⟨s, hs, hres⟩ := G.hd h hh
      have hp := pos_res G.trie hs hres (r := wv.key3) rfl
      have hok0 := row_ok G hw (i := 0) (by omega)
      obtain ⟨e0, e1⟩ := chain_getD hok0.elen (row_ok G hw (i := 1) hi).elen
        ((G.walk.chain wv hw 0 hi).1 (hall 0 (by omega))).1
      rw [e0, e1, he0, restAt_one]; exact hp
    · exact row_step G hw hpos hi (hall i (by omega))
        (ih hpos (by omega) (fun j hj => hall j (by omega)))

/-- After a non-step row, the last row is not a step. -/
theorem tail_mode (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) :
    ∀ d i, i + d + 1 = wv.steps.length → (wv.step i).mode ≠ 0 → wv.last.mode ≠ 0
  | 0, i, hd, hm => by
    unfold WalkR.last; rw [show wv.steps.length - 1 = i by omega]; exact hm
  | d + 1, i, hd, hm => by
    have := ((G.walk.chain wv hw i (by omega)).2 hm)
    exact tail_mode G hw d (i + 1) (by omega) (by omega)

/-- What a walk concludes, from a row reached through steps. -/
theorem walk3_concl (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {X : Option (Option Bytes)} :
    ∀ d i, i + d + 1 = wv.steps.length → 1 ≤ i → (wv.step (i - 1)).mode = 0 →
      Pos f vs V X ((wv.step i).e.getD 0 0) ((wv.step i).e.getD 1 0) (restAt wv i) →
      (wv.last.mode = 0 → X = some (some (valOf V (f (wv.last.e.getD 3 0))))) ∧
      (wv.last.mode ≠ 0 → X = some none) := by
  intro d
  induction d with
  | zero =>
    intro i hd h1 hprev hp
    have hok := row_ok G hw (i := i) (by omega)
    have hlast : (i + 1 == wv.steps.length) = true := by simp; omega
    have hli : wv.last = wv.step i := by unfold WalkR.last; rw [show wv.steps.length - 1 = i by omega]
    have hrest : restAt wv i = [] := by rw [show i = wv.steps.length - 1 by omega]; exact restAt_last wv
    rw [hrest] at hp
    rw [hli]
    have hm3 : (wv.step i).mode ≠ 3 := by
      have := ((G.walk.chain wv hw (i - 1) (by omega)).1 hprev).2
      rwa [show i - 1 + 1 = i by omega] at this
    have hmode := hok.mode
    have hend := hok.lastEnd hlast
    rcases (show (wv.step i).mode = 0 ∨ (wv.step i).mode = 1 ∨ (wv.step i).mode = 2 by omega) with
      hm | hm | hm
    · obtain ⟨hsy, -, hk⟩ := hok.stepE hm
      have hk := hk hlast
      obtain ⟨s, hs, he⟩ := node_edge G hw (i := i) (by omega) (by omega)
        (Or.inr (by rw [hk]; decide))
      rw [hk] at he
      exact ⟨fun _ => pos_val G.trie hp hs he, fun h => absurd hm h⟩
    · obtain ⟨hk, hne⟩ := hok.absK hm
      obtain ⟨s, hs, he⟩ := node_edge G hw (i := i) (by omega) (by omega)
        (Or.inr (by rcases hk with hk | hk <;> rw [hk] <;> decide))
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      exact pos_absK G.trie hp hs he hk hne (Or.inl ⟨rfl, hend⟩)
    · obtain ⟨hI0, -, -, hhv, -⟩ := hok.absB hm
      obtain ⟨n, hn, he0, hb⟩ := bmap_provided3 G.node G.walk G.balB G.rowsP hw (row_mem (by omega)) hm
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      rw [hI0, he0] at hp
      exact pos_absB G.trie hp (List.getElem?_eq_getElem hn) (G.node.wf _ (List.getElem_mem hn)) hb
        (Or.inl ⟨rfl, hhv hlast⟩)
  | succ d ih =>
    intro i hd h1 hprev hp
    have hok := row_ok G hw (i := i) (by omega)
    have hnl : (i + 1 == wv.steps.length) = false := by simp; omega
    have hm3 : (wv.step i).mode ≠ 3 := by
      have := ((G.walk.chain wv hw (i - 1) (by omega)).1 hprev).2
      rwa [show i - 1 + 1 = i by omega] at this
    have hmode := hok.mode
    have hrs := restAt_succ wv (i := i) (by omega)
    rcases (show (wv.step i).mode = 0 ∨ (wv.step i).mode = 1 ∨ (wv.step i).mode = 2 by omega) with
      hm | hm | hm
    · have hn := row_step G hw h1 (by omega) hm hp
      exact ih (i + 1) (by omega) (by omega) (by simpa using hm) hn
    · have htail := tail_mode G hw (d + 1) i (by omega) (by omega)
      obtain ⟨hk, hne⟩ := hok.absK hm
      obtain ⟨s, hs, he⟩ := node_edge G hw (i := i) (by omega) (by omega)
        (Or.inr (by rcases hk with hk | hk <;> rw [hk] <;> decide))
      refine ⟨fun h => absurd h htail, fun _ => ?_⟩
      exact pos_absK G.trie hp hs he hk hne (Or.inr ⟨_, hrs⟩)
    · have htail := tail_mode G hw (d + 1) i (by omega) (by omega)
      obtain ⟨hI0, -, -, -, hnb⟩ := hok.absB hm
      obtain ⟨hσ, hbit⟩ := hnb hnl
      obtain ⟨n, hn, he0, hb⟩ := bmap_provided3 G.node G.walk G.balB G.rowsP hw (row_mem (by omega)) hm
      refine ⟨fun h => absurd h htail, fun _ => ?_⟩
      rw [hI0, he0] at hp
      exact pos_absB G.trie hp (List.getElem?_eq_getElem hn) (G.node.wf _ (List.getElem_mem hn)) hb
        (Or.inr ⟨_, _, hrs, hσ, hbit⟩)

/-- **The walk link** (internal hypotheses). -/
theorem walk3_find_of (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf f vs) V h.rid).find wv.key3 = some (some (valOf V (f wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf f vs) V h.rid).find wv.key3 = some none) := by
  obtain ⟨h, hh, ht, hpos⟩ := walk3_pos G hw
  refine ⟨h, hh, ht, ?_⟩
  have hL := G.walk.len wv hw
  have hp1 := hpos 1 (Nat.le_refl _) (by omega) (fun j hj => by
    rw [show j = 0 by omega]; exact (G.walk.start wv hw).1)
  have hc := walk3_concl G hw (wv.steps.length - 2) 1 (by omega) (Nat.le_refl _) (G.walk.start wv hw).1 hp1
  unfold WalkR.fk WalkR.k
  by_cases hm : wv.last.mode = 0
  · simp only [hm, if_true]
    exact ⟨fun _ => hc.1 hm, fun h => absurd h (by decide)⟩
  · simp only [hm, if_false]
    exact ⟨fun h => absurd h (by decide), fun _ => hc.2 hm⟩

end Walk

/-- `hkl` from `NodeWf3.rows`: a record's key has at most `2·|ser|` nibbles, `|ser| < 2^22`. -/
theorem klen_of_rows {vs : List NodeS3} (hN : NodeWf3 vs) : ∀ s ∈ vs, klen3 s.v < P := by
  intro s hs
  have hrow := hN.rows
  have hle : (s.v.ser false).length ≤ (vs.map fun s => (s.v.ser false).length).sum :=
    le_sum_of_mem (fun s : NodeS3 => (s.v.ser false).length) hs
  have hP : 2 ^ 24 < P := by unfold P; omega
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at hle
    have := Near.Render.NodeLay.hpN_len k true
    have hser : (hpN k true).length ≤ ((NodeV3.leaf k sl m).ser false).length := by
      simp only [NodeV3.ser, List.length_append]; omega
    simp only [klen3]; omega
  | ext k kid m =>
    rw [hv] at hle
    have := Near.Render.NodeLay.hpN_len k false
    have hser : (hpN k false).length ≤ ((NodeV3.ext k kid m).ser false).length := by
      simp only [NodeV3.ser, List.length_append]; omega
    simp only [klen3]; omega
  | branch => simp only [klen3]; unfold P; omega

/-- **The v3 walk link.**  `R := recsOf f vs`.  Under the node / head / walk views, `EDGE` and
`BMAP` balance, and the structural facts `hunf` / `hpar` / `hhead` (from `PARENT` / `DIGEST`
balance), every walk has a head `h` of its instance whose root's trie answers the walk's key
as the walk's `FINAL` says. -/
theorem walk3_find {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3} {hs : List HeadE}
    {ws : List WalkR}
    (hN : NodeWf3 vs) (hH : HeadWf hs) (hW : WalkWf3 ws)
    (hE : BusBal vs hs ws B_EDGE) (hB : BusBal vs hs ws B_BMAP)
    -- discharged upstream by the v3 analogue of v1 `Link.walk_steps_lt` (`Near/Link/WalkLen.lean`):
    -- `KEYNIB` balance with the key providers bounds the walk rows
    (hT : (ws.flatMap (·.steps)).length < P)
    -- discharged upstream from `KEYNIB` balance (v1 `Link.keynib_perm`, `Near/Link/WalkKey.lean`):
    -- the key providers send nibbles `< 16` and `END`, never `SYM_START`
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    -- from `PARENT`/`DIGEST` balance (`Link3` unfolding of the record trie)
    (hunf : ∀ n (hn : n < vs.length),
      fullTree (recsOf f vs) V n = nodeTree3 V (fullTree (recsOf f vs) V) (vs[n].v.toRec3 f))
    (hpar : ∀ p (hp : p < vs.length) {c l r : Nat} {pre po : List Nat},
      (c, l, r, pre, po) ∈ vs[p].v.revealed → ∃ hc : c < vs.length, vs[c].res = r)
    -- `hpar` / `hhead`: `Link3.kid_depth` / `Link3.head_link` (`Link/Parent3.lean`)
    (hhead : ∀ h ∈ hs, ∃ hr : h.rid < vs.length, vs[h.rid].res = h.rres)
    {wv : WalkR} (hw : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf f vs) V h.rid).find wv.key3 = some (some (valOf V (f wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf f vs) V h.rid).find wv.key3 = some none) :=
  walk3_find_of
    { node := hN, head := hH, walk := hW, balE := hE, balB := hB, rowsP := hT, klen := klen_of_rows hN, sym := hsym
      trie := TrieHyp.of hunf hN.res hpar
      hd := fun h hh => by
        obtain ⟨hr, he⟩ := hhead h hh
        exact ⟨vs[h.rid], List.getElem?_eq_getElem hr, he⟩ } hw

end ZkFormal.NearV3.Walk3
