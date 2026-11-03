import WasmBase.Main.SegRows

/-!
# WasmBase.Main.SegMpath — the MPATH Merkle update (E2E M4)

`MPATH` (table 20) has one row per touched memory block and tree level: the old path (`co → po`)
and the new path (`cn → pn`) under the same siblings `sb`, the index bit `bit`, the accumulated
index `acc` (`= blk` at the top), the level `lvl` (`= depth − 1` at the top), and the old/new roots
`ri`/`rt` carried along the block.  Each parent is one SHA-512 compression on the interface bus 103
(`h_in = IV384`, the 1024-bit node block `left48 ‖ right48 ‖ pad`, `h_out = po ‖ xo`).

There is no Lean model of the native SHA-512 chip here, so the compression is a hypothesis: a
function `node : List F → List F → List F` (18-limb digests) with `po = node left right` on every
active row, where `left`/`right` are the limb expressions `nodeBlock` actually sends
(`selL`/`selR`: `bit·sb + (1 − bit)·co` and `bit·co + (1 − bit)·sb`).

* `mpath_block`: for one block's `n` rows (`bot` … `top`), the old root is the Merkle fold of the
  old leaf under the siblings and bits, the new root likewise from the new leaf, `blk = Σ bit_l·2^l`,
  `lvl = n − 1 = depth − 1`, and `ro = 1 → rt = ri`.
* `rch_chain`: the root chain.  RCH is a permutation bus between `SEGB` (`[0] ++ memIn` out,
  `[nbt] ++ memOut` in) and the top rows (`[kb] ++ ri` in, `[kb + 1] ++ rt` out); with `kb = 0, 1, …`
  the roots chain `memIn = ri_0`, `ri_{k+1} = rt_k`, `memOut = rt_{nb−1}`, `nbt = nb`
  (`kb` of a top row = number of top rows before it, `mp_kb`; bus-level, both directions of the
  RCH balance).

Not here: the LEAF link (MPATH's bottom row receives `[blk, ro, old leaf, new leaf]` from MEMB's
padding row) and MEMB's `blk` order.  The chain itself is by `kb`, i.e. by row order; it is a
sequential composition of per-block updates (each block's siblings are those of the intermediate
tree), so it needs no `blk` order — distinctness of the touched blocks is MEMB's business.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem seg_t20 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[20]'(by simp [seg_air_len]) = Mpath.table := rfl

theorem mp_ix_names : ix Mpath.cols "act" = 0 ∧ ix Mpath.cols "bot" = 1 ∧ ix Mpath.cols "top" = 2 ∧
    ix Mpath.cols "bit" = 3 ∧ ix Mpath.cols "ro" = 4 ∧ ix Mpath.cols "blk" = 5 ∧ ix Mpath.cols "lvl" = 6 ∧
    ix Mpath.cols "acc" = 7 ∧ ix Mpath.cols "pw" = 8 ∧ ix Mpath.cols "kb" = 9 := by decide

theorem mp_ix_limbs : ∀ l, l < 18 → ix Mpath.cols s!"co{l}" = 12 + l ∧ ix Mpath.cols s!"cn{l}" = 30 + l ∧
    ix Mpath.cols s!"sb{l}" = 48 + l ∧ ix Mpath.cols s!"po{l}" = 66 + l ∧ ix Mpath.cols s!"pn{l}" = 84 + l ∧
    ix Mpath.cols s!"ri{l}" = 114 + l ∧ ix Mpath.cols s!"rt{l}" = 132 + l := by decide

/-- MPATH's constraints hold on every row. -/
theorem mp_C {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 20) : ∀ e ∈ Mpath.constraints, e.eval (tr.row pub 20 r) = 0 := by
  have ht : 20 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  intro e he
  exact H.constr 20 ht r hr e (by rw [seg_t20]; exact he)

/-- The cell `i` of row `r` of MPATH. -/
abbrev mc (tr : Trace) (r i : Nat) : F := tr.cell 20 r i

/-- An 18-limb digest starting at column `base`. -/
def mdig (tr : Trace) (r base : Nat) : List F := (List.range 18).map fun l => mc tr r (base + l)


/-! ## The Merkle model -/

/-- One Merkle step: `bit = 1` puts the current node on the right. -/
def mstep (node : List F → List F → List F) (cur sib : List F) (b : F) : List F :=
  if b = 1 then node sib cur else node cur sib

/-- The Merkle fold of a leaf under `(sibling, bit)` pairs, bottom first. -/
def mfold (node : List F → List F → List F) : List F → List (List F × F) → List F
  | cur, [] => cur
  | cur, (sib, b) :: rest => mfold node (mstep node cur sib b) rest

theorem mfold_append_one (node : List F → List F → List F) :
    ∀ (cur : List F) (A : List (List F × F)) (x : List F × F),
      mfold node cur (A ++ [x]) = mstep node (mfold node cur A) x.1 x.2
  | cur, [], x => rfl
  | cur, (sib, b) :: A, x => mfold_append_one node _ A x

/-- The left half of the node block MPATH sends for the path at `base` (`12` old, `30` new):
`bit·sb + (1 − bit)·cur` limbwise (`Mpath.nodeBlock`'s first 6 words). -/
def selL (tr : Trace) (r base : Nat) : List F :=
  (List.range 18).map fun i => mc tr r 3 * mc tr r (48 + i) + (1 - mc tr r 3) * mc tr r (base + i)
/-- The right half: `bit·cur + (1 − bit)·sb`. -/
def selR (tr : Trace) (r base : Nat) : List F :=
  (List.range 18).map fun i => mc tr r 3 * mc tr r (base + i) + (1 - mc tr r 3) * mc tr r (48 + i)

theorem sel_bit {tr : Trace} {r base : Nat} (hb : mc tr r 3 = 0 ∨ mc tr r 3 = 1) (node : List F → List F → List F) :
    node (selL tr r base) (selR tr r base) = mstep node (mdig tr r base) (mdig tr r 48) (mc tr r 3) := by
  unfold selL selR mstep mdig
  rcases hb with h | h
  · rw [h, if_neg (by decide)]
    congr 1 <;> (apply List.map_congr_left; intro i _; grind)
  · rw [h, if_pos rfl]
    congr 1 <;> (apply List.map_congr_left; intro i _; grind)

theorem mdig_eq {tr : Trace} {r r' a b : Nat} (h : ∀ l, l < 18 → mc tr r (a + l) = mc tr r' (b + l)) :
    mdig tr r a = mdig tr r' b := by
  unfold mdig; apply List.map_congr_left; intro l hl; exact h l (List.mem_range.mp hl)

/-- Number of top rows strictly before row `r`. -/
def topCount (tr : Trace) (r : Nat) : Nat := ((List.range r).filter fun r' => decide (mc tr r' 2 = 1)).length

theorem topCount_succ (tr : Trace) (r : Nat) :
    topCount tr (r + 1) = topCount tr r + (if mc tr r 2 = 1 then 1 else 0) := by
  unfold topCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : mc tr r 2 = 1 <;> simp [h]

theorem topCount_le (tr : Trace) (r : Nat) : topCount tr r ≤ r := by
  unfold topCount
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem topCount_mono (tr : Trace) {r r' : Nat} (h : r ≤ r') : topCount tr r ≤ topCount tr r' := by
  induction r' with
  | zero => have : r = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ r' ih =>
    by_cases e : r = r' + 1
    · subst e; exact Nat.le_refl _
    · have := ih (by omega); rw [topCount_succ]; omega

section rows
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
include H

theorem mp_bool {r : Nat} (hr : r < tr.height 20) :
    (mc tr r 0 = 0 ∨ mc tr r 0 = 1) ∧ (mc tr r 1 = 0 ∨ mc tr r 1 = 1) ∧ (mc tr r 2 = 0 ∨ mc tr r 2 = 1) ∧
      (mc tr r 3 = 0 ∨ mc tr r 3 = 1) ∧ (mc tr r 4 = 0 ∨ mc tr r 4 = 1) := by
  have C := mp_C H hr
  obtain ⟨a, b, t, bt, ro, -⟩ := mp_ix_names
  have cv : ∀ i, (v i).eval (tr.row pub 20 r) = mc tr r i := fun i => rfl
  have bb : ∀ n i, ix Mpath.cols n = i → Chips.bool (Mpath.c n) ∈ Mpath.constraints →
      mc tr r i = 0 ∨ mc tr r i = 1 := by
    intro n i hi hm
    have h := C _ hm
    simp only [Chips.bool, Mpath.c, hi, Expr.eval_mul', Expr.eval_sub', cv] at h
    have one : ((1 : Nat) : F) = 1 := rfl
    simp only [Expr.eval_ofNat', one] at h
    exact bool_cases h
  exact ⟨bb "act" 0 a (by simp [Mpath.constraints]), bb "bot" 1 b (by simp [Mpath.constraints]),
    bb "top" 2 t (by simp [Mpath.constraints]), bb "bit" 3 bt (by simp [Mpath.constraints]),
    bb "ro" 4 ro (by simp [Mpath.constraints])⟩


theorem mp_next {r : Nat} (hr1 : r + 1 < tr.height 20) (hact : mc tr r 0 = 1) (htop : mc tr r 2 = 0) :
    mc tr (r + 1) 0 = 1 ∧ mc tr (r + 1) 1 = 0 ∧ mc tr (r + 1) 6 = mc tr r 6 + 1 ∧
      mc tr (r + 1) 5 = mc tr r 5 ∧ mc tr (r + 1) 4 = mc tr r 4 ∧ mc tr (r + 1) 9 = mc tr r 9 ∧
      mc tr (r + 1) 8 = 2 * mc tr r 8 ∧ mc tr (r + 1) 7 = mc tr r 7 + 2 * mc tr r 8 * mc tr (r + 1) 3 ∧
      ∀ l, l < 18 → mc tr (r + 1) (12 + l) = mc tr r (66 + l) ∧ mc tr (r + 1) (30 + l) = mc tr r (84 + l) ∧
        mc tr (r + 1) (114 + l) = mc tr r (114 + l) ∧ mc tr (r + 1) (132 + l) = mc tr r (132 + l) := by
  have C := mp_C H (Nat.lt_of_succ_lt hr1)
  obtain ⟨ia, ib, it, ibt, iro, iblk, ilvl, iacc, ipw, ikb⟩ := mp_ix_names
  have hl : (r + 1 == tr.height 20) = false := by simp; omega
  have hn : (r + 1) % tr.height 20 = r + 1 := Nat.mod_eq_of_lt hr1
  have one : ((1 : Nat) : F) = 1 := rfl
  have two : ((2 : Nat) : F) = 2 := rfl
  have tr1 : Expr.trans.eval (tr.row pub 20 r) = 1 := by simp [Expr.eval, Trace.row, hl]
  have cx : ∀ i, (Chips.v i).eval (tr.row pub 20 r) = mc tr r i := fun i => rfl
  -- a `notTop` constraint `trans·act·(1 − top)·Z = 0` gives `Z = 0`
  have nt : ∀ Z : Expr, Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * Z ∈ Mpath.constraints →
      Z.eval (tr.row pub 20 r) = 0 := by
    intro Z hZ
    have h := C _ hZ
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Mpath.c, ia, it, cx, tr1, hact, htop,
      one] at h
    grind
  have nx : ∀ i, (Chips.nv i).eval (tr.row pub 20 r) = mc tr (r + 1) i := by
    intro i; simp only [Chips.nv, Expr.eval_nxt, Trace.row, hn]
  have g := fun (Z : Expr) (hZ : Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * Z ∈ Mpath.constraints) =>
    nt Z hZ
  have e1 := g (1 - Mpath.n "act") (by simp [Mpath.constraints])
  have e2 := g (Mpath.n "bot") (by simp [Mpath.constraints])
  have e3 := g (Mpath.n "lvl" - Mpath.c "lvl" - 1) (by simp [Mpath.constraints])
  have e4 := g (Mpath.n "blk" - Mpath.c "blk") (by simp [Mpath.constraints])
  have e5 := g (Mpath.n "ro" - Mpath.c "ro") (by simp [Mpath.constraints])
  have e6 := g (Mpath.n "kb" - Mpath.c "kb") (by simp [Mpath.constraints])
  have e7 := g (Mpath.n "pw" - 2 * Mpath.c "pw") (by simp [Mpath.constraints])
  have e8 := g (Mpath.n "acc" - Mpath.c "acc" - 2 * Mpath.c "pw" * Mpath.n "bit") (by simp [Mpath.constraints])
  simp only [Mpath.n, Mpath.c, ia, ib, it, ibt, iro, iblk, ilvl, iacc, ipw, ikb, Expr.eval_sub', Expr.eval_mul',
    Expr.eval_ofNat', nx, cx, one, two] at e1 e2 e3 e4 e5 e6 e7 e8
  refine ⟨by grind, e2, by grind, by grind, by grind, by grind, by grind, by grind, ?_⟩
  intro l hl18
  obtain ⟨jco, jcn, -, jpo, jpn, jri, jrt⟩ := mp_ix_limbs l hl18
  have mem : ∀ Z, Z ∈ ((List.range 18).flatMap fun l =>
      [Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"co{l}" - Mpath.c s!"po{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"cn{l}" - Mpath.c s!"pn{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"ri{l}" - Mpath.c s!"ri{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"rt{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "top" * (Mpath.c s!"po{l}" - Mpath.c s!"ri{l}"), Mpath.c "top" * (Mpath.c s!"pn{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "ro" * (Mpath.c s!"pn{l}" - Mpath.c s!"po{l}")]) → Z ∈ Mpath.constraints := by
    intro Z hZ; unfold Mpath.constraints; exact List.mem_append_right _ hZ
  have f1 := g (Mpath.n s!"co{l}" - Mpath.c s!"po{l}") (mem _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl18, by simp⟩))
  have f2 := g (Mpath.n s!"cn{l}" - Mpath.c s!"pn{l}") (mem _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl18, by simp⟩))
  have f3 := g (Mpath.n s!"ri{l}" - Mpath.c s!"ri{l}") (mem _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl18, by simp⟩))
  have f4 := g (Mpath.n s!"rt{l}" - Mpath.c s!"rt{l}") (mem _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl18, by simp⟩))
  simp only [Mpath.n, Mpath.c, jco, jcn, jpo, jpn, jri, jrt, Expr.eval_sub', nx, cx] at f1 f2 f3 f4
  exact ⟨by grind, by grind, by grind, by grind⟩

theorem mp_local {r : Nat} (hr : r < tr.height 20) :
    (mc tr r 1 = 1 → mc tr r 6 = 0 ∧ mc tr r 8 = 1 ∧ mc tr r 7 = mc tr r 3) ∧
    (mc tr r 2 = 1 → mc tr r 6 = pub.getD pubDepth 0 - 1 ∧ mc tr r 7 = mc tr r 5 ∧
      ∀ l, l < 18 → mc tr r (66 + l) = mc tr r (114 + l) ∧ mc tr r (84 + l) = mc tr r (132 + l)) ∧
    (mc tr r 4 = 1 → ∀ l, l < 18 → mc tr r (84 + l) = mc tr r (66 + l)) ∧
    (mc tr r 0 = 0 → mc tr r 1 = 0 ∧ mc tr r 2 = 0) := by
  have C := mp_C H hr
  obtain ⟨ia, ib, it, ibt, iro, iblk, ilvl, iacc, ipw, ikb⟩ := mp_ix_names
  have one : ((1 : Nat) : F) = 1 := rfl
  have cx : ∀ i, (Chips.v i).eval (tr.row pub 20 r) = mc tr r i := fun i => rfl
  have px : ∀ i, (Chips.pv i).eval (tr.row pub 20 r) = pub.getD i 0 := by
    intro i; simp [Chips.pv, Expr.eval_pub, Trace.row]
  have sel : ∀ (a : String) (i : Nat) (Z : Expr), ix Mpath.cols a = i → Mpath.c a * Z ∈ Mpath.constraints →
      mc tr r i = 1 → Z.eval (tr.row pub 20 r) = 0 := by
    intro a i Z hi hm h1
    have h := C _ hm
    simp only [Expr.eval_mul', Mpath.c, hi, cx, h1] at h
    grind
  have mem : ∀ l Z, l < 18 → Z ∈ ((List.range 18).flatMap fun l =>
      [Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"co{l}" - Mpath.c s!"po{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"cn{l}" - Mpath.c s!"pn{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"ri{l}" - Mpath.c s!"ri{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"rt{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "top" * (Mpath.c s!"po{l}" - Mpath.c s!"ri{l}"), Mpath.c "top" * (Mpath.c s!"pn{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "ro" * (Mpath.c s!"pn{l}" - Mpath.c s!"po{l}")]).filter (fun Z' => decide (Z' = Z)) →
      Z ∈ Mpath.constraints := by
    intro l Z _ hZ; unfold Mpath.constraints
    exact List.mem_append_right _ (List.mem_filter.mp hZ).1
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h0 => ?_⟩
  · have a := sel "bot" 1 (Mpath.c "lvl") ib (by simp [Mpath.constraints]) h1
    have b := sel "bot" 1 (Mpath.c "pw" - 1) ib (by simp [Mpath.constraints]) h1
    have c := sel "bot" 1 (Mpath.c "acc" - Mpath.c "bit") ib (by simp [Mpath.constraints]) h1
    simp only [Mpath.c, ilvl, ipw, iacc, ibt, Expr.eval_sub', Expr.eval_ofNat', cx, one] at a b c
    exact ⟨a, by grind, by grind⟩
  · have a := sel "top" 2 (Mpath.c "lvl" - Chips.pv pubDepth + 1) it (by simp [Mpath.constraints]) h1
    have b := sel "top" 2 (Mpath.c "acc" - Mpath.c "blk") it (by simp [Mpath.constraints]) h1
    simp only [Mpath.c, ilvl, iacc, iblk, Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', cx, px, one] at a b
    refine ⟨by grind, by grind, fun l hl => ?_⟩
    obtain ⟨-, -, -, jpo, jpn, jri, jrt⟩ := mp_ix_limbs l hl
    have hm : ∀ Z, Z ∈ ((List.range 18).flatMap fun l =>
      [Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"co{l}" - Mpath.c s!"po{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"cn{l}" - Mpath.c s!"pn{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"ri{l}" - Mpath.c s!"ri{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"rt{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "top" * (Mpath.c s!"po{l}" - Mpath.c s!"ri{l}"), Mpath.c "top" * (Mpath.c s!"pn{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "ro" * (Mpath.c s!"pn{l}" - Mpath.c s!"po{l}")]) → Z ∈ Mpath.constraints := by
      intro Z hZ; unfold Mpath.constraints; exact List.mem_append_right _ hZ
    have c := sel "top" 2 (Mpath.c s!"po{l}" - Mpath.c s!"ri{l}") it
      (hm _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, by simp⟩)) h1
    have d := sel "top" 2 (Mpath.c s!"pn{l}" - Mpath.c s!"rt{l}") it
      (hm _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, by simp⟩)) h1
    simp only [Mpath.c, jpo, jpn, jri, jrt, Expr.eval_sub', cx] at c d
    exact ⟨by grind, by grind⟩
  · intro l hl
    obtain ⟨-, -, -, jpo, jpn, -, -⟩ := mp_ix_limbs l hl
    have hm : ∀ Z, Z ∈ ((List.range 18).flatMap fun l =>
      [Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"co{l}" - Mpath.c s!"po{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"cn{l}" - Mpath.c s!"pn{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"ri{l}" - Mpath.c s!"ri{l}"),
       Expr.trans * Mpath.c "act" * (1 - Mpath.c "top") * (Mpath.n s!"rt{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "top" * (Mpath.c s!"po{l}" - Mpath.c s!"ri{l}"), Mpath.c "top" * (Mpath.c s!"pn{l}" - Mpath.c s!"rt{l}"),
       Mpath.c "ro" * (Mpath.c s!"pn{l}" - Mpath.c s!"po{l}")]) → Z ∈ Mpath.constraints := by
      intro Z hZ; unfold Mpath.constraints; exact List.mem_append_right _ hZ
    have c := sel "ro" 4 (Mpath.c s!"pn{l}" - Mpath.c s!"po{l}") iro
      (hm _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, by simp⟩)) h1
    simp only [Mpath.c, jpo, jpn, Expr.eval_sub', cx] at c
    grind
  · have a := C ((1 - Mpath.c "act") * Mpath.c "bot") (by simp [Mpath.constraints])
    have b := C ((1 - Mpath.c "act") * Mpath.c "top") (by simp [Mpath.constraints])
    simp only [Mpath.c, ia, ib, it, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cx, one, h0] at a b
    exact ⟨by grind, by grind⟩

theorem mp_edges {r : Nat} (hr : r < tr.height 20) :
    (r = 0 → mc tr r 0 = 1 → mc tr r 1 = 1 ∧ mc tr r 9 = 0) ∧
    (r + 1 < tr.height 20 → mc tr r 2 = 1 → mc tr (r + 1) 0 = 1 →
      mc tr (r + 1) 1 = 1 ∧ mc tr (r + 1) 9 = mc tr r 9 + 1) ∧
    (r + 1 < tr.height 20 → mc tr r 0 = 0 → mc tr (r + 1) 0 = 0) ∧
    (r + 1 = tr.height 20 → mc tr r 0 = 1 → mc tr r 2 = 1) := by
  have C := mp_C H hr
  obtain ⟨ia, ib, it, ibt, iro, iblk, ilvl, iacc, ipw, ikb⟩ := mp_ix_names
  have one : ((1 : Nat) : F) = 1 := rfl
  have cx : ∀ i, (Chips.v i).eval (tr.row pub 20 r) = mc tr r i := fun i => rfl
  refine ⟨fun h0 ha => ?_, fun hr1 ht hna => ?_, fun hr1 h0 => ?_, fun hl ha => ?_⟩
  · subst h0
    have f1 : Expr.first.eval (tr.row pub 20 0) = 1 := by simp [Expr.eval, Trace.row]
    have a := C (Expr.first * Mpath.c "act" * (1 - Mpath.c "bot")) (by simp [Mpath.constraints])
    have b := C (Expr.first * Mpath.c "act" * Mpath.c "kb") (by simp [Mpath.constraints])
    simp only [Mpath.c, ia, ib, ikb, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cx, one, f1, ha] at a b
    exact ⟨by grind, by grind⟩
  · have hl : (r + 1 == tr.height 20) = false := by simp; omega
    have tr1 : Expr.trans.eval (tr.row pub 20 r) = 1 := by simp [Expr.eval, Trace.row, hl]
    have nx : ∀ i, (Chips.nv i).eval (tr.row pub 20 r) = mc tr (r + 1) i := by
      intro i; simp only [Chips.nv, Expr.eval_nxt, Trace.row, Nat.mod_eq_of_lt hr1]
    have a := C (Expr.trans * Mpath.c "top" * Mpath.n "act" * (1 - Mpath.n "bot")) (by simp [Mpath.constraints])
    have b := C (Expr.trans * Mpath.c "top" * Mpath.n "act" * (Mpath.n "kb" - Mpath.c "kb" - 1))
      (by simp [Mpath.constraints])
    simp only [Mpath.c, Mpath.n, ia, ib, it, ikb, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cx, nx, one,
      tr1, ht, hna] at a b
    exact ⟨by grind, by grind⟩
  · have hl : (r + 1 == tr.height 20) = false := by simp; omega
    have tr1 : Expr.trans.eval (tr.row pub 20 r) = 1 := by simp [Expr.eval, Trace.row, hl]
    have nx : ∀ i, (Chips.nv i).eval (tr.row pub 20 r) = mc tr (r + 1) i := by
      intro i; simp only [Chips.nv, Expr.eval_nxt, Trace.row, Nat.mod_eq_of_lt hr1]
    have a := C (Expr.trans * (1 - Mpath.c "act") * Mpath.n "act") (by simp [Mpath.constraints])
    simp only [Mpath.c, Mpath.n, ia, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cx, nx, one, tr1, h0] at a
    grind
  · have l1 : Expr.last.eval (tr.row pub 20 r) = 1 := by simp [Expr.eval, Trace.row, hl]
    have a := C (Expr.last * Mpath.c "act" * (1 - Mpath.c "top")) (by simp [Mpath.constraints])
    simp only [Mpath.c, ia, it, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cx, one, l1, ha] at a
    grind


/-- **One block's Merkle update.**  Rows `r0 … r0 + n − 1` of MPATH: `act` and `bot` on the first,
`top = 0` until the last, `top = 1` on the last.  If every row's old parent is the compression of
its node block (`chipO`), and the new one too when the block is not read-only (`chipN`), then:
* the old root `ri` is the Merkle fold of the old leaf `co(r0)` under the siblings and bits,
* the new root `rt` is the fold of the new leaf `cn(r0)` (not read-only), or `rt = ri` (read-only),
* `blk = Σ_l bit_l · 2^l` and `n − 1 = depth − 1` (field), and `kb`, `ro` are constant on the block. -/
theorem mpath_block (node : List F → List F → List F) {r0 n : Nat} (hn : 0 < n)
    (hh : r0 + n ≤ tr.height 20) (hact : mc tr r0 0 = 1) (hbot : mc tr r0 1 = 1)
    (hmid : ∀ l, l + 1 < n → mc tr (r0 + l) 2 = 0) (htop : mc tr (r0 + (n - 1)) 2 = 1)
    (chipO : ∀ l, l < n → mdig tr (r0 + l) 66 = node (selL tr (r0 + l) 12) (selR tr (r0 + l) 12))
    (chipN : mc tr r0 4 = 0 → ∀ l, l < n → mdig tr (r0 + l) 84 = node (selL tr (r0 + l) 30) (selR tr (r0 + l) 30)) :
    mdig tr (r0 + (n - 1)) 114 =
      mfold node (mdig tr r0 12) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)) ∧
    (mc tr r0 4 = 0 → mdig tr (r0 + (n - 1)) 132 =
      mfold node (mdig tr r0 30) ((List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3))) ∧
    (mc tr r0 4 = 1 → mdig tr (r0 + (n - 1)) 132 = mdig tr (r0 + (n - 1)) 114) ∧
    mc tr r0 5 = ((List.range n).map fun l => mc tr (r0 + l) 3 * ((2 ^ l : Nat) : F)).foldr (· + ·) 0 ∧
    (((n - 1 : Nat) : F) = pub.getD pubDepth 0 - 1) ∧
    mc tr (r0 + (n - 1)) 9 = mc tr r0 9 ∧ mc tr (r0 + (n - 1)) 4 = mc tr r0 4 := by
  have sumF : ∀ l, ((List.range (l + 1)).map fun j => mc tr (r0 + j) 3 * ((2 ^ j : Nat) : F)).foldr (· + ·) 0 =
      ((List.range l).map fun j => mc tr (r0 + j) 3 * ((2 ^ j : Nat) : F)).foldr (· + ·) 0 +
        mc tr (r0 + l) 3 * ((2 ^ l : Nat) : F) := by
    intro l
    rw [List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    generalize mc tr (r0 + l) 3 * ((2 ^ l : Nat) : F) = z
    induction ((List.range l).map fun j => mc tr (r0 + j) 3 * ((2 ^ j : Nat) : F)) with
    | nil => simp only [List.foldr_nil]; grind
    | cons a t ih => simp only [List.foldr_cons, ih]; grind
  -- the invariant along the block
  have inv : ∀ l, l < n →
      mc tr (r0 + l) 0 = 1 ∧ mc tr (r0 + l) 6 = ((l : Nat) : F) ∧ mc tr (r0 + l) 8 = ((2 ^ l : Nat) : F) ∧
      mc tr (r0 + l) 7 = ((List.range (l + 1)).map fun j => mc tr (r0 + j) 3 * ((2 ^ j : Nat) : F)).foldr (· + ·) 0 ∧
      mc tr (r0 + l) 5 = mc tr r0 5 ∧ mc tr (r0 + l) 4 = mc tr r0 4 ∧ mc tr (r0 + l) 9 = mc tr r0 9 ∧
      mdig tr (r0 + l) 12 = mfold node (mdig tr r0 12) ((List.range l).map fun j => (mdig tr (r0 + j) 48, mc tr (r0 + j) 3)) ∧
      (mc tr r0 4 = 0 → mdig tr (r0 + l) 30 =
        mfold node (mdig tr r0 30) ((List.range l).map fun j => (mdig tr (r0 + j) 48, mc tr (r0 + j) 3))) := by
    intro l
    induction l with
    | zero =>
      intro _
      obtain ⟨b1, -, -, -⟩ := mp_local H (r := r0) (by omega)
      obtain ⟨l0, p1, a1⟩ := b1 hbot
      refine ⟨hact, by rw [Nat.add_zero, l0]; rfl, by rw [Nat.add_zero, p1]; rfl, ?_, rfl, rfl, rfl,
        by simp [mfold], fun _ => by simp [mfold]⟩
      rw [Nat.add_zero, a1]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, Nat.add_zero, Nat.pow_zero]
      have : ((1 : Nat) : F) = 1 := rfl
      rw [this]; grind
    | succ l ih =>
      intro hl
      obtain ⟨ha, hlv, hpw, hacc, hblk, hro, hkb, hco, hcn⟩ := ih (by omega)
      have hr1 : r0 + l + 1 < tr.height 20 := by omega
      obtain ⟨na, -, nlv, nblk, nro, nkb, npw, nacc, nlimb⟩ := mp_next H hr1 ha (hmid l hl)
      have hbool := (mp_bool H (r := r0 + l) (by omega)).2.2.2.1
      refine ⟨by rw [← Nat.add_assoc]; exact na, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← Nat.add_assoc, nlv, hlv, Lean.Grind.Semiring.natCast_add]; rfl
      · rw [← Nat.add_assoc, npw, hpw, Nat.pow_succ, Lean.Grind.Semiring.natCast_mul]; grind
      · rw [← Nat.add_assoc, nacc, hacc, hpw, sumF (l + 1), Nat.add_assoc]
        have : ((2 ^ (l + 1) : Nat) : F) = 2 * ((2 ^ l : Nat) : F) := by
          rw [Nat.pow_succ, Lean.Grind.Semiring.natCast_mul]; grind
        rw [this]; grind
      · rw [← Nat.add_assoc, nblk, hblk]
      · rw [← Nat.add_assoc, nro, hro]
      · rw [← Nat.add_assoc, nkb, hkb]
      · rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, mfold_append_one, ← hco,
          ← sel_bit hbool node, ← chipO l (by omega), ← Nat.add_assoc]
        exact mdig_eq fun i hi => (nlimb i hi).1
      · intro h0
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, mfold_append_one, ← hcn h0,
          ← sel_bit hbool node, ← chipN h0 l (by omega), ← Nat.add_assoc]
        exact mdig_eq fun i hi => (nlimb i hi).2.1
  obtain ⟨ha, hlv, -, hacc, hblk, hro, hkb, hco, hcn⟩ := inv (n - 1) (by omega)
  obtain ⟨-, t1, r1, -⟩ := mp_local H (r := r0 + (n - 1)) (by omega)
  obtain ⟨tl, tacc, tlimb⟩ := t1 htop
  have hbool := (mp_bool H (r := r0 + (n - 1)) (by omega)).2.2.2.1
  have hsibs : (List.range n).map (fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)) =
      (List.range (n - 1)).map (fun j => (mdig tr (r0 + j) 48, mc tr (r0 + j) 3)) ++
      [(mdig tr (r0 + (n - 1)) 48, mc tr (r0 + (n - 1)) 3)] := by
    conv => lhs; rw [show n = n - 1 + 1 by omega, List.range_succ, List.map_append]
    rfl
  refine ⟨?_, fun h0 => ?_, fun h1 => ?_, ?_, ?_, hkb, hro⟩
  · rw [hsibs, mfold_append_one, ← hco, ← sel_bit hbool node, ← chipO (n - 1) (by omega)]
    exact (mdig_eq fun i hi => (tlimb i hi).1).symm
  · rw [hsibs, mfold_append_one, ← hcn h0, ← sel_bit hbool node, ← chipN h0 (n - 1) (by omega)]
    exact (mdig_eq fun i hi => (tlimb i hi).2).symm
  · have hro1 : mc tr (r0 + (n - 1)) 4 = 1 := by rw [hro, h1]
    exact mdig_eq fun i hi => by rw [← (tlimb i hi).2, ← (tlimb i hi).1, r1 hro1 i hi]
  · rw [← hblk, ← tacc, hacc, show n - 1 + 1 = n by omega]
  · rw [← hlv, tl]


/-- Active rows form a prefix, and on an active row `kb` is the number of top rows before it. -/
theorem mp_kb {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    (∀ r', r' ≤ r → mc tr r' 0 = 1) ∧ mc tr r 9 = ((topCount tr r : Nat) : F) := by
  induction r with
  | zero =>
    refine ⟨fun r' h => by have : r' = 0 := by omega
                           subst this; exact ha, ?_⟩
    rw [((mp_edges H hr).1 rfl ha).2]; rfl
  | succ r ih =>
    have ha' : mc tr r 0 = 1 := by
      rcases (mp_bool H (r := r) (by omega)).1 with h | h
      · exact absurd ((mp_edges H (r := r) (by omega)).2.2.1 hr h ▸ ha) (by decide)
      · exact h
    obtain ⟨hpre, hkb⟩ := ih (by omega) ha'
    refine ⟨fun r' h => ?_, ?_⟩
    · by_cases e : r' = r + 1
      · subst e; exact ha
      · exact hpre r' (by omega)
    · rw [topCount_succ]
      rcases (mp_bool H (r := r) (by omega)).2.2.1 with ht | ht
      · obtain ⟨-, -, -, -, -, nkb, -⟩ := mp_next H hr ha' ht
        rw [nkb, hkb, ht, if_neg (by decide), Nat.add_zero]
      · rw [((mp_edges H (r := r) (by omega)).2.1 hr ht ha).2, hkb, ht, if_pos rfl,
          Lean.Grind.Semiring.natCast_add]; rfl

/-- A top row is active. -/
theorem mp_top_act {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 2 = 1) : mc tr r 0 = 1 := by
  rcases (mp_bool H hr).1 with h | h
  · exact absurd ((mp_local H hr).2.2.2 h).2 (by rw [ht]; decide)
  · exact h

/-- `kb` of a top row, as a natural: the number of top rows before it. -/
theorem mp_kb_top {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 2 = 1) :
    (mc tr r 9).toNat = topCount tr r := by
  rw [(mp_kb H hr (mp_top_act H hr ht)).2, Fp.toNat_cast_of_lt]
  have := topCount_le tr r
  have hh := H.heightLe 20 (by simp [seg_air_len])
  unfold maxLogHeight at hh
  rw [P_val]; omega
end rows

/-! ## The root chain (bus RCH = 16) -/

theorem segb_rch : Segb.table.inters.filter (fun i => i.bus = 16) =
    [⟨busRch, true, .first, [0] ++ Segb.pubs pubMemIn 18⟩,
     ⟨busRch, false, .first, [Segb.c "nbt"] ++ Segb.pubs pubMemOut 18⟩] := by decide

theorem mpath_rch : Mpath.table.inters.filter (fun i => i.bus = 16) =
    [⟨busRch, false, Mpath.c "top", [Mpath.c "kb"] ++ Mpath.dig "ri"⟩,
     ⟨busRch, true, Mpath.c "top", [Mpath.c "kb" + 1] ++ Mpath.dig "rt"⟩] := by decide

theorem segb_ix_nbt : ix Segb.cols "nbt" = 3 := by decide

theorem seg_rch_tables (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 0 → t ≠ 20 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus ≠ 16 := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 0 → t ≠ 20 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != 16) = true := by
    decide
  have h : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 0 → t ≠ 20 →
      ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != 16) = true := by
    simp only [e]; exact h0
  intro t ht h0' h20 i hi
  have := List.all_eq_true.mp (h t ht h0' h20) i hi
  simpa using this

theorem seg_t0 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[0]'(by simp [seg_air_len]) = Segb.table := rfl

/-- The 18 limbs of a public digest. -/
def pubDig (pub : List F) (b : Nat) : List F := (List.range 18).map fun i => pub.getD (b + i) 0

theorem pubs_eval (rw : Row) (pub : List F) (hp : rw.pub = fun i => pub.getD i 0) (b : Nat) :
    (Segb.pubs b 18).map (·.eval rw) = pubDig pub b := by
  simp only [Segb.pubs, pubDig, List.map_map]
  apply List.map_congr_left; intro i _
  simp [Chips.pv, Expr.eval_pub, hp]

theorem dig_eval (tr : Trace) (pub : List F) (r : Nat) (base : Nat) (s : String)
    (hix : ∀ l, l < 18 → ix Mpath.cols s!"{s}{l}" = base + l) :
    (Mpath.dig s).map (·.eval (tr.row pub 20 r)) = mdig tr r base := by
  simp only [Mpath.dig, names, mdig, List.map_map]
  apply List.map_congr_left; intro l hl
  simp only [Function.comp, Mpath.c, hix l (List.mem_range.mp hl)]
  rfl

/-- A send with count 1 on a bus whose send counts are bits has a matching receive with a nonzero
count. -/
theorem send_has_recv {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ o' ∈ occs A tr pub, o'.1 = b ∧ o'.2.1 = false ∧ o'.2.2.1 = o.2.2.1 ∧ o'.2.2.2 ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : busNat A tr pub b false o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' =>
      Classical.byContradiction fun hc' => hn ⟨o', ho', hb', hs', hm', hc'⟩
  have hbal := H.balance b o.2.2.1
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_lt H b true o.2.2.1 hbit
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

theorem first_toNat (tr : Trace) (pub : List F) (r : Nat) : (Expr.first.eval (tr.row pub 0 r)).toNat ≤ 1 ∧
    ((Expr.first.eval (tr.row pub 0 r)).toNat ≠ 0 → r = 0) := by
  by_cases h : r = 0
  · subst h; simp [Expr.eval, Trace.row]; decide
  · have : Expr.first.eval (tr.row pub 0 r) = 0 := by simp [Expr.eval, Trace.row, h]
    rw [this]; exact ⟨by decide, fun h' => absurd rfl h'⟩

theorem cons_append_inj {a b : F} {L L' : List F} (h : [a] ++ L = [b] ++ L') : a = b ∧ L = L' := by
  simpa using h

section chain
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **Every RCH occurrence**: SEGB's `[0] ++ memIn` (out) / `[nbt] ++ memOut` (in) with count
`first`, or a MPATH row's `[kb] ++ ri` (in) / `[kb + 1] ++ rt` (out) with count `top`. -/
theorem rch_occ {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = 16) :
    (∃ r, r < tr.height 0 ∧
      (o = (16, true, [0] ++ pubDig pub pubMemIn, (Expr.first.eval (tr.row pub 0 r)).toNat) ∨
       o = (16, false, [tr.cell 0 r 3] ++ pubDig pub pubMemOut, (Expr.first.eval (tr.row pub 0 r)).toNat))) ∨
    (∃ r, r < tr.height 20 ∧
      (o = (16, false, [mc tr r 9] ++ mdig tr r 114, (mc tr r 2).toNat) ∨
       o = (16, true, [mc tr r 9 + 1] ++ mdig tr r 132, (mc tr r 2).toNat))) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb
  have hp : (tr.row pub t r).pub = fun i => pub.getD i 0 := rfl
  by_cases h0 : t = 0
  · subst h0
    rw [seg_t0] at hi
    have hm : i ∈ Segb.table.inters.filter (fun i => i.bus = 16) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [segb_rch] at hm
    left; refine ⟨r, hr, ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · left
      simp only [List.map_append, List.map_cons, List.map_nil, Expr.eval_ofNat']
      rw [pubs_eval _ pub hp]; rfl
    · right
      simp only [List.map_append, List.map_cons, List.map_nil, Segb.c, segb_ix_nbt]
      rw [pubs_eval _ pub hp]; rfl
  by_cases h20 : t = 20
  · subst h20
    rw [seg_t20] at hi
    have hm : i ∈ Mpath.table.inters.filter (fun i => i.bus = 16) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [mpath_rch] at hm
    right; refine ⟨r, hr, ?_⟩
    obtain ⟨-, -, it, -, -, -, -, -, -, ikb⟩ := mp_ix_names
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · left
      simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, it, ikb]
      rw [dig_eval tr pub r 114 "ri" (fun l hl => (mp_ix_limbs l hl).2.2.2.2.2.1)]; rfl
    · right
      simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, it, ikb, Expr.eval_add',
        Expr.eval_ofNat']
      rw [dig_eval tr pub r 132 "rt" (fun l hl => (mp_ix_limbs l hl).2.2.2.2.2.2)]; rfl
  · exact absurd hb (seg_rch_tables nloc ngl t ht h0 h20 i hi)

theorem top_toNat {r : Nat} (hr : r < tr.height 20) : (mc tr r 2).toNat ≤ 1 ∧
    ((mc tr r 2).toNat ≠ 0 → mc tr r 2 = 1) := by
  rcases (mp_bool H hr).2.2.1 with h | h <;> rw [h]
  · exact ⟨by decide, fun h' => absurd rfl h'⟩
  · exact ⟨by decide, fun _ => rfl⟩

theorem rch_bits (s : Bool) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = 16 → o.2.1 = s → o.2.2.2 ≤ 1 := by
  intro o ho hb _
  rcases rch_occ H ho hb with ⟨r, -, rfl | rfl⟩ | ⟨r, hr, rfl | rfl⟩
  · exact (first_toNat tr pub r).1
  · exact (first_toNat tr pub r).1
  · exact (top_toNat H hr).1
  · exact (top_toNat H hr).1

/-- `kb` of a top row is small. -/
theorem kb_lt {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 2 = 1) : (mc tr r 9).toNat < 2 ^ 24 := by
  rw [mp_kb_top H hr ht]
  have := topCount_le tr r
  have hh := H.heightLe 20 (by simp [seg_air_len]); unfold maxLogHeight at hh
  omega

theorem kb_succ_toNat {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 2 = 1) :
    (mc tr r 9 + 1).toNat = (mc tr r 9).toNat + 1 := by
  have := kb_lt H hr ht
  conv => lhs; rw [← Fp.cast_toNat (mc tr r 9)]
  rw [show (1 : F) = ((1 : Nat) : F) from rfl, ← Lean.Grind.Semiring.natCast_add,
    Fp.toNat_cast_of_lt (by rw [P_val]; omega)]

/-- Two top rows with the same `kb` are the same row. -/
theorem top_unique {r r' : Nat} (hr : r < tr.height 20) (hr' : r' < tr.height 20) (ht : mc tr r 2 = 1)
    (ht' : mc tr r' 2 = 1) (h : topCount tr r = topCount tr r') : r = r' := by
  rcases Nat.lt_trichotomy r r' with l | e | l
  · have := topCount_mono tr (show r + 1 ≤ r' by omega)
    rw [topCount_succ, ht, if_pos rfl] at this; omega
  · exact e
  · have := topCount_mono tr (show r' + 1 ≤ r by omega)
    rw [topCount_succ, ht', if_pos rfl] at this; omega

/-- **The root chain.**  On MPATH's top rows (one per touched block, `kb` = the block's position):
* the first block's old root is `memIn`;
* block `k + 1`'s old root is block `k`'s new root;
* the last block's new root is `memOut`, and `nbt` is the number of blocks;
* with no touched block, `memOut = memIn` and `nbt = 0`. -/
theorem rch_chain :
    (∀ r, r < tr.height 20 → mc tr r 2 = 1 → topCount tr r = 0 → mdig tr r 114 = pubDig pub pubMemIn) ∧
    (∀ r r', r < tr.height 20 → r' < tr.height 20 → mc tr r 2 = 1 → mc tr r' 2 = 1 →
      topCount tr r' = topCount tr r + 1 → mdig tr r' 114 = mdig tr r 132) ∧
    (∀ r, r < tr.height 20 → mc tr r 2 = 1 → topCount tr r + 1 = topCount tr (tr.height 20) →
      pubDig pub pubMemOut = mdig tr r 132 ∧ tr.cell 0 0 3 = ((topCount tr (tr.height 20) : Nat) : F)) ∧
    (topCount tr (tr.height 20) = 0 → pubDig pub pubMemOut = pubDig pub pubMemIn ∧ tr.cell 0 0 3 = 0) := by
  have hh := H.heightLe 20 (by simp [seg_air_len]); unfold maxLogHeight at hh
  have hP' := P_val
  have bitsR := rch_bits H false
  have bitsS := rch_bits H true
  -- MPATH receive of top row `r` and its sender
  have recvM : ∀ r, r < tr.height 20 → mc tr r 2 = 1 →
      (mc tr r 9 = 0 ∧ mdig tr r 114 = pubDig pub pubMemIn) ∨
      (∃ r'', r'' < tr.height 20 ∧ mc tr r'' 2 = 1 ∧ mc tr r 9 = mc tr r'' 9 + 1 ∧ mdig tr r 114 = mdig tr r'' 132) := by
    intro r hr ht
    have hq : ((16, false, [mc tr r 9] ++ mdig tr r 114, (mc tr r 2).toNat) : Occ) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
      refine mem_occs.mpr ⟨20, by simp [seg_air_len], r, hr,
        ⟨busRch, false, Mpath.c "top", [Mpath.c "kb"] ++ Mpath.dig "ri"⟩, ?_, ?_⟩
      · rw [seg_t20]; exact (List.mem_filter.mp (show _ ∈ Mpath.table.inters.filter (fun i => i.bus = 16) by
          rw [mpath_rch]; exact List.mem_cons_self)).1
      · obtain ⟨-, -, it, -, -, -, -, -, -, ikb⟩ := mp_ix_names
        simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, it, ikb]
        rw [dig_eval tr pub r 114 "ri" (fun l hl => (mp_ix_limbs l hl).2.2.2.2.2.1)]; rfl
    obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_send H 16 bitsR hq rfl rfl (by rw [ht]; rfl)
    rcases rch_occ H ho' hb' with ⟨r0, -, rfl | rfl⟩ | ⟨r'', hr'', rfl | rfl⟩
    · obtain ⟨a, b⟩ := cons_append_inj hm'
      exact Or.inl ⟨a.symm, b.symm⟩
    · simp at hs'
    · simp at hs'
    · obtain ⟨a, b⟩ := cons_append_inj hm'
      exact Or.inr ⟨r'', hr'', (top_toNat H hr'').2 hc', a.symm, b.symm⟩
  -- MPATH send of top row `r` and its receiver
  have sendM : ∀ r, r < tr.height 20 → mc tr r 2 = 1 →
      (mc tr r 9 + 1 = tr.cell 0 0 3 ∧ mdig tr r 132 = pubDig pub pubMemOut) ∨
      (∃ r'', r'' < tr.height 20 ∧ mc tr r'' 2 = 1 ∧ mc tr r'' 9 = mc tr r 9 + 1) := by
    intro r hr ht
    have hq : ((16, true, [mc tr r 9 + 1] ++ mdig tr r 132, (mc tr r 2).toNat) : Occ) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
      refine mem_occs.mpr ⟨20, by simp [seg_air_len], r, hr,
        ⟨busRch, true, Mpath.c "top", [Mpath.c "kb" + 1] ++ Mpath.dig "rt"⟩, ?_, ?_⟩
      · rw [seg_t20]; exact (List.mem_filter.mp (show _ ∈ Mpath.table.inters.filter (fun i => i.bus = 16) by
          rw [mpath_rch]; simp)).1
      · obtain ⟨-, -, it, -, -, -, -, -, -, ikb⟩ := mp_ix_names
        simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, it, ikb, Expr.eval_add',
          Expr.eval_ofNat']
        rw [dig_eval tr pub r 132 "rt" (fun l hl => (mp_ix_limbs l hl).2.2.2.2.2.2)]; rfl
    obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 16 bitsS hq rfl rfl (by rw [ht]; rfl)
    rcases rch_occ H ho' hb' with ⟨r0, -, rfl | rfl⟩ | ⟨r'', hr'', rfl | rfl⟩
    · simp at hs'
    · obtain ⟨a, b⟩ := cons_append_inj hm'
      have := (first_toNat tr pub r0).2 hc'; subst this
      exact Or.inl ⟨a.symm, b.symm⟩
    · obtain ⟨a, -⟩ := cons_append_inj hm'
      exact Or.inr ⟨r'', hr'', (top_toNat H hr'').2 hc', a⟩
    · simp at hs'
  refine ⟨fun r hr ht h0 => ?_, fun r r' hr hr' ht ht' hk => ?_, fun r hr ht hl => ?_, fun h0 => ?_⟩
  · rcases recvM r hr ht with ⟨-, e⟩ | ⟨r'', hr'', ht'', hk, -⟩
    · exact e
    · exfalso
      have a := congrArg Fp.toNat hk
      rw [kb_succ_toNat H hr'' ht'', mp_kb_top H hr ht, h0] at a; omega
  · rcases recvM r' hr' ht' with ⟨hz, -⟩ | ⟨r'', hr'', ht'', hk', e⟩
    · exfalso
      have a := congrArg Fp.toNat hz
      rw [mp_kb_top H hr' ht'] at a
      exact absurd (show (0 : F).toNat = 0 from rfl) (by rw [← a, hk]; omega)
    · have a := congrArg Fp.toNat hk'
      rw [kb_succ_toNat H hr'' ht'', mp_kb_top H hr' ht', mp_kb_top H hr'' ht''] at a
      rw [e, top_unique H hr'' hr ht'' ht (by omega)]
  · rcases sendM r hr ht with ⟨a, e⟩ | ⟨r'', hr'', ht'', hk⟩
    · refine ⟨e.symm, ?_⟩
      rw [← a, ← hl, (mp_kb H hr (mp_top_act H hr ht)).2, Lean.Grind.Semiring.natCast_add]; rfl
    · exfalso
      have a := congrArg Fp.toNat hk
      rw [kb_succ_toNat H hr ht, mp_kb_top H hr ht, mp_kb_top H hr'' ht''] at a
      have m1 := topCount_mono tr (show r'' + 1 ≤ tr.height 20 by omega)
      rw [topCount_succ, ht'', if_pos rfl] at m1
      omega
  · have notop : ∀ r, r < tr.height 20 → mc tr r 2 ≠ 1 := by
      intro r hr ht
      have m1 := topCount_mono tr (show r + 1 ≤ tr.height 20 by omega)
      rw [topCount_succ, ht, if_pos rfl] at m1
      omega
    have h0t : 0 < tr.height 0 := by have := H.heightPos 0 (by simp [seg_air_len]); omega
    have hq : ((16, true, [0] ++ pubDig pub pubMemIn, (Expr.first.eval (tr.row pub 0 0)).toNat) : Occ) ∈
        occs (wasmBaseSegAir nloc ngl) tr pub := by
      refine mem_occs.mpr ⟨0, by simp [seg_air_len], 0, h0t,
        ⟨busRch, true, .first, [0] ++ Segb.pubs pubMemIn 18⟩, ?_, ?_⟩
      · rw [seg_t0]; exact (List.mem_filter.mp (show _ ∈ Segb.table.inters.filter (fun i => i.bus = 16) by
          rw [segb_rch]; exact List.mem_cons_self)).1
      · simp only [List.map_append, List.map_cons, List.map_nil, Expr.eval_ofNat']
        rw [pubs_eval _ pub rfl]; rfl
    obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 16 bitsS hq rfl rfl
      (by simp [Expr.eval, Trace.row]; decide)
    rcases rch_occ H ho' hb' with ⟨r0, -, rfl | rfl⟩ | ⟨r'', hr'', rfl | rfl⟩
    · simp at hs'
    · obtain ⟨a, b⟩ := cons_append_inj hm'
      have := (first_toNat tr pub r0).2 hc'; subst this
      exact ⟨b, a⟩
    · exact absurd ((top_toNat H hr'').2 hc') (notop r'' hr'')
    · simp at hs'

end chain

#print axioms mpath_block
#print axioms rch_chain
#print axioms mp_kb

end WasmBase
