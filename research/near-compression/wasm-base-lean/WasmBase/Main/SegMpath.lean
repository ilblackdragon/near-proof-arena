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
  the roots chain `memIn = ri_0`, `ri_{k+1} = rt_k`, `memOut = rt_{nb−1}`.
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

end rows

end WasmBase
