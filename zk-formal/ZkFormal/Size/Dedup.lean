import ZkFormal.Prover.BcsSize
import ZkFormal.Prover.SizeBound

/-!
# ZkFormal.Size.Dedup — the deduplicated multiproof size bound (lane `v3-size`, lever (a))

`Prover.openSize s mats = s · (4·Σ widths + 64·depth)` charges every one of the `s` query
positions a full Merkle path.  The deployed multiproof format (`Stark.Merkle.multiproof`,
honest stream `Prover.multiproofBytes`) is **sorted and deduplicated**: level by level, every
known node contributes its parent once, and a sibling digest (64 bytes) is sent only for a
parent with exactly one known child.  At parent depth `j` there are at most `min s 2^j`
parents (a strictly increasing list below `2^j`), so the shared top `⌈log₂ s⌉` levels are
charged once:

* `multiproof_size_le`: for sorted, duplicate-free `S < 2^n` with `|S| ≤ s`,
  `|multiproofBytes … S| ≤ openSizeD s mats`, where
  `openSizeD s mats = 4·Σ_{(m,w) ∈ mats} min s 2^m · w + 64·dsum s n` and
  `dsum s n = Σ_{j<n} min s 2^j` (`≤ s·n`, `dsum_le_mul`).
* `size32D : SizeStmt32D`: the honest proof (`proveTree`, 32-byte hash) has at most
  `sizeBoundD V pr.hdr` bytes (`sizeBoundD` = `sizeBound` with `openSizeD` per oracle).
* `sizeBoundD_le`: `sizeBoundD ≤ sizeBound` on every header (never worse).

The stream is the one the verifier reads: `Prover.ev_multiproof` shows the deployed reader
(`mpLeaves`, `mpUp`, `mpLevels`) consumes exactly `multiproofBytes`.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Size

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Prover

/-! ## Counting -/

/-- `dsum s n = Σ_{j<n} min s 2^j`: sibling digests of a deduplicated multiproof of `s`
positions over a tree of depth `n`. -/
def dsum (s : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => dsum s n + min s (2 ^ n)

theorem dsum_mono (s : Nat) {m : Nat} : ∀ {n : Nat}, m ≤ n → dsum s m ≤ dsum s n
  | 0, h => by rw [show m = 0 by omega]; exact Nat.le_refl _
  | n + 1, h => by
    by_cases hm : m = n + 1
    · rw [hm]; exact Nat.le_refl _
    · have := dsum_mono s (m := m) (n := n) (by omega)
      simp only [dsum]; exact Nat.le_trans this (Nat.le_add_right _ _)

theorem dsum_le_mul (s : Nat) : ∀ n, dsum s n ≤ s * n
  | 0 => by simp [dsum]
  | n + 1 => by
    have := dsum_le_mul s n
    have := Nat.min_le_left s (2 ^ n)
    simp only [dsum, Nat.mul_succ]; omega

theorem dsum_eq_sumR (s : Nat) : ∀ n, dsum s n = sumR n (fun j => min s (2 ^ j))
  | 0 => rfl
  | n + 1 => by rw [dsum, sumR_succ, dsum_eq_sumR s n]

theorem min_pow_mono (s : Nat) {a b : Nat} (h : a ≤ b) : min s (2 ^ a) ≤ min s (2 ^ b) := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  omega

/-- A strictly increasing list of naturals in `[m, N)` has at most `N - m` entries. -/
theorem length_le_of_sorted : ∀ (l : List Nat) (m N : Nat), l.Pairwise (· < ·) →
    (∀ x ∈ l, m ≤ x ∧ x < N) → l.length ≤ N - m
  | [], _, _, _, _ => by simp
  | a :: l, m, N, hs, hb => by
    have ha := hb a (by simp)
    have ih := length_le_of_sorted l (a + 1) N (List.pairwise_cons.mp hs).2
      (fun x hx => ⟨(List.pairwise_cons.mp hs).1 x hx, (hb x (by simp [hx])).2⟩)
    simp only [List.length_cons]
    have : a + 1 ≤ N := ha.2
    omega

theorem length_le_pow {l : List Nat} {k : Nat} (hs : l.Pairwise (· < ·))
    (hb : ∀ x ∈ l, x < 2 ^ k) : l.length ≤ 2 ^ k := by
  have := length_le_of_sorted l 0 (2 ^ k) hs (fun x hx => ⟨Nat.zero_le _, hb x hx⟩)
  omega

/-- Weighted version of `Prover.sum_levelWidths`. -/
theorem sum_levelWidthsW (c : Nat → Nat) (n : Nat) : ∀ mats : List (Nat × Nat),
    (∀ m ∈ mats, m.1 ≤ n) →
    sumR (n + 1) (fun k => c k * (levelWidths mats k).sum) = (mats.map fun m => c m.1 * m.2).sum
  | [], _ => by
    have : ∀ N, sumR N (fun k => c k * (levelWidths [] k).sum) = 0 := by
      intro N; induction N with
      | zero => rfl
      | succ N ih => rw [sumR_succ, ih]; simp [levelWidths]
    exact this _
  | m :: mats, h => by
    have e : (fun k => c k * (levelWidths (m :: mats) k).sum) =
        fun k => (if m.1 = k then c m.1 * m.2 else 0) + c k * (levelWidths mats k).sum := by
      funext k
      by_cases hk : m.1 = k
      · have : (levelWidths (m :: mats) k) = m.2 :: levelWidths mats k := by
          simp [levelWidths, hk]
        rw [this, ite_eq_left_of_eq_true _ _ (eq_true hk), hk, List.sum_cons, Nat.mul_add]
      · have : (levelWidths (m :: mats) k) = levelWidths mats k := by
          simp [levelWidths, hk]
        rw [this, ite_eq_right_of_eq_false _ _ (eq_false hk), Nat.zero_add]
    rw [e, sumR_add, sumR_ind _ _ _ (by have := h m (by simp); omega),
      sum_levelWidthsW c n mats fun m' hm' => h m' (by simp [hm'])]
    simp

/-! ## The deduplicated opening size -/

/-- **Deduplicated multiproof bound** for `s` positions over an oracle of shapes `mats`:
rows `min s 2^m` per matrix of log `m` (4 bytes per base element), and
`dsum s n = Σ_{j<n} min s 2^j` sibling digests of 64 bytes. -/
def openSizeD (s : Nat) (mats : List (Nat × Nat)) : Nat :=
  4 * (mats.map fun m => min s (2 ^ m.1) * m.2).sum + 64 * dsum s (treeLog mats)

theorem openSizeD_le (s : Nat) (mats : List (Nat × Nat)) : openSizeD s mats ≤ openSize s mats := by
  unfold openSizeD openSize
  have h1 : (mats.map fun m => min s (2 ^ m.1) * m.2).sum ≤ s * (mats.map (·.2)).sum := by
    rw [← SizeBound.sum_map_mul]
    exact SizeBound.sum_map_le fun m _ => Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
  have h3 := dsum_le_mul s (treeLog mats)
  generalize (mats.map fun m => min s (2 ^ m.1) * m.2).sum = A at *
  generalize (mats.map (·.2)).sum = W at *
  generalize dsum s (treeLog mats) = D at *
  generalize treeLog mats = n at *
  rw [Nat.mul_add, Nat.mul_left_comm s 4, Nat.mul_left_comm s 64]
  have := Nat.mul_le_mul_left 4 h1
  have := Nat.mul_le_mul_left 64 h3
  omega

/-! ## The honest multiproof stream -/

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
variable (H : Bytes → Bytes) (o : Oracle F)

/-- One level: at most one sibling digest and one row block per **parent**. -/
theorem upBytes_lengthD (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) {k : Nat}
    (hk : k < treeLog (shapesOf o)) : ∀ cur : List Nat, (∀ x ∈ cur, x < 2 ^ (k + 1)) →
    (upBytes (K := K) (ev H (buildTree (K := K) o)) o k cur).1.length ≤
      (parentsOf cur).length * (64 + 4 * lw o k) := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => intro; simp [upBytes]
  | case2 x =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    rw [upBytes, buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)]
    simp only [List.length_append, node_length H o hH, rowsBytes_length o hr k _ hp, parentsOf,
      List.length_cons, List.length_nil]
    omega
  | case3 x x' rest hc ih =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have h := ih fun y hy => hlt y (by simp [hy])
    rw [upBytes, ite_eq_left_of_eq_true _ _ (eq_true hc), parentsOf,
      ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [List.length_append, rowsBytes_length o hr k _ hp, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]; omega
  | case4 x x' rest hc ih =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have h := ih fun y hy => hlt y (List.mem_cons_of_mem _ hy)
    rw [upBytes, ite_eq_right_of_eq_false _ _ (eq_false hc), parentsOf,
      ite_eq_right_of_eq_false _ _ (eq_false hc),
      buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)]
    simp only [List.length_append, node_length H o hH, rowsBytes_length o hr k _ hp,
      List.length_cons] at h ⊢
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- All levels above depth `k`: at most `min s 2^j` parents at every depth `j < k`. -/
theorem levelsBytes_lengthD (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) (s : Nat) :
    ∀ k, k ≤ treeLog (shapesOf o) → ∀ cur : List Nat, cur.Pairwise (· < ·) →
    (∀ x ∈ cur, x < 2 ^ k) → cur.length ≤ s →
    (levelsBytes (K := K) (ev H (buildTree (K := K) o)) o k cur).length ≤
      sumR k (fun j => min s (2 ^ j) * (64 + 4 * lw o j))
  | 0, _, _, _, _, _ => by simp [levelsBytes, sumR]
  | k + 1, hk, cur, hs, hlt, hl => by
    have h1 := upBytes_lengthD H o hH hr (k := k) (by omega) cur hlt
    have hps := parentsOf_sorted hs
    have hplt := parentsOf_lt hlt
    have hpl0 := parentsOf_length cur
    have hpl : (parentsOf cur).length ≤ min s (2 ^ k) :=
      Nat.le_min.mpr ⟨by omega, length_le_pow hps hplt⟩
    have h2 := levelsBytes_lengthD hH hr s k (by omega) (parentsOf cur) hps hplt (by omega)
    simp only [levelsBytes, List.length_append, upBytes_snd]
    rw [sumR_succ]
    have h3 := Nat.mul_le_mul_right (64 + 4 * lw o k) hpl
    omega

/-- **Deduplicated multiproof size** of the honest stream (`multiproofBytes`, the stream the
deployed reader `Stark.Merkle.multiproof` consumes exactly, `ev_multiproof`): for sorted,
duplicate-free leaf indices `S < 2^n` with `|S| ≤ s`, at most `openSizeD s (shapesOf o)` bytes. -/
theorem multiproof_size_le (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) (s : Nat)
    (S : List Nat) (hs : S.Pairwise (· < ·)) (hlt : ∀ x ∈ S, x < 2 ^ treeLog (shapesOf o))
    (hl : S.length ≤ s) :
    (multiproofBytes (K := K) (ev H (buildTree (K := K) o)) o S).length ≤
      openSizeD s (shapesOf o) := by
  have hSn : S.length ≤ min s (2 ^ treeLog (shapesOf o)) :=
    Nat.le_min.mpr ⟨hl, length_le_pow hs hlt⟩
  have hleaf : (S.flatMap (rowsBytes (K := K) o (treeLog (shapesOf o)))).length =
      S.length * (4 * lw o (treeLog (shapesOf o))) := by
    have : ∀ S' : List Nat, (∀ x ∈ S', x < 2 ^ treeLog (shapesOf o)) →
        (S'.flatMap (rowsBytes (K := K) o (treeLog (shapesOf o)))).length =
          S'.length * (4 * lw o (treeLog (shapesOf o))) := by
      intro S' h
      induction S' with
      | nil => simp
      | cons x S' ih =>
        simp only [List.flatMap_cons, List.length_append, rowsBytes_length o hr _ x (h x (by simp)),
          ih (fun y hy => h y (by simp [hy])), List.length_cons, Nat.succ_mul]
        omega
    exact this S hlt
  have hlev := levelsBytes_lengthD H o hH hr s _ (Nat.le_refl _) S hs hlt hl
  have hsum := sum_levelWidthsW (fun j => min s (2 ^ j)) (treeLog (shapesOf o)) (shapesOf o)
    (shapes_le o)
  have hds := dsum_eq_sumR s (treeLog (shapesOf o))
  unfold multiproofBytes openSizeD
  rw [List.length_append, hleaf, ← hsum, sumR_succ, hds]
  -- split the per-level sum into digests and rows
  have hsplit : sumR (treeLog (shapesOf o)) (fun j => min s (2 ^ j) * (64 + 4 * lw o j)) =
      64 * sumR (treeLog (shapesOf o)) (fun j => min s (2 ^ j)) +
        4 * sumR (treeLog (shapesOf o)) (fun j => min s (2 ^ j) * (levelWidths (shapesOf o) j).sum) := by
    have e1 : (fun j => min s (2 ^ j) * (64 + 4 * lw o j)) =
        fun j => 64 * min s (2 ^ j) + 4 * (min s (2 ^ j) * (levelWidths (shapesOf o) j).sum) := by
      funext j; simp only [lw]; rw [Nat.mul_add, Nat.mul_comm (min s (2 ^ j)) 64,
        Nat.mul_left_comm]
    rw [e1, sumR_add]
    have hm : ∀ (c : Nat) (f : Nat → Nat) N, sumR N (fun j => c * f j) = c * sumR N f := by
      intro c f N; induction N with
      | zero => rfl
      | succ N ih => rw [sumR_succ, sumR_succ, ih, Nat.mul_add]
    rw [hm 64 (fun j => min s (2 ^ j)), hm 4 (fun j => min s (2 ^ j) * (levelWidths (shapesOf o) j).sum)]
  have h3 : S.length * (4 * lw o (treeLog (shapesOf o))) ≤
      min s (2 ^ treeLog (shapesOf o)) * (4 * lw o (treeLog (shapesOf o))) :=
    Nat.mul_le_mul_right _ hSn
  have e4 : min s (2 ^ treeLog (shapesOf o)) * (4 * lw o (treeLog (shapesOf o))) =
      4 * (min s (2 ^ treeLog (shapesOf o)) * (levelWidths (shapesOf o) (treeLog (shapesOf o))).sum) := by
    simp only [lw]; rw [Nat.mul_left_comm]
  rw [hsplit] at hlev
  rw [Nat.mul_add]
  omega

/-- All openings of a proof, with the deduplicated bound per oracle. -/
theorem openBytes_lengthD (hH : ∀ m, (fit32 (H m)).length = 32) (n0 : Nat) (xs : List Nat)
    (hlt : ∀ x ∈ xs, x < 2 ^ n0) : ∀ ts : List (Oracle F × List (List Bytes)),
    (∀ t ∈ ts, t.2 = ev H (buildTree (K := K) t.1) ∧ RowsOk t.1) →
    (openBytes (K := K) n0 xs ts).length ≤ (ts.map fun t => openSizeD xs.length (shapesOf t.1)).sum
  | [], _ => by simp [openBytes]
  | (o', lv) :: ts, hts => by
    obtain ⟨hlv, hr⟩ := hts (o', lv) (by simp)
    simp only at hlv hr
    subst hlv
    have ih := openBytes_lengthD hH n0 xs hlt ts fun t ht => hts t (by simp [ht])
    have hS : ∀ s ∈ sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o'))),
        s < 2 ^ treeLog (shapesOf o') := by
      intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_sortDedup.mp hs)
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le (hlt x hx) (Nat.pow_le_pow_right (by decide) (by omega))
    have hm := multiproof_size_le H o' hH hr xs.length _
      (sortDedup_sorted _) hS
      (by have := sortDedup_length (xs.map fun x => x >>> (n0 - treeLog (shapesOf o'))); simpa using this)
    simp only [openBytes, List.length_append, List.map_cons, List.sum_cons]
    omega

end

/-! ## The per-header bound and the honest proof -/

/-- **Deduplicated proof-size bound** for header `hdr` (`sizeBound` with `openSizeD`). -/
def sizeBoundD {F K : Type} (V : IopSpec F K) (hdr : List Nat) : Nat :=
  prefixSize (V.schedule hdr) +
    ((schedOracles (V.schedule hdr)).map (openSizeD (V.numChunks * V.posPerChunk))).sum

/-- `sizeBoundD` never exceeds `sizeBound`. -/
theorem sizeBoundD_le {F K : Type} (V : IopSpec F K) (hdr : List Nat) :
    sizeBoundD V hdr ≤ sizeBound V hdr := by
  unfold sizeBoundD sizeBound
  exact Nat.add_le_add_left (SizeBound.sum_map_le fun m _ => openSizeD_le _ m) _

/-- Proof size against the deduplicated bound, for 32-byte hashes. -/
def SizeStmt32D : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) (H : Bytes → Bytes),
    (∀ m, (fit32 (H m)).length = 32) → ProverWf V pr cb →
    (runH (pureH H) (proveTree V pr pub cb) ()).1.length ≤ sizeBoundD V pr.hdr

/-- **The honest proof has at most `sizeBoundD V pr.hdr` bytes.** -/
theorem size32D : SizeStmt32D := by
  intro F K _ _ _ _ _ V pr pub cb H hH hw
  change (ev H (proveTree V pr pub cb)).length ≤ _
  obtain ⟨R, ps, ents, entsV, ts, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    ev_commitLoop H hw hH (V.schedule pr.hdr) ⟨whp H tagInit (initMsg pub cb), PT.init cb, [], []⟩
      inv_init
  have hraw := raw_length H hw hH (V.schedule pr.hdr) ⟨whp H tagInit (initMsg pub cb), PT.init cb, [], []⟩
    inv_init
  generalize hst : ev H (commitLoop pr (V.schedule pr.hdr)
    ⟨whp H tagInit (initMsg pub cb), PT.init cb, [], []⟩) = st at *
  simp only [List.nil_append] at h3 hraw
  simp only [List.length_nil, Nat.zero_add] at hraw
  simp only [proveTree, hw.hdrOk, ite_true, ev_bind, ev_WH, hst, ev_pure, List.length_append, hraw, h3]
  have hxl := positions_length V (V.queryLog pr.hdr) (ev H (queryAnswers st.d V.numChunks))
  rw [ev_queryAnswers_length] at hxl
  have ho := openBytes_lengthD H hH (V.queryLog pr.hdr) _
    (positions_lt V (V.queryLog pr.hdr) (ev H (queryAnswers st.d V.numChunks))) ts h11
  rw [hxl] at ho
  unfold sizeBoundD
  rw [← h10, List.map_map] at *
  exact Nat.add_le_add_left ho _

end ZkFormal.Size
