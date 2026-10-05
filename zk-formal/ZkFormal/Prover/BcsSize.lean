import ZkFormal.Prover.BcsComplete

/-!
# ZkFormal.Prover.BcsSize — the proof-size bound (P2)

`size32 : SizeStmt32`: for a 32-byte hash, the honest proof has at most
`sizeBound V pr.hdr` bytes: the commit-phase prefix is exactly
`prefixSize (V.schedule pr.hdr)` (`raw_length`), and the multiproof of every oracle,
for `|xs| = numChunks · posPerChunk` positions, has at most
`|xs| · (4 · Σ widths + 64 · depth)` bytes (`multiproofBytes_le`).

`SizeStmt` itself (every `H`) is false: with 33-byte answers a root has 66 > 64 bytes
(R-L7-bcs-1).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-- (P2, corrected) Proof size for 32-byte hashes. -/
def SizeStmt32 : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) (H : Bytes → Bytes),
    (∀ m, (fit32 (H m)).length = 32) → ProverWf V pr cb →
    (runH (pureH H) (proveTree V pr pub cb) ()).1.length ≤ sizeBound V pr.hdr

/-! ## Sums over a range -/

def sumR (N : Nat) (f : Nat → Nat) : Nat := ((List.range N).map f).sum

theorem sumR_succ (N : Nat) (f : Nat → Nat) : sumR (N + 1) f = sumR N f + f N := by
  simp [sumR, List.range_succ, List.sum_append]

theorem sumR_add (N : Nat) (f g : Nat → Nat) : sumR N (fun k => f k + g k) = sumR N f + sumR N g := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sumR_succ, sumR_succ, sumR_succ, ih]; omega

theorem sumR_ind (N a w : Nat) (h : a < N) : sumR N (fun k => if a = k then w else 0) = w := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [sumR_succ]
    by_cases ha : a = N
    · subst ha
      have : sumR a (fun k => if a = k then w else 0) = 0 := by
        have : ∀ M, M ≤ a → sumR M (fun k => if a = k then w else 0) = 0 := by
          intro M hM
          induction M with
          | zero => rfl
          | succ M ihM =>
            rw [sumR_succ, ihM (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact this a (Nat.le_refl _)
      rw [this, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; omega
    · rw [ih (by omega), ite_eq_right_of_eq_false _ _ (eq_false ha)]; omega

theorem sum_levelWidths (n : Nat) : ∀ mats : List (Nat × Nat), (∀ m ∈ mats, m.1 ≤ n) →
    sumR (n + 1) (fun k => (levelWidths mats k).sum) = (mats.map (·.2)).sum
  | [], _ => by
    have : ∀ N, sumR N (fun k => (levelWidths [] k).sum) = 0 := by
      intro N; induction N with
      | zero => rfl
      | succ N ih => rw [sumR_succ, ih]; rfl
    exact this _
  | m :: mats, h => by
    have e : (fun k => (levelWidths (m :: mats) k).sum) =
        fun k => (if m.1 = k then m.2 else 0) + (levelWidths mats k).sum := by
      funext k
      simp only [levelWidths, List.filter_cons, beq_iff_eq]
      split <;> simp_all
    rw [e, sumR_add, sumR_ind _ _ _ (by have := h m (by simp); omega),
      sum_levelWidths n mats fun m' hm' => h m' (by simp [hm'])]
    simp

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

/-! ## Commit-phase prefix -/

theorem encF_length (a : F) : (encF (K := K) a).length = 4 := Bytes.leN_length _ _

theorem flatMap_encF_length : ∀ row : List F, (row.flatMap (encF (K := K))).length = 4 * row.length
  | [] => rfl
  | a :: row => by
    simp only [List.flatMap_cons, List.length_append, encF_length, flatMap_encF_length row,
      List.length_cons]; omega

theorem encK_length (x : K) : (encK (F := F) x).length = 32 := by
  simp only [encK, flatMap_encF_length, StarkFieldLaws.limbs_length]

theorem flatMap_encK_length : ∀ xs : List K, (xs.flatMap (encK (F := F))).length = 32 * xs.length
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.length_append, encK_length, flatMap_encK_length xs,
      List.length_cons]; omega

theorem msgBytes_length : ∀ {m : List (PartV K (Oracle F))} {parts : List Part}, Fits2 m parts →
    ∀ roots : List Bytes, roots.length = (msgOracles m).length → (∀ r ∈ roots, r.length = 64) →
    (msgBytes (F := F) m roots).length = (parts.map partSize).sum
  | [], [], .nil, roots, hl, _ => by
    have : roots = [] := by simpa [msgOracles] using hl
    subst this; rfl
  | p :: ps, q :: qs, .cons hpq hs, roots, hl, hr64 => by
    cases p with
    | header l =>
      cases q with
      | header n =>
        have hl' : roots.length = (msgOracles ps).length := by
          rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
        have hfit : l.length = n := hpq
        simp only [msgBytes, partBytes, List.length_append, msgBytes_length hs roots hl' hr64,
          List.map_cons, List.sum_cons, partSize, encHeader, Bytes.leN_length, List.length_map, hfit]
      | oracle _ => exact (hpq : False).elim
      | elems _ => exact (hpq : False).elim
    | oracle o =>
      cases q with
      | oracle mats =>
        match roots, hl, hr64 with
        | [], hl, _ => simp [msgOracles] at hl
        | r :: rs, hl, hr64 =>
          have hl' : rs.length = (msgOracles ps).length := by
            rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
          simp only [msgBytes, partBytes, List.length_append, hr64 r (by simp),
            msgBytes_length hs rs hl' (fun r' h' => hr64 r' (List.mem_cons_of_mem _ h')),
            List.map_cons, List.sum_cons, partSize]
      | header _ => exact (hpq : False).elim
      | elems _ => exact (hpq : False).elim
    | elems xs =>
      cases q with
      | elems n =>
        have hl' : roots.length = (msgOracles ps).length := by
          rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
        have hfit : xs.length = n := hpq
        simp only [msgBytes, partBytes, List.length_append, flatMap_encK_length,
          msgBytes_length hs roots hl' hr64, List.map_cons, List.sum_cons, partSize, hfit]
      | header _ => exact (hpq : False).elim
      | oracle _ => exact (hpq : False).elim

theorem prefixSize_msg (ps : List Part) (ss : List Slot) :
    prefixSize (.msg ps :: ss) = (ps.map partSize).sum + prefixSize ss := by
  simp [prefixSize]

theorem prefixSize_chal (b : Bool) (ss : List Slot) : prefixSize (.chal b :: ss) = prefixSize ss := by
  simp [prefixSize]

variable (H : Bytes → Bytes)
variable {V : IopSpec F K} {pr : IopProver F K} {cb : Bytes}

theorem raw_length (hw : ProverWf V pr cb) (hH : ∀ m, (fit32 (H m)).length = 32) :
    ∀ (ss : List Slot) (st : CState F K), Inv V pr cb ss st.τ →
      (ev H (commitLoop pr ss st)).raw.length = st.raw.length + prefixSize ss
  | [], st, _ => by simp [commitLoop, ev_pure, prefixSize]
  | .msg parts :: ss, st, hi => by
    obtain ⟨hi1, hf⟩ := inv_msg hw hi
    have hloop : ev H (commitLoop pr (.msg parts :: ss) st) =
        ev H (commitLoop pr ss (ev H (commitMsg st (pr.next st.τ)))) := by
      simp only [commitLoop, ev_bind]
    rw [hloop, raw_length hw hH ss _ (by rw [ev_commitMsg]; exact hi1), ev_commitMsg, prefixSize_msg]
    have h64 : ∀ r ∈ (msgOracles (pr.next st.τ)).map (fun o => rootOf (ev H (buildTree (K := K) o))),
        r.length = 64 := by
      intro r hr
      obtain ⟨o, _, rfl⟩ := List.mem_map.mp hr
      rw [buildTree_root]; exact node_length H o hH _ _ _
    simp only [List.length_append, msgBytes_length hf _ (by simp) h64]
    omega
  | .chal ood :: ss, st, hi => by
    have hloop : ev H (commitLoop pr (.chal ood :: ss) st) = ev H (commitLoop pr ss ⟨whp H tagChal st.d,
        st.τ.pushChal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)),
        st.raw, st.trees⟩) := by
      simp only [commitLoop, ev_bind_WH]
    rw [hloop, raw_length hw hH ss _ (inv_chal hw hi _), prefixSize_chal]

/-! ## Openings -/

/-- Total width of the matrices of level `k`. -/
def lw (o : Oracle F) (k : Nat) : Nat := (levelWidths (shapesOf o) k).sum

theorem rows_flatMap_length (j : Nat) : ∀ ms : List (Mat F), (∀ M ∈ ms, (M.row j).length = M.width) →
    (ms.flatMap fun M => (M.row j).flatMap (encF (K := K))).length = 4 * (ms.map (·.width)).sum
  | [], _ => rfl
  | M :: ms, h => by
    simp only [List.flatMap_cons, List.length_append, flatMap_encF_length, h M (by simp),
      rows_flatMap_length j ms (fun M' hM' => h M' (by simp [hM'])), List.map_cons, List.sum_cons]
    omega

theorem rowsBytes_length (o : Oracle F) (hr : RowsOk o) (k j : Nat) (hj : j < 2 ^ k) :
    (rowsBytes (K := K) o k j).length = 4 * lw o k := by
  unfold rowsBytes lw
  rw [levelWidths_shapesOf, rows_flatMap_length]
  intro M hM
  simp only [List.mem_filter, beq_iff_eq] at hM
  exact hr M hM.1 j (hM.2 ▸ hj)

theorem parentsOf_length : ∀ cur : List Nat, (parentsOf cur).length ≤ cur.length := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => simp [parentsOf]
  | case2 x => simp [parentsOf]
  | case3 x x' rest hc ih =>
    rw [parentsOf, ite_eq_left_of_eq_true _ _ (eq_true hc)]; simp; omega
  | case4 x x' rest hc ih =>
    rw [parentsOf, ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp at ih ⊢; omega

variable (H : Bytes → Bytes) (o : Oracle F)

theorem upBytes_length (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) {k : Nat}
    (hk : k < treeLog (shapesOf o)) : ∀ cur : List Nat, (∀ x ∈ cur, x < 2 ^ (k + 1)) →
    (upBytes (K := K) (ev H (buildTree (K := K) o)) o k cur).1.length ≤
      cur.length * (64 + 4 * lw o k) := by
  intro cur
  induction cur using parentsOf.induct with
  | case1 => intro; simp [upBytes]
  | case2 x =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    rw [upBytes, buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)]
    simp only [List.length_append, node_length H o hH, rowsBytes_length o hr k _ hp, List.length_cons,
      List.length_nil]
    omega
  | case3 x x' rest hc ih =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have h := ih fun y hy => hlt y (by simp [hy])
    rw [upBytes, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [List.length_append, rowsBytes_length o hr k _ hp, List.length_cons]
    rw [Nat.add_mul, Nat.add_mul]; omega
  | case4 x x' rest hc ih =>
    intro hlt
    have hx := hlt x (by simp)
    have hp : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have h := ih fun y hy => hlt y (List.mem_cons_of_mem _ hy)
    rw [upBytes, ite_eq_right_of_eq_false _ _ (eq_false hc),
      buildTree_at (K := K) H o (k := k + 1) (by omega) (xor_one_lt hx)]
    simp only [List.length_append, node_length H o hH, rowsBytes_length o hr k _ hp] at h ⊢
    simp only [List.length_cons] at h ⊢
    rw [Nat.add_mul]; omega

theorem levelsBytes_length (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) (s : Nat) :
    ∀ k, k ≤ treeLog (shapesOf o) → ∀ cur : List Nat, (∀ x ∈ cur, x < 2 ^ k) → cur.length ≤ s →
    (levelsBytes (K := K) (ev H (buildTree (K := K) o)) o k cur).length ≤
      s * (64 * k + 4 * sumR k (lw o))
  | 0, _, _, _, _ => by simp [levelsBytes]
  | k + 1, hk, cur, hlt, hs => by
    have h1 := upBytes_length H o hH hr (k := k) (by omega) cur hlt
    have h2 := levelsBytes_length hH hr s k (by omega) (parentsOf cur) (parentsOf_lt hlt)
      (Nat.le_trans (parentsOf_length cur) hs)
    simp only [levelsBytes, List.length_append, upBytes_snd]
    have h3 : cur.length * (64 + 4 * lw o k) ≤ s * (64 + 4 * lw o k) := Nat.mul_le_mul_right _ hs
    rw [sumR_succ]
    have e : s * (64 * (k + 1) + 4 * (sumR k (lw o) + lw o k)) =
        s * (64 * k + 4 * sumR k (lw o)) + s * (64 + 4 * lw o k) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [e]; omega

theorem shapes_le (m : Nat × Nat) (hm : m ∈ shapesOf o) : m.1 ≤ treeLog (shapesOf o) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hm
  exact log_le_treeLog hM

theorem multiproofBytes_length (hH : ∀ m, (fit32 (H m)).length = 32) (hr : RowsOk o) (s : Nat)
    (S : List Nat) (hlt : ∀ x ∈ S, x < 2 ^ treeLog (shapesOf o)) (hs : S.length ≤ s) :
    (multiproofBytes (K := K) (ev H (buildTree (K := K) o)) o S).length ≤ openSize s (shapesOf o) := by
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
  have hlev := levelsBytes_length H o hH hr s _ (Nat.le_refl _) S hlt hs
  have hsum := sum_levelWidths (treeLog (shapesOf o)) (shapesOf o) (shapes_le o)
  unfold multiproofBytes openSize
  rw [List.length_append, hleaf, ← hsum, sumR_succ]
  have h3 : S.length * (4 * lw o (treeLog (shapesOf o))) ≤ s * (4 * lw o (treeLog (shapesOf o))) :=
    Nat.mul_le_mul_right _ hs
  have e : s * (4 * (sumR (treeLog (shapesOf o)) (fun k => (levelWidths (shapesOf o) k).sum) +
      (levelWidths (shapesOf o) (treeLog (shapesOf o))).sum) + 64 * treeLog (shapesOf o)) =
      s * (64 * treeLog (shapesOf o) + 4 * sumR (treeLog (shapesOf o)) (lw o)) +
        s * (4 * lw o (treeLog (shapesOf o))) := by
    have hl : sumR (treeLog (shapesOf o)) (lw o) =
        sumR (treeLog (shapesOf o)) (fun k => (levelWidths (shapesOf o) k).sum) := rfl
    rw [← Nat.mul_add]; congr 1; simp only [lw]; omega
  rw [e]; omega

theorem openBytes_length (hH : ∀ m, (fit32 (H m)).length = 32) (n0 : Nat) (xs : List Nat)
    (hlt : ∀ x ∈ xs, x < 2 ^ n0) : ∀ ts : List (Oracle F × List (List Bytes)),
    (∀ t ∈ ts, t.2 = ev H (buildTree (K := K) t.1) ∧ RowsOk t.1) →
    (openBytes (K := K) n0 xs ts).length ≤ (ts.map fun t => openSize xs.length (shapesOf t.1)).sum
  | [], _ => by simp [openBytes]
  | (o', lv) :: ts, hts => by
    obtain ⟨hlv, hr⟩ := hts (o', lv) (by simp)
    simp only at hlv hr
    subst hlv
    have ih := openBytes_length hH n0 xs hlt ts fun t ht => hts t (by simp [ht])
    have hS : ∀ s ∈ sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o'))),
        s < 2 ^ treeLog (shapesOf o') := by
      intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_sortDedup.mp hs)
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le (hlt x hx) (Nat.pow_le_pow_right (by decide) (by omega))
    have hm := multiproofBytes_length H o' hH hr xs.length _ hS
      (by have := sortDedup_length (xs.map fun x => x >>> (n0 - treeLog (shapesOf o'))); simpa using this)
    simp only [openBytes, List.length_append, List.map_cons, List.sum_cons]
    omega

end

/-- **(P2, corrected)** The honest proof has at most `sizeBound V pr.hdr` bytes. -/
theorem size32 : SizeStmt32 := by
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
  have ho := openBytes_length H hH (V.queryLog pr.hdr) _ (positions_lt V (V.queryLog pr.hdr) (ev H (queryAnswers st.d V.numChunks))) ts h11
  rw [hxl] at ho
  unfold sizeBound
  rw [← h10, List.map_map] at *
  exact Nat.add_le_add_left ho _

end ZkFormal.Prover
