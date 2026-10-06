import ZkFormal.NearV3.Extract.Ups.PlanRows
import ZkFormal.NearV3.Extract.Ups.LayoutMain

/-!
# ZkFormal.NearV3.Extract.Ups.Plan — the part plan (layer 2)

`UpsPlan s ps ci ti di si kd sdx`: the segment's case `ci`, terminal position `I = ti`,
terminal level `D = di` and terminal row `t* = si + 1` (indices into `UCase.all`, one-hot
columns); every part `k` has a kind `kd k` (index into `UKind.all`) and a source level
`sdx k`.  The plan:

* the number of parts is `nT + dep_D` (`nT = nTof ci ti` terminal parts, one upper part per
  depth above the terminal record);
* part `k < nT` is the `k`-th terminal part of the case (`termPlan`), reads level `D`
  (`sN = N_D`, depth `dep_D`), `up = 0`, `rc = D`;
* part `k ≥ nT` is an upper part (`RDB`, `RDE` or `PT`), `up = 1`, at depth
  `pdep = dep_D − (k + 1 − nT)` (the root part at depth `0`);
* `rc` counts the descend parts from `k` to the root part; there are exactly `D` of them;
  a descend reads level `rc − 1`;
* every non-`PT` part reads `sN = N_sd` at depth `dep_sd`;
* the chain: `cN` of part `k + 1` is `sN` of part `k`;
* `rootP` marks exactly the last part.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Descend parts among parts `k … k+m−1` (kind index `≤ 1`: `RDB`, `RDE`). -/
def rdCount (kd : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => (if kd k ≤ 1 then 1 else 0) + rdCount kd (k + 1) m

theorem rdCount_le (kd : Nat → Nat) : ∀ k m, rdCount kd k m ≤ m
  | _, 0 => Nat.le_refl _
  | k, m + 1 => by have := rdCount_le kd (k + 1) m; simp only [rdCount]; split <;> omega

/-- **The part plan of a segment.** -/
structure UpsPlan (s : UpsSeg) (ps : List (Nat × Nat)) (ci ti di si : Nat) (kd sdx : Nat → Nat) : Prop where
  ix : ci < 11 ∧ ti < 3 ∧ di < 3 ∧ si < 3
  /-- the segment's one-hot selectors (on every row) -/
  seg : ∀ i, i < s.rows.length →
    (∀ m, m < 11 → s.row i (17 + m) = if m = ci then 1 else 0) ∧
    (∀ m, m < 3 → s.row i (34 + m) = if m = ti then 1 else 0) ∧
    (∀ m, m < 3 → s.row i (28 + m) = if m = di then 1 else 0) ∧
    (∀ m, m < 3 → s.row i (31 + m) = if m = si then 1 else 0)
  /-- the part's kind and source level (one-hot, on its first row) -/
  part : ∀ k (hk : k < ps.length), kd k < 12 ∧ sdx k < 3 ∧
    (∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = kd k then 1 else 0) ∧
    (∀ m, m < 3 → s.row ps[k].1 (65 + m) = if m = sdx k then 1 else 0)
  /-- the number of parts -/
  len : ps.length = nTof ci ti + s.row 0 (176 + di)
  /-- terminal parts -/
  term : ∀ k (hk : k < ps.length), k < nTof ci ti →
    UKind.all.getD (kd k) .RDB = (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB ∧ 1 < kd k ∧ kd k < 11 ∧
    s.row ps[k].1 UpsV3.up = 0 ∧ s.row ps[k].1 UpsV3.rc = di ∧ sdx k = di ∧ s.row ps[k].1 pdep = s.row 0 (176 + di)
  /-- upper parts -/
  upper : ∀ k (hk : k < ps.length), nTof ci ti ≤ k →
    (kd k ≤ 1 ∨ kd k = 11) ∧ s.row ps[k].1 UpsV3.up = 1 ∧
    s.row ps[k].1 pdep + (k + 1 - nTof ci ti) = s.row 0 (176 + di)
  /-- the descend counter -/
  rcnt : ∀ k (hk : k < ps.length), s.row ps[k].1 UpsV3.rc = rdCount kd k (ps.length - k)
  ndesc : rdCount kd 0 ps.length = di
  desc : ∀ k (hk : k < ps.length), kd k ≤ 1 → s.row ps[k].1 UpsV3.rc = sdx k + 1
  /-- the source record and its depth (every part but a pass-through) -/
  src : ∀ k (hk : k < ps.length), kd k ≠ 11 →
    s.row ps[k].1 sN = s.row 0 (11 + sdx k) ∧ s.row ps[k].1 pdep = s.row 0 (176 + sdx k)
  /-- the chain of source records -/
  chain : ∀ k (hk : k + 1 < ps.length), s.row ps[k + 1].1 cN = s.row ps[k].1 sN
  /-- the root part is the last part -/
  root : ∀ k (hk : k < ps.length), s.row ps[k].1 rootP = 1 ↔ k + 1 = ps.length

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-! ## Finite facts of the plan -/

def termCheck : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti => (List.range 4).all fun k =>
    (List.range 12).all fun ki =>
      !(decide (k < nTof ci ti) && UKind.all.getD ki .RDB == (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB) ||
        (decide (1 < ki) && decide (ki < 11))

theorem termCheck_ok : termCheck = true := by decide

theorem termKind {ci ti k ki : Nat} (h1 : ci < 11) (h2 : ti < 3) (h3 : k < nTof ci ti) (h4 : ki < 12)
    (h : UKind.all.getD ki .RDB = (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB) : 1 < ki ∧ ki < 11 := by
  have hT := nTof_le ci h1 ti h2
  have c := termCheck_ok
  simp only [termCheck, List.all_eq_true, List.mem_range] at c
  have := c ci h1 ti h2 k (by omega) ki h4
  simp [h3] at this
  exact this.resolve_left (fun hn => hn (by simpa using h))

theorem upperKind : ∀ ki, ki < 12 → ((UKind.all.getD ki .RDB).upper = true ↔ (ki ≤ 1 ∨ ki = 11)) := by decide

theorem nTof_pos : ∀ ci, ci < 11 → ∀ ti, ti < 3 → 1 ≤ nTof ci ti := by decide

theorem planOk_dec {ci ti jj ki uu : Nat} (h : planOk ci ti jj ki uu = true) (hki : ki < 12) :
    (1 ≤ jj ∧ jj ≤ nTof ci ti → UKind.all.getD ki .RDB = (termPlan (UCase.all.getD ci .LP) ti).getD (jj - 1) .RDB ∧
      uu = 0) ∧
    (¬ (1 ≤ jj ∧ jj ≤ nTof ci ti) → (ki ≤ 1 ∨ ki = 11) ∧ uu = 1) := by
  unfold planOk at h
  simp only [nTof] at *
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨fun _ => h, fun h' => absurd hc h'⟩
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨fun h' => absurd h' hc, fun _ => ⟨(upperKind ki hki).1 h.1, h.2⟩⟩

theorem segIx_mem : (∀ m, m < 11 → 17 + m ∈ segConst) ∧ (∀ m, m < 3 → 34 + m ∈ segConst) ∧
    (∀ m, m < 3 → 28 + m ∈ segConst) ∧ (∀ m, m < 3 → 31 + m ∈ segConst) ∧
    (∀ m, m < 3 → 176 + m ∈ segConst) ∧ (∀ m, m < 3 → 11 + m ∈ segConst) ∧ nQ ∈ segConst := by decide

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw hs hL

theorem pFirst (k : Nat) (hk : k < ps.length) :
    ps[k].1 < s.rows.length ∧ s.row ps[k].1 qb = 1 ∧ s.row ps[k].1 pf = 1 := by
  obtain ⟨-, U⟩ := hL.part k hk
  have r := U.rows 0 U.pos
  rw [Nat.add_zero] at r
  exact ⟨by have := U.le; have := U.pos; omega, r.1, r.2.2.1.2 rfl⟩

theorem pLast (k : Nat) (hk : k < ps.length) :
    ps[k].1 + ps[k].2 - 1 < s.rows.length ∧ s.row (ps[k].1 + ps[k].2 - 1) qb = 1 ∧
      s.row (ps[k].1 + ps[k].2 - 1) pl = 1 ∧
      ∀ x ∈ partConst, s.row (ps[k].1 + ps[k].2 - 1) x = s.row ps[k].1 x := by
  obtain ⟨-, U⟩ := hL.part k hk
  have r := U.rows (ps[k].2 - 1) (by have := U.pos; omega)
  rw [show ps[k].1 + (ps[k].2 - 1) = ps[k].1 + ps[k].2 - 1 by have := U.pos; omega] at r
  exact ⟨by have := U.le; have := U.pos; omega, r.1, r.2.2.2.1.2 (by have := U.pos; omega), r.2.2.2.2⟩

theorem pNext (k : Nat) (hk : k + 1 < ps.length) : ps[k].1 + ps[k].2 - 1 + 1 = ps[k + 1].1 := by
  have := consec_get ps (4 + L) hL.consec k hk
  have := (hL.part k (by omega)).2.pos
  omega

theorem pEnd : (ps[ps.length - 1]'(by have := hL.nonempty; omega)).1 +
    (ps[ps.length - 1]'(by have := hL.nonempty; omega)).2 = s.rows.length := by
  have := segEnd_last ps (4 + L) hL.consec hL.nonempty
  rw [hL.cover] at this; exact this.symm

theorem pRoot (k : Nat) (hk : k < ps.length) : s.row ps[k].1 rootP = 1 ↔ k + 1 = ps.length := by
  obtain ⟨hlt, hq, hp, hc⟩ := pLast hw hs hL k hk
  have hst := hw.stop s hs _ hlt
  rw [hc rootP (by decide)] at hst
  have hE := pEnd hw hs hL
  constructor
  · intro h
    have := hst.1 ⟨hq, hp, h⟩
    rcases Nat.lt_or_ge (k + 1) ps.length with h' | h'
    · have := pNext hw hs hL k h'
      have := (pFirst hw hs hL (k + 1) h').1
      omega
    · omega
  · intro h
    have hk' : k = ps.length - 1 := by omega
    have hpos := (hL.part _ hk).2.pos
    have e : ps[k] = ps[ps.length - 1]'(by omega) := by simp only [hk']
    rw [← e] at hE
    exact (hst.2 (by omega)).2.2

theorem rootP0 (k : Nat) (hk : k + 1 < ps.length) : s.row ps[k].1 rootP = 0 := by
  have hb := partBoolN (okRow hw hs (pFirst hw hs hL k (by omega)).1) (rowLt hw hs _)
    (pFirst hw hs hL k (by omega)).2.2 (x := rootP) (by decide)
  have := (pRoot hw hs hL k (by omega))
  omega

/-- The position flags: part `k` has `jo (m + 1) = [m = k]`. -/
theorem joAt : ∀ k (hk : k < ps.length) m, m < 4 → s.row ps[k].1 (61 + m) = if m = k then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro hk m hm
    obtain ⟨hL1, hLm, hval⟩ := hL.value
    have v := hval (L - 1) (by omega)
    rw [show 4 + (L - 1) = 3 + L by omega] at v
    have h0 : ps[0].1 = 4 + L := consec_head ps (4 + L) hL.consec hk
    have hn : 3 + L + 1 < s.rows.length := by omega
    have J := joValueEnd (okIn hw hs hn) (rowLt hw hs _) (rowLt hw hs _) v.1 (v.2.2.2.2 (by omega))
    rw [show 3 + L + 1 = ps[0].1 by omega] at J
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
    · exact J.1
    · exact J.2.1
    · exact J.2.2.1
    · exact J.2.2.2
  | succ k ih =>
    intro hk m hm
    obtain ⟨hlt, hq, hp, hc⟩ := pLast hw hs hL k (by omega)
    have hn := pNext hw hs hL k hk
    have hr := rootP0 hw hs hL k hk
    rw [← hc rootP (by decide)] at hr
    have E := partEnd (okIn hw hs (by have := (pFirst hw hs hL (k + 1) hk).1; omega)) (rowLt hw hs _)
      (rowLt hw hs _) hq hp hr
    rw [hn] at E
    have c1 := hc (jo 1) (by decide); have c2 := hc (jo 2) (by decide); have c3 := hc (jo 3) (by decide)
    have i0 := ih (by omega) 0 (by omega); have i1 := ih (by omega) 1 (by omega)
    have i2 := ih (by omega) 2 (by omega)
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
    · exact E.1.trans (by simp)
    · rw [show 61 + 1 = jo 2 from rfl, E.2.1, c1]; exact i0.trans (by split <;> split <;> omega)
    · rw [show 61 + 2 = jo 3 from rfl, E.2.2.1, c2]; exact i1.trans (by split <;> split <;> omega)
    · rw [show 61 + 3 = jo 4 from rfl, E.2.2.2.1, c3]; exact i2.trans (by split <;> split <;> omega)

theorem psLe : ps.length ≤ s.rows.length := by
  have hE := pEnd hw hs hL
  have : ps.length ≤ (ps[ps.length - 1]'(by have := hL.nonempty; omega)).1 + 1 := by
    have := consec_mem_lt ps (4 + L) hL.consec 0 hL.nonempty
    -- the starts are strictly increasing
    have inc : ∀ k (hk : k < ps.length), k ≤ ps[k].1 := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro hk
        have := consec_get ps (4 + L) hL.consec k hk
        have := (hL.part k (by omega)).2.pos
        have := ih (by omega); omega
    have := inc (ps.length - 1) (by have := hL.nonempty; omega); omega
  have := (hL.part (ps.length - 1) (by have := hL.nonempty; omega)).2.pos
  omega

/-- **The part plan** of a segment with a layout. -/
theorem ups_plan_seg : ∃ ci ti di si kd sdx, UpsPlan s ps ci ti di si kd sdx := by
  have hlen0 : 0 < s.rows.length := by have := hL.walk.1; omega
  have hsf := hL.walk.2.1
  obtain ⟨ci, ti, di, si, h1, h2, h3, h4, ecs, eti, edd, ets⟩ :=
    segIx (okRow hw hs hlen0) (rowLt hw hs 0) (nextLt hw hs 0) hsf
  obtain ⟨mcs, mti, mdd, mts, mdep, mN, mnQ⟩ := segIx_mem
  have SC := fun i (hi : i < s.rows.length) x (hx : x ∈ segConst) => segConstAll hw hs hi hx
  have seg : ∀ i, i < s.rows.length →
      (∀ m, m < 11 → s.row i (17 + m) = if m = ci then 1 else 0) ∧
      (∀ m, m < 3 → s.row i (34 + m) = if m = ti then 1 else 0) ∧
      (∀ m, m < 3 → s.row i (28 + m) = if m = di then 1 else 0) ∧
      (∀ m, m < 3 → s.row i (31 + m) = if m = si then 1 else 0) := fun i hi =>
    ⟨fun m hm => (SC i hi _ (mcs m hm)).trans (ecs m hm), fun m hm => (SC i hi _ (mti m hm)).trans (eti m hm),
     fun m hm => (SC i hi _ (mdd m hm)).trans (edd m hm), fun m hm => (SC i hi _ (mts m hm)).trans (ets m hm)⟩
  -- part indices
  have hP : ∀ k (hk : k < ps.length), ∃ ki sdi, ki < 12 ∧ sdi < 3 ∧
      (∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = ki then 1 else 0) ∧
      (∀ m, m < 3 → s.row ps[k].1 (65 + m) = if m = sdi then 1 else 0) := fun k hk => by
    obtain ⟨hlt, hq, hp⟩ := pFirst hw hs hL k hk
    exact partIx (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hp hq
  let F : Nat → Nat × Nat := fun k =>
    if hk : k < ps.length then (Classical.choose (hP k hk), Classical.choose (Classical.choose_spec (hP k hk)))
    else (0, 0)
  have hF : ∀ k (hk : k < ps.length), (F k).1 < 12 ∧ (F k).2 < 3 ∧
      (∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = (F k).1 then 1 else 0) ∧
      (∀ m, m < 3 → s.row ps[k].1 (65 + m) = if m = (F k).2 then 1 else 0) := fun k hk => by
    simp only [F, dif_pos hk]
    exact Classical.choose_spec (Classical.choose_spec (hP k hk))
  refine ⟨ci, ti, di, si, fun k => (F k).1, fun k => (F k).2, ?_⟩
  -- per-part facts
  have hT1 := nTof_pos ci h1 ti h2
  have hT4 := nTof_le ci h1 ti h2
  have hRows := lenLe hw hs
  have hpsle := psLe hw hs hL
  have P22 : 2 ^ 22 < P := by unfold P; omega
  have PP : ∀ k (hk : k < ps.length),
      (k < nTof ci ti → UKind.all.getD (F k).1 .RDB = (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB ∧
        s.row ps[k].1 UpsV3.up = 0) ∧
      (nTof ci ti ≤ k → ((F k).1 ≤ 1 ∨ (F k).1 = 11) ∧ s.row ps[k].1 UpsV3.up = 1) := by
    intro k hk
    obtain ⟨hlt, hq, hp⟩ := pFirst hw hs hL k hk
    obtain ⟨f1, -, fk, -⟩ := hF k hk
    obtain ⟨c1, c2, -, -⟩ := seg _ hlt
    have J := joAt hw hs hL k hk
    have pf := planFact (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (jj := if k < 4 then k + 1 else 0)
      h1 h2 (by split <;> omega) f1 hp hq c1 c2 (fun m hm => by
        rw [J m hm]
        by_cases hk4 : k < 4
        · rw [if_pos hk4]
          by_cases e : m = k
          · rw [if_pos e, if_pos (by omega)]
          · rw [if_neg e, if_neg (by omega)]
        · rw [if_neg hk4, if_neg (by omega), if_neg (by omega)]) fk
    have D := planOk_dec pf f1
    refine ⟨fun hk' => ?_, fun hk' => ?_⟩
    · have := D.1 (by split <;> omega)
      rw [show (if k < 4 then k + 1 else 0) - 1 = k by split <;> omega] at this
      exact this
    · exact D.2 (by split <;> omega)
  have HP : ∀ k (hk : k < ps.length),
      (s.row ps[k].1 UpsV3.up = 0 → s.row ps[k].1 pdep = s.row ps[k].1 (176 + di)) ∧
      (s.row ps[k].1 UpsV3.up = 1 → (s.row ps[k].1 pdep + s.row ps[k].1 j) % P =
        (s.row ps[k].1 (176 + di) + nTof ci ti) % P) ∧
      (s.row ps[k].1 UpsV3.up = 0 → s.row ps[k].1 UpsV3.rc = di) ∧
      ((F k).1 ≠ 11 → (F k).1 ≤ 1 → s.row ps[k].1 UpsV3.rc = (F k).2 + 1) ∧
      ((F k).1 ≠ 11 → 1 < (F k).1 → (F k).2 = di) ∧
      ((F k).1 ≠ 11 → s.row ps[k].1 sN = s.row ps[k].1 (11 + (F k).2) ∧
        s.row ps[k].1 pdep = s.row ps[k].1 (176 + (F k).2)) := by
    intro k hk
    obtain ⟨hlt, hq, hp⟩ := pFirst hw hs hL k hk
    obtain ⟨f1, f2, fk, fs⟩ := hF k hk
    obtain ⟨c1, c2, c3, -⟩ := seg _ hlt
    exact partHeadPlan (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) h1 h2 h3 f1 f2 hp hq c1 c2 c3 fk fs
  have dep0 : ∀ k (hk : k < ps.length) m, m < 3 → s.row ps[k].1 (176 + m) = s.row 0 (176 + m) := fun k hk m hm =>
    SC _ (pFirst hw hs hL k hk).1 _ (mdep m hm)
  have N0 : ∀ k (hk : k < ps.length) m, m < 3 → s.row ps[k].1 (11 + m) = s.row 0 (11 + m) := fun k hk m hm =>
    SC _ (pFirst hw hs hL k hk).1 _ (mN m hm)
  have hj : ∀ k (hk : k < ps.length), s.row ps[k].1 j = k + 1 := fun k hk => (hL.part k hk).1
  have rdv : ∀ k (hk : k < ps.length), s.row ps[k].1 kRDB + s.row ps[k].1 kRDE = if (F k).1 ≤ 1 then 1 else 0 := by
    intro k hk
    obtain ⟨f1, -, fk, -⟩ := hF k hk
    have a : s.row ps[k].1 kRDB = if 0 = (F k).1 then 1 else 0 := fk 0 (by omega)
    have b : s.row ps[k].1 kRDE = if 1 = (F k).1 then 1 else 0 := fk 1 (by omega)
    rw [a, b]; split <;> split <;> split <;> omega
  -- the descend counter, backwards from the root part
  have RC : ∀ t k (hk : k < ps.length), k + t + 1 = ps.length →
      s.row ps[k].1 UpsV3.rc = rdCount (fun k => (F k).1) k (ps.length - k) := by
    intro t
    induction t with
    | zero =>
      intro k hk he
      obtain ⟨hlt, hq, hpl, hc⟩ := pLast hw hs hL k hk
      have hr := (pRoot hw hs hL k hk).2 (by omega)
      rw [← hc rootP (by decide)] at hr
      have E := rootEnd (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hpl hr
      rw [hc UpsV3.rc (by decide), hc kRDB (by decide), hc kRDE (by decide), rdv k hk] at E
      rw [E, show ps.length - k = 0 + 1 by omega]
      simp only [rdCount]; split <;> simp [P_lit]
    | succ t ih =>
      intro k hk he
      obtain ⟨hlt, hq, hpl, hc⟩ := pLast hw hs hL k hk
      have hr := rootP0 hw hs hL k (by omega)
      rw [← hc rootP (by decide)] at hr
      have hn := pNext hw hs hL k (by omega)
      have E := partEnd (okIn hw hs (by have := (pFirst hw hs hL (k + 1) (by omega)).1; omega)) (rowLt hw hs _)
        (rowLt hw hs _) hq hpl hr
      rw [hn, hc UpsV3.rc (by decide), hc kRDB (by decide), hc kRDE (by decide)] at E
      have e1 := ih (k + 1) (by omega) (by omega)
      have := rdCount_le (fun k => (F k).1) (k + 1) (ps.length - (k + 1))
      rw [show ps.length - k = (ps.length - (k + 1)) + 1 by omega]
      simp only [rdCount]
      have e2 := E.2.2.2.2.1
      rw [Nat.add_assoc, rdv k hk, e1] at e2
      rw [← e2, Nat.mod_eq_of_lt (by split <;> omega)]
      omega
  have rcnt : ∀ k (hk : k < ps.length), s.row ps[k].1 UpsV3.rc = rdCount (fun k => (F k).1) k (ps.length - k) :=
    fun k hk => RC (ps.length - k - 1) k hk (by omega)
  -- the number of parts
  have hpos := hL.nonempty
  have last := ps.length - 1
  obtain ⟨hltL, hqL, hpL⟩ := pFirst hw hs hL (ps.length - 1) (by omega)
  have hrL := (pRoot hw hs hL (ps.length - 1) (by omega)).2 (by omega)
  have RP := rootPart (okRow hw hs hltL) (rowLt hw hs _) (nextLt hw hs _) hqL hrL
  have hnQ := segNQ (okRow hw hs hlen0) (rowLt hw hs 0) (nextLt hw hs 0) h1 h2 h3 hsf ecs eti edd
  rw [SC _ hltL _ mnQ] at RP
  have hjL := hj (ps.length - 1) (by omega)
  have dD := dep0 (ps.length - 1) (by omega) di h3
  have hdP := rowLt hw hs 0 (176 + di)
  have hlenEq : ps.length = nTof ci ti + s.row 0 (176 + di) := by
    rcases Nat.lt_or_ge (ps.length - 1) (nTof ci ti) with hlt' | hge
    · have hu := ((PP _ (by omega)).1 hlt').2
      have := (HP _ (by omega)).1 hu
      rw [RP.1, dD] at this
      rw [← this, Nat.add_zero, Nat.mod_eq_of_lt (by unfold P; omega)] at hnQ
      omega
    · have hu := ((PP _ (by omega)).2 hge).2
      have := (HP _ (by omega)).2.1 hu
      rw [RP.1, dD, Nat.zero_add, hjL, show ps.length - 1 + 1 = ps.length by omega,
        Nat.mod_eq_of_lt (by unfold P; omega)] at this
      have hlt : s.row 0 (176 + di) + nTof ci ti < P := by
        apply Classical.byContradiction; intro hne
        have hge' : P ≤ s.row 0 (176 + di) + nTof ci ti := by omega
        have : (s.row 0 (176 + di) + nTof ci ti) % P = s.row 0 (176 + di) + nTof ci ti - P := by
          rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]
        omega
      rw [Nat.mod_eq_of_lt hlt] at this
      omega
  refine ⟨⟨h1, h2, h3, h4⟩, seg, hF, hlenEq, ?_, ?_, rcnt, ?_, ?_, ?_, ?_, fun k hk => pRoot hw hs hL k hk⟩
  · intro k hk hT
    obtain ⟨e1, e2⟩ := (PP k hk).1 hT
    obtain ⟨f1, -, -, -⟩ := hF k hk
    have tk := termKind h1 h2 hT f1 e1
    have H := HP k hk
    refine ⟨e1, tk.1, tk.2, e2, H.2.2.1 e2, H.2.2.2.2.1 (by omega) tk.1, ?_⟩
    rw [H.1 e2, dep0 k hk di h3]
  · intro k hk hT
    obtain ⟨e1, e2⟩ := (PP k hk).2 hT
    refine ⟨e1, e2, ?_⟩
    have := (HP k hk).2.1 e2
    rw [hj k hk, dep0 k hk di h3] at this
    have hpd := rowLt hw hs ps[k].1 pdep
    have e : (s.row 0 (176 + di) + nTof ci ti) % P = ps.length := by
      rw [Nat.mod_eq_of_lt (by unfold P; omega)]; omega
    rw [e] at this
    have : s.row ps[k].1 pdep + (k + 1) = ps.length := by
      rcases Nat.lt_or_ge (s.row ps[k].1 pdep + (k + 1)) P with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at this; exact this
      · have : (s.row ps[k].1 pdep + (k + 1)) % P = s.row ps[k].1 pdep + (k + 1) - P := by
          rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by unfold P at hpd ⊢; omega)]
        omega
    omega
  · -- every descend counted
    have := rcnt 0 hpos
    rw [((HP 0 hpos).2.2.1 ((PP 0 hpos).1 (by omega)).2), Nat.sub_zero] at this
    exact this.symm
  · intro k hk hd
    exact (HP k hk).2.2.2.1 (by omega) hd
  · intro k hk hn
    have := (HP k hk).2.2.2.2.2 hn
    obtain ⟨-, f2, -, -⟩ := hF k hk
    rw [N0 k hk _ f2, dep0 k hk _ f2] at this
    exact this
  · intro k hk
    obtain ⟨hlt, hq, hpl, hc⟩ := pLast hw hs hL k (by omega)
    have hr := rootP0 hw hs hL k hk
    rw [← hc rootP (by decide)] at hr
    have hn := pNext hw hs hL k hk
    have E := partEnd (okIn hw hs (by have := (pFirst hw hs hL (k + 1) hk).1; omega)) (rowLt hw hs _)
      (rowLt hw hs _) hq hpl hr
    rw [hn, hc sN (by decide)] at E
    exact E.2.2.2.2.2

end

/-- **Layer 2, the part plan**: every segment with a layout has a part plan. -/
theorem ups_plan {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)}
    {fls : List (List (Nat × Nat))} {ws : List Nat} (hL : UpsLayout s L ps fls ws) :
    ∃ ci ti di si kd sdx, UpsPlan s ps ci ti di si kd sdx :=
  ups_plan_seg hw hs hL

end ZkFormal.NearV3.UpsRows
