import ZkFormal.Chacha.Shuffle.Basic

/-!
# ZkFormal.Chacha.Shuffle.Walk — instances of `shufV3`

Hypothesis `GenRecv`: every step row's `busGen` receive is a `gen_index` result
(`Rng.genMsg key kq (q+1) j kn` with `genAt 64 (q+1) key kq = some (j, kn)`); this follows
from `genIndex_sound` when the stream table is the only sender on `busGen`.

`walkStart`: every active row belongs to an instance starting at an `st` row `s`; along the
instance `q` decreases by one per row, and `inst, L, lid, ks, key` are constant, `inst = s`.
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table NearSpecV3
open ZkFormal.Chacha.Rng (ofNat_inj eval_c)

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The key of row `r`. -/
def skey (tr : Trace Fp) (t r : Nat) : List Nat :=
  (List.range 8).map fun j => cv tr t r (colK j 0) + 65536 * cv tr t r (colK j 1)

/-- The `busGen` message received on row `r`. -/
def genRecvMsg (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List Fp :=
  (keyMsg ++ [ZkFormal.Chacha.Table.E.c colKq, .add (ZkFormal.Chacha.Table.E.c colQ) (ZkFormal.Chacha.Table.E.k 1),
    ZkFormal.Chacha.Table.E.c colJ, ZkFormal.Chacha.Table.E.c colKn]).map (·.eval tr t r pub)

/-- Every step row receives a `gen_index` result. -/
def GenRecv (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height t → cv tr t r colA = 1 → cv tr t r colFin = 0 →
    ∃ key kstart n j kend, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ 1 ≤ n ∧ n < 2 ^ 14 ∧
      kstart < 2013265921 ∧ kend < 2 ^ 30 + 1 ∧ genAt 64 n key kstart = some (j, kend) ∧
      genRecvMsg tr t r pub = Rng.genMsg key kstart n j kend

/-- Decoding a step row's `gen_index` receive. -/
theorem step_info (hG : GenRecv tr t pub) {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1)
    (hf : cv tr t r colFin = 0) :
    cv tr t r colQ + 1 < 2 ^ 14 ∧ cv tr t r colJ ≤ cv tr t r colQ ∧
    genAt 64 (cv tr t r colQ + 1) (skey tr t r) (cv tr t r colKq) = some (cv tr t r colJ, cv tr t r colKn) ∧
    (skey tr t r).length = 8 ∧ (∀ x ∈ skey tr t r, x < 2 ^ 32) := by
  obtain ⟨key, kstart, n, j, kend, hk, hkey, hn1, hn2, hks, hke, hgen, hmsg⟩ := hG r hr ha hf
  have hj : j < n := genAt_lt hgen (by omega) (by omega)
  unfold genRecvMsg Rng.genMsg at hmsg
  simp only [List.map_append, keyMsg, List.map_map] at hmsg
  obtain ⟨h1, h2⟩ := List.append_inj hmsg (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h2
  obtain ⟨hkq, hq, hjj, hkn, -⟩ := h2
  rw [eval_c] at hkq hjj hkn
  have hq' : (Expr.add (ZkFormal.Chacha.Table.E.c colQ) (ZkFormal.Chacha.Table.E.k 1)).eval tr t r pub =
      Fp.ofNat ((cv tr t r colQ + 1) % 2013265921) := by
    rw [eval_eq]; simp only [zev_add, zev_c, zev_k, cur_cv]
    rw [← Int.natCast_add, intCast_ofNat]
    apply Fp.ext; simp [Fp.toNat_ofNat, P]
  rw [hq'] at hq
  have eq := ofNat_inj (Nat.mod_lt _ (by decide)) (by omega) hq
  have ekq := ofNat_inj (cv_lt _ _) hks hkq
  have ej := ofNat_inj (cv_lt _ _) (by omega) hjj
  have ekn := ofNat_inj (cv_lt _ _) (by omega) hkn
  have hqlt : cv tr t r colQ + 1 < 2013265921 := by
    have := cv_lt (tr := tr) (t := t) r colQ
    rcases Nat.lt_or_ge (cv tr t r colQ + 1) 2013265921 with h | h
    · exact h
    · have e : cv tr t r colQ + 1 = 2013265921 := by omega
      rw [e, Nat.mod_self] at eq; omega
  rw [Nat.mod_eq_of_lt hqlt] at eq
  have hK : ∀ jj l, jj < 8 → l < 2 → cv tr t r (colK jj l) = (key.getD jj 0 / 2 ^ (16 * l)) % 65536 := by
    intro jj l hjj hl
    have := congrArg (·.getD (2 * jj + l) 0) h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 2 * jj + l < 16 by omega),
      Option.map_some, Option.getD_some, Function.comp, eval_c] at this
    rw [← List.getD_eq_getElem?_getD, show (2 * jj + l) / 2 = jj by omega,
      show (2 * jj + l) % 2 = l by omega] at this
    exact ofNat_inj (cv_lt _ _) (by have := Nat.mod_lt (key.getD jj 0 / 2 ^ (16 * l)) (show 65536 > 0 by decide); omega) this
  have hsk : skey tr t r = key := by
    apply List.ext_getElem (by simp [skey, hk])
    intro jj h1 h2
    simp only [skey, List.getElem_map, List.getElem_range]
    have hjj : jj < 8 := by simp [skey] at h1; exact h1
    rw [hK jj 0 hjj (by decide), hK jj 1 hjj (by decide)]
    have := hkey (key[jj]) (List.getElem_mem _)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    simp; omega
  refine ⟨by omega, by omega, ?_, by rw [hsk]; exact hk, by rw [hsk]; exact hkey⟩
  rw [hsk, ekq, eq, ej, ekn]; exact hgen

section
variable (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
include hL hG

/-- A step row is not the last row, and its `q` is `≥ 1`; the next row has `q − 1`. -/
theorem step_next {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) (hf : cv tr t r colFin = 0) :
    r + 1 < tr.height t ∧ 1 ≤ cv tr t r colQ ∧ cv tr t (r + 1) colQ + 1 = cv tr t r colQ := by
  have hlast : r + 1 < tr.height t := by
    rcases Nat.lt_or_ge (r + 1) (tr.height t) with h | h
    · exact h
    · exfalso
      have hr1 : r + 1 = tr.height t := by omega
      -- the transition at the last row reads row 0
      have hz := hL.zc hr (mem_cM (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub
        (ZkFormal.Chacha.Table.E.n colA) (ZkFormal.Chacha.Table.E.n colSt)) gStep) (by simp [cM]))
      simp only [zev_sub, zev_n, zev_c, cur_cv, gStep, ha, hf] at hz
      have hn : ∀ x, (tenv tr t r pub).nxt x = cv tr t 0 x := fun x => by
        show (tr.cell t ((r + 1) % tr.height t) x).toNat = _; rw [hr1, Nat.mod_self]; rfl
      rw [hn, hn] at hz
      have := bA hL (Nat.two_pow_pos (tr.log t)) (r := 0); have := bSt hL (Nat.two_pow_pos (tr.log t)) (r := 0)
      have e := hz (by omega) (by omega)
      have ha0 : cv tr t 0 colA = 1 := by omega
      have := first_start hL ha0; omega
  obtain ⟨ha1, -, hq1, -⟩ := cont hL hlast ha hf
  have hq0 : 1 ≤ cv tr t r colQ := by
    rcases Nat.eq_zero_or_pos (cv tr t r colQ) with h0 | h0
    · exfalso
      rw [h0] at hq1
      have hc := cv_lt (tr := tr) (t := t) (r + 1) colQ
      have e : cv tr t (r + 1) colQ = 2013265920 := by
        rcases Nat.lt_or_ge (cv tr t (r + 1) colQ + 1) 2013265921 with h | h
        · rw [Nat.mod_eq_of_lt h] at hq1; omega
        · omega
      -- row `r + 1` is active: a step needs `q + 1 < 2^14`, a final row needs `q = 0`
      have := bFin hL hlast
      rcases (show cv tr t (r + 1) colFin = 0 ∨ cv tr t (r + 1) colFin = 1 by omega) with hf1 | hf1
      · have := (step_info hG hlast ha1 hf1).1; omega
      · have := (fin_facts hL hlast hf1).1; omega
    · exact h0
  refine ⟨hlast, hq0, ?_⟩
  have hc := cv_lt (tr := tr) (t := t) (r + 1) colQ
  rcases Nat.lt_or_ge (cv tr t (r + 1) colQ + 1) 2013265921 with h | h
  · rw [Nat.mod_eq_of_lt h] at hq1; exact hq1
  · have e : cv tr t (r + 1) colQ + 1 = 2013265921 := by omega
    rw [e, Nat.mod_self] at hq1; omega

/-- **Every active row belongs to an instance.** -/
theorem walkStart (hH : tr.height t ≤ 2 ^ 20) : ∀ r, r < tr.height t → cv tr t r colA = 1 →
    ∃ s, s ≤ r ∧ cv tr t s colSt = 1 ∧ ∀ x, s ≤ x → x ≤ r →
      cv tr t x colA = 1 ∧ (x < r → cv tr t x colFin = 0) ∧ (s < x → cv tr t x colSt = 0) ∧
      cv tr t x colQ + (x - s) = cv tr t s colQ ∧ cv tr t x colInst = s ∧
      cv tr t x colL = cv tr t s colL ∧ cv tr t x colLid = cv tr t s colLid ∧
      cv tr t x colKs = cv tr t s colKs ∧ skey tr t x = skey tr t s ∧
      (x < r → cv tr t (x + 1) colKq = cv tr t x colKn) := by
  intro r
  induction r with
  | zero =>
    intro hr ha
    have hst := first_start hL ha
    refine ⟨0, Nat.le_refl _, hst, fun x h1 h2 => ?_⟩
    have hx : x = 0 := by omega
    subst hx
    exact ⟨ha, fun h => absurd h (by omega), fun h => absurd h (by omega), by simp,
      (start_facts hL hH hr hst).2.2, rfl, rfl, rfl, rfl, fun h => absurd h (by omega)⟩
  | succ r ih =>
    intro hr ha
    have := bSt hL hr
    rcases (show cv tr t (r + 1) colSt = 1 ∨ cv tr t (r + 1) colSt = 0 by omega) with hst | hst
    · refine ⟨r + 1, Nat.le_refl _, hst, fun x h1 h2 => ?_⟩
      have hx : x = r + 1 := by omega
      subst hx
      exact ⟨ha, fun h => absurd h (by omega), fun h => absurd h (by omega), by simp,
        (start_facts hL hH hr hst).2.2, rfl, rfl, rfl, rfl, fun h => absurd h (by omega)⟩
    · -- the previous row is a step of the same instance
      have t0 := trans0 hL hr; rw [ha, hst] at t0
      have := bA hL (show r < _ by omega); have := bFin hL (show r < _ by omega)
      have ha' : cv tr t r colA = 1 := by omega
      have hf' : cv tr t r colFin = 0 := by omega
      obtain ⟨s, hs, hst0, hall⟩ := ih (by omega) ha'
      obtain ⟨-, -, -, hL1, hlid1, hinst1, hks1, hkq1, hK1⟩ := cont hL hr ha' hf'
      obtain ⟨-, -, hq1⟩ := step_next hL hG (show r < _ by omega) ha' hf'
      refine ⟨s, by omega, hst0, fun x h1 h2 => ?_⟩
      rcases Nat.lt_or_ge x (r + 1) with hx | hx
      · obtain ⟨a1, -, s1, q1, i1, l1, d1, k1, key1, kq1⟩ := hall x h1 (by omega)
        refine ⟨a1, fun _ => ?_, s1, q1, i1, l1, d1, k1, key1, fun _ => ?_⟩
        · rcases Nat.lt_or_ge x r with h' | h'
          · exact (hall x h1 (by omega)).2.1 h'
          · rw [show x = r by omega]; exact hf'
        · rcases Nat.lt_or_ge x r with h' | h'
          · exact kq1 h'
          · rw [show x = r by omega]; exact hkq1
      · have hx' : x = r + 1 := by omega
        subst hx'
        obtain ⟨-, -, -, q0, i0, l0, d0, k0, key0, -⟩ := hall r hs (Nat.le_refl _)
        refine ⟨ha, fun h => absurd h (by omega), fun _ => hst, by omega, by rw [hinst1, i0],
          by rw [hL1, l0], by rw [hlid1, d0], by rw [hks1, k0], ?_, fun h => absurd h (by omega)⟩
        rw [← key0]; unfold skey; apply List.map_congr_left; intro j hj
        have hj' := List.mem_range.mp hj
        rw [hK1 j 0 hj' (by decide), hK1 j 1 hj' (by decide)]

end

end ZkFormal.Chacha.Shuffle
