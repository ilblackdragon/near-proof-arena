import ZkFormal.NearV3.Render.UniqGen

/-!
# ZkFormal.NearV3.Render.UniqLocal — the honest `uniqV3` table is locally legal

Constraint by constraint (as v1 `Near/Render/Proof/SortLocal.lean`), for any trace whose
table `tt` has height `H ≥ 32·|L|` and cells `Fp.ofNat (UniqGen.cell L H q col)` on
rows `q < H`, columns `col < 53`.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.Uniq (act sf sl ft eid peid tau st eq i bb cin cout dbit d diffE cmpG segConst)
open UniqGen

namespace UniqLocal

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl

section cells
variable (L : List UEnt) (H q : Nat)
theorem v_act' (h : q < 32 * L.length) (x : Nat) (hx : x < 21) : cell L H q x = actCell L q x := by
  simp [cell, h, show ¬ 21 ≤ x by omega]
theorem v_pad (h : ¬ q < 32 * L.length) (x : Nat) (hx : x < 21) : cell L H q x = 0 := by
  simp [cell, h, show ¬ 21 ≤ x by omega]
theorem v_d (j : Nat) (hj : j < 32) : cell L H q (21 + j) = bbAt L ((q + 2 * H - 1 - j) % H) := by
  simp [cell, show 21 + j < 53 by omega]
end cells

theorem mod0 {q H : Nat} (hq : q < H) : ((q + 1) % H + 2 * H - 1 - 0) % H = q := by
  by_cases hl : q + 1 < H
  · rw [Nat.mod_eq_of_lt hl, show q + 1 + 2 * H - 1 - 0 = q + H * 2 by omega, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hq
  · rw [show q + 1 = H by omega, Nat.mod_self, show 0 + 2 * H - 1 - 0 = (H - 1) + H by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem modj {q H j : Nat} (hq : q < H) (hj : j + 2 ≤ H) :
    ((q + 1) % H + 2 * H - 1 - (j + 1)) % H = (q + 2 * H - 1 - j) % H := by
  by_cases hl : q + 1 < H
  · rw [Nat.mod_eq_of_lt hl, show q + 1 + 2 * H - 1 - (j + 1) = q + 2 * H - 1 - j by omega]
  · rw [show q + 1 = H by omega, Nat.mod_self, show q + 2 * H - 1 - j = (0 + 2 * H - 1 - (j + 1)) + H by omega,
      Nat.add_mod_right]

theorem boolF {v : Nat} (h : v ≤ 1) : Fp.ofNat v * (Fp.ofNat v - 1) = 0 := by
  rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 h with rfl | rfl <;> simp only [ofNat0, ofNat1] <;> grind

theorem ofNat_succ (a : Nat) : Fp.ofNat (a + 1) = Fp.ofNat a + 1 := (ofNat_add' a 1).symm

section rows
variable {L : List UEnt} (ok : UOk L) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : 32 * L.length ≤ H)
  (hc : ∀ q col, q < H → col < 53 → tr.cell tt q col = Fp.ofNat (cell L H q col))
include ok hH hHS hc

theorem cA {q : Nat} (hq : q < H) (ha : q < 32 * L.length) {x : Nat} (hx : x < 21) :
    tr.cell tt q x = Fp.ofNat (actCell L q x) := by
  rw [hc q x hq (by omega), v_act' L H q ha x hx]

theorem cP {q : Nat} (hq : q < H) (ha : ¬ q < 32 * L.length) {x : Nat} (hx : x < 21) :
    tr.cell tt q x = 0 := by
  rw [hc q x hq (by omega), v_pad L H q ha x hx]; rfl

/-- `diffE` on an active row is the byte of `diff`. -/
theorem diffE_act {q : Nat} (hq : q < H) (ha : q < 32 * L.length) :
    diffE.eval tr tt q pub = Fp.ofNat (SortGen.byte (diffOf L (q / 32)) (q % 32)) := by
  have hb := SortGen.byte_lt (diffOf L (q / 32)) (q % 32)
  simp only [diffE, bits, List.range, List.range.loop, List.map, eval_sum_cons, eval_sum_nil, eval_smul,
    eval_c, dbit, Nat.reduceAdd, natCast_eq]
  simp only [cA ok hH hHS hc hq ha (by decide : (13 : Nat) < 21), cA ok hH hHS hc hq ha (by decide : (14 : Nat) < 21),
    cA ok hH hHS hc hq ha (by decide : (15 : Nat) < 21), cA ok hH hHS hc hq ha (by decide : (16 : Nat) < 21),
    cA ok hH hHS hc hq ha (by decide : (17 : Nat) < 21), cA ok hH hHS hc hq ha (by decide : (18 : Nat) < 21),
    cA ok hH hHS hc hq ha (by decide : (19 : Nat) < 21), cA ok hH hHS hc hq ha (by decide : (20 : Nat) < 21)]
  simp only [actCell, Nat.reduceLT, if_true, ofNat_mul', ofNat_add', ← ofNat0]
  congr 1
  simp only [Nat.reducePow]
  omega

theorem diffE_pad {q : Nat} (hq : q < H) (ha : ¬ q < 32 * L.length) : diffE.eval tr tt q pub = 0 := by
  simp only [diffE, bits, List.range, List.range.loop, List.map, eval_sum_cons, eval_sum_nil, eval_smul,
    eval_c, dbit, Nat.reduceAdd]
  simp only [cP ok hH hHS hc hq ha (by decide : (13 : Nat) < 21), cP ok hH hHS hc hq ha (by decide : (14 : Nat) < 21),
    cP ok hH hHS hc hq ha (by decide : (15 : Nat) < 21), cP ok hH hHS hc hq ha (by decide : (16 : Nat) < 21),
    cP ok hH hHS hc hq ha (by decide : (17 : Nat) < 21), cP ok hH hHS hc hq ha (by decide : (18 : Nat) < 21),
    cP ok hH hHS hc hq ha (by decide : (19 : Nat) < 21), cP ok hH hHS hc hq ha (by decide : (20 : Nat) < 21)]
  grind

theorem bools {q : Nat} (hq : q < H) {x : Nat}
    (hx : x ∈ [act, sf, sl, ft, st, eq, cin, cout] ++ (List.range 8).map dbit) :
    (Dsl.bool (c x)).eval tr tt q pub = 0 := by
  have hx21 : x < 21 := by
    simp only [act, sf, sl, ft, st, eq, cin, cout, dbit, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;> omega
  simp only [eval_bool, eval_c]
  by_cases ha : q < 32 * L.length
  · rw [cA ok hH hHS hc hq ha hx21]
    apply boolF
    simp only [act, sf, sl, ft, st, eq, cin, cout, dbit, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · simp [actCell]
    · simp only [actCell]; split <;> omega
    · simp only [actCell]; split <;> omega
    · simp only [actCell]; split <;> omega
    · exact st_le _
    · exact eq_le _
    · have := carry_bool (L := L) (q / 32) (q % 32); simp only [actCell]; omega
    · have := carry_bool (L := L) (q / 32) (q % 32 + 1); simp only [actCell]; omega
    · rw [show 13 + j = j + 13 by omega]; simp only [actCell, if_pos hj]; omega
  · rw [cP ok hH hHS hc hq ha hx21]; grind

/-- Row-only constraints. -/
theorem rowC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ Expr.mul (c sf) (Dsl.not (c act)), .mul (c sl) (Dsl.not (c act)),
      .mul .isFirst (Dsl.not (c sf)), .mul .isFirst (Dsl.not (c ft)),
      .mul .isLast (.mul (c act) (Dsl.not (c sl))),
      .mul (c sf) (c i), .mul (c sl) (sub (c i) (k 31)),
      .mul (c sf) (sub (c cin) (Dsl.not (c eq))), .mul (c sl) (c cout),
      .mul (c ft) (c eq), .mul (c eq) (c st) ]) :
    e.eval tr tt q pub = 0 := by
  have hn := ok.pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < 32 * L.length
  · have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
    have c32 := carry32 ok (L := L) (t := q / 32) (by omega)
    have c0 := carry0 (L := L) (q / 32)
    have est := eq_st (L := L) (q / 32)
    have el := eq_le (L := L) (q / 32)
    have sle := st_le (L := L) (q / 32)
    have e0 : q / 32 = 0 → eqOf L (q / 32) = 0 := fun h => by rw [h]; exact eq0
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH, act, sf, sl, ft,
      i, cin, cout, eq, st, cq, Nat.reduceLT, actCell, natCast_eq] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind)
      | (rw [ofNat_mul', est, ofNat0])
      | (rename_i h; rw [e0 h]; simp only [ofNat0, ofNat1]; grind)
      | (rename_i h; simp only [h, Nat.reduceAdd, c32, c0]
         rcases (show eqOf L (q / 32) = 0 ∨ eqOf L (q / 32) = 1 by omega) with h' | h' <;>
         simp only [h', ofNat0, ofNat1, Nat.reduceSub] <;> grind)
  · have cq := fun (x : Nat) (hx : x < 21) => cP ok hH hHS hc hq ha hx
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH, act, sf, sl, ft,
      i, cin, cout, eq, st, cq, Nat.reduceLT] <;>
    repeat' split
    all_goals first | omega | grind

theorem eqDiff {q : Nat} (hq : q < H) : (Expr.mul (c eq) diffE).eval tr tt q pub = 0 := by
  rw [eval_mul, eval_c]
  by_cases ha : q < 32 * L.length
  · rw [diffE_act ok hH hHS hc hq ha, cA ok hH hHS hc hq ha (by decide : eq < 21)]
    simp only [eq, actCell]
    rcases (show eqOf L (q / 32) = 0 ∨ eqOf L (q / 32) = 1 from
      (Nat.le_one_iff_eq_zero_or_eq_one).1 (eq_le _)) with h | h
    · rw [h, ofNat0]; grind
    · rw [eq_diff h]; simp only [SortGen.byte, Nat.zero_div, Nat.zero_mod, ofNat0]; grind
  · rw [diffE_pad ok hH hHS hc hq ha]; grind

/-- Constraints gated by `act·(1 − sl)` (within a segment). -/
theorem gateW {q : Nat} (hq : q < H) {E : Expr}
    (hE : q < 32 * L.length → q + 1 < 32 * L.length → (q + 1) / 32 = q / 32 → (q + 1) % 32 = q % 32 + 1 →
      (q + 1) % H = q + 1 → E.eval tr tt q pub = 0) :
    (mul3 (c act) (Dsl.not (c sl)) E).eval tr tt q pub = 0 := by
  simp only [eval_mul3, eval_c, eval_not]
  by_cases ha : q < 32 * L.length
  · rw [cA ok hH hHS hc hq ha (by decide : act < 21), cA ok hH hHS hc hq ha (by decide : sl < 21)]
    simp only [act, sl, actCell]
    by_cases hs : q % 32 = 31
    · simp only [hs, if_true, ofNat1]; grind
    · rw [hE ha (by omega) (by omega) (by omega) (Nat.mod_eq_of_lt (by omega))]; grind
  · rw [cP ok hH hHS hc hq ha (by decide : act < 21)]; grind

theorem within {q : Nat} (hq : q < H) {E : Expr}
    (hE : E ∈ [Dsl.not (n act), n sf, sub (n i) (.add (c i) (k 1)), sub (n cin) (c cout)] ∨
      ∃ x ∈ segConst, E = sub (n x) (c x)) :
    (mul3 (c act) (Dsl.not (c sl)) E).eval tr tt q pub = 0 := by
  apply gateW ok hH hHS hc hq
  intro ha ha' hdiv hmod hnx
  have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
  have cn := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc (q := q + 1) (by omega) ha' hx
  simp only [segConst, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with (rfl | rfl | rfl | rfl) | ⟨x, hx, rfl⟩
  · simp only [eval_not, eval_n, hH, hnx, cn, act, Nat.reduceLT, actCell, ofNat1]; grind
  · simp only [eval_n, hH, hnx, cn, sf, Nat.reduceLT, actCell, hmod]; rfl
  · simp only [eval_sub, eval_add, eval_n, eval_c, eval_k, hH, hnx, cn, cq, i, Nat.reduceLT, actCell, hmod,
      ofNat_succ, natCast_eq]; simp only [ofNat0]; grind
  · simp only [eval_sub, eval_n, eval_c, hH, hnx, cn, cq, cin, cout, Nat.reduceLT, actCell, hmod, hdiv]; grind
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_sub, eval_n, eval_c, hH, hnx, cn, cq, eid, peid, tau, st, eq, ft, Nat.reduceLT, actCell,
      hdiv] <;> grind

/-- Segment boundaries and padding. -/
theorem trans {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c sl) (n act) (Dsl.not (n sf)),
      .mul .isTransition (mul3 (c sl) (n act) (n ft)),
      .mul (mul3 (c sl) (n act) .isTransition) (sub (n peid) (c eid)),
      .mul (mul3 (c sl) (n act) .isTransition) (sub (n tau) (.add (c tau) (n st))),
      mul3 .isTransition (Dsl.not (c act)) (n act) ]) :
    e.eval tr tt q pub = 0 := by
  have hn := ok.pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < 32 * L.length
  · have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
    by_cases hs : q % 32 = 31
    · by_cases hl : q + 1 = H
      · -- wrap-around to row 0
        have hnx : (q + 1) % H = 0 := by rw [hl]; exact Nat.mod_self H
        have hl' : (q + 1 = H) = True := eq_true hl
        have c0 := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc (q := 0) (by omega) (by omega) hx
        rcases he with rfl | rfl | rfl | rfl | rfl <;>
        simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH, hnx,
          hl', if_true, cq, c0, act, sf, sl, ft, Nat.reduceLT, actCell, hs, Nat.zero_mod, Nat.zero_div] <;>
        (try simp only [ofNat0, ofNat1]) <;> grind
      · have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
        by_cases ha' : q + 1 < 32 * L.length
        · -- next segment
          have cn := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc (q := q + 1) (by omega) ha' hx
          have hdiv : (q + 1) / 32 = q / 32 + 1 := by omega
          have hmod : (q + 1) % 32 = 0 := by omega
          have hts := tau_step ok (t := q / 32) (by omega)
          rcases he with rfl | rfl | rfl | rfl | rfl <;>
          simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH,
            hnx, hl, if_false, cq, cn, act, sf, sl, ft, eid, peid, tau, st, Nat.reduceLT, actCell, hs, hdiv, hmod,
            if_true, Nat.add_one_ne_zero, peidOf, Nat.add_sub_cancel, hts, ofNat_add'] <;>
          (try simp only [ofNat0, ofNat1]) <;> grind
        · -- next row is padding
          have cn := fun (x : Nat) (hx : x < 21) => cP ok hH hHS hc (q := q + 1) (by omega) ha' hx
          rcases he with rfl | rfl | rfl | rfl | rfl <;>
          simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH,
            hnx, hl, if_false, cq, cn, act, sf, sl, ft, eid, peid, tau, st, Nat.reduceLT, actCell] <;>
          (try simp only [ofNat0, ofNat1]) <;> grind
    · rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH,
        cq, act, sl, Nat.reduceLT, actCell, hs, if_false] <;>
      (try simp only [ofNat0, ofNat1]) <;> grind
  · have cq := fun (x : Nat) (hx : x < 21) => cP ok hH hHS hc hq ha hx
    by_cases hl : q + 1 = H
    · have hl' : (q + 1 = H) = True := eq_true hl
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH,
        hl', if_true, cq, act, sl, Nat.reduceLT] <;> grind
    · have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cn := fun (x : Nat) (hx : x < 21) => cP ok hH hHS hc (q := q + 1) (by omega) (by omega) hx
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH,
        hnx, cq, cn, act, sl, Nat.reduceLT] <;> grind

theorem chain {q : Nat} (hq : q < H) :
    (Expr.mul cmpG (sub (c bb) (sub (.add (c (d 31)) (.add diffE (c cin))) (smul 256 (c cout))))).eval
      tr tt q pub = 0 := by
  simp only [cmpG, eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_smul]
  by_cases ha : q < 32 * L.length
  · have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
    by_cases hs : same L (q / 32) = true
    · obtain ⟨h0, hst⟩ := (same_iff _).1 hs
      have hmod : (q + 2 * H - 1 - 31) % H = q - 32 := by
        rw [show q + 2 * H - 1 - 31 = (q - 32) + H * 2 by omega, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [diffE_act ok hH hHS hc hq ha, hc q (d 31) hq (by decide), show d 31 = 21 + 31 from rfl,
        v_d L H q 31 (by decide), hmod]
      have hN := congrArg Fp.ofNat (chainNat ok ha hs)
      simp only [← ofNat_add', ← ofNat_mul'] at hN
      simp only [cq, act, ft, st, bb, cin, cout, Nat.reduceLT, actCell, h0, hst, if_false, natCast_eq,
        ofNat0, ofNat1]
      grind
    · have : q / 32 = 0 ∨ stOf L (q / 32) = 1 := by
        have := st_le (L := L) (q / 32)
        by_cases h0 : q / 32 = 0
        · exact Or.inl h0
        · by_cases h1 : stOf L (q / 32) = 0
          · exact absurd ((same_iff _).2 ⟨h0, h1⟩) hs
          · omega
      rcases this with h | h <;>
      simp only [cq, act, ft, st, Nat.reduceLT, actCell, h, if_true, ofNat1] <;> grind
  · simp only [cP ok hH hHS hc hq ha (by decide : act < 21)]; grind

theorem delay0 {q : Nat} (hq : q < H) :
    (Expr.mul (c act) (sub (n (d 0)) (c bb))).eval tr tt q pub = 0 := by
  have hq' : (q + 1) % H < H := Nat.mod_lt _ (by omega)
  simp only [eval_mul, eval_c, eval_n, eval_sub, hH]
  rw [hc _ _ hq' (by decide), show d 0 = 21 + 0 from rfl, v_d L H _ 0 (by decide), mod0 hq]
  by_cases ha : q < 32 * L.length
  · rw [cA ok hH hHS hc hq ha (by decide : act < 21), cA ok hH hHS hc hq ha (by decide : bb < 21)]
    simp only [act, bb, actCell, ofNat1]; grind
  · rw [cP ok hH hHS hc hq ha (by decide : act < 21)]; grind

theorem delayj {q j : Nat} (hq : q < H) (hj : j < 31) :
    (Expr.mul (c act) (sub (n (d (j + 1))) (c (d j)))).eval tr tt q pub = 0 := by
  have hn := ok.pos
  have hq' : (q + 1) % H < H := Nat.mod_lt _ (by omega)
  simp only [eval_mul, eval_c, eval_n, eval_sub, hH, d]
  rw [hc _ (21 + (j + 1)) hq' (by omega), hc q (21 + j) hq (by omega),
    v_d L H _ (j + 1) (by omega), v_d L H _ j (by omega), modj hq (by omega)]
  grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ Uniq.constraints) :
    e.eval tr tt q pub = 0 := by
  simp only [Uniq.constraints] at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · rcases List.mem_append.1 he with he | he
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
          exact bools ok hH hHS hc hq hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact rowC ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
          · exact eqDiff ok hH hHS hc hq
          · exact within ok hH hHS hc hq (Or.inl (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
          · exact within ok hH hHS hc hq (Or.inl (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
          · exact within ok hH hHS hc hq (Or.inl (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
          · exact within ok hH hHS hc hq (Or.inl (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        exact within ok hH hHS hc hq (Or.inr ⟨x, hx, rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact trans ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact trans ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact trans ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact trans ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact trans ok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact chain ok hH hHS hc hq
      · exact delay0 ok hH hHS hc hq
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact delayj ok hH hHS hc hq (List.mem_range.1 hj)

theorem multBits {q : Nat} (hq : q < H) {it : Interaction} (hi : it ∈ Uniq.interactions) {b : Expr}
    (hb : b ∈ it.mult) : b.eval tr tt q pub = 0 ∨ b.eval tr tt q pub = 1 := by
  simp only [Uniq.interactions, recv, send, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    simp only [eval_mul, eval_c]
  · by_cases ha : q < 32 * L.length
    · rw [cA ok hH hHS hc hq ha (by decide : act < 21)]; simp [act, actCell, ofNat1]
    · rw [cP ok hH hHS hc hq ha (by decide : act < 21)]; left; rfl
  · by_cases ha : q < 32 * L.length
    · rw [cA ok hH hHS hc hq ha (by decide : sf < 21), cA ok hH hHS hc hq ha (by decide : eq < 21)]
      simp only [sf, eq, actCell]
      rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 (eq_le (L := L) (q / 32)) with h | h <;> rw [h] <;>
        split <;> simp only [ofNat0, ofNat1] <;> grind
    · rw [cP ok hH hHS hc hq ha (by decide : sf < 21)]; left; grind

end rows

end UniqLocal

open UniqLocal in
/-- **The honest `uniqV3` table is locally legal.**  Hypotheses on the trace: table `t` has
`log₂` height `logOf (32·|L|)` and, on every row `r < height` and column `x < Uniq.width`,
the cell `Fp.ofNat (UniqGen.cell L height r x)` (this is what `mkTab` + `Fp.ofNat` gives for
`uniqRows L`, as for v1 `render_mkTab`; cells outside the table are unconstrained). -/
theorem uniq_render_local (L : List UEnt) (hok : UOk L) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (32 * L.length))
    (hcell : ∀ r x, r < tr.height t → x < Uniq.width →
      tr.cell t r x = Fp.ofNat (UniqGen.cell L (tr.height t) r x)) :
    TableLocal Uniq.table tr t pub := by
  have hHS : 32 * L.length ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) hok.cap
  · intro r hr e he
    exact constr hok rfl hHS hcell hr he
  · intro r hr it hi b hb
    exact multBits hok rfl hHS hcell hr hi hb

end ZkFormal.NearV3.Render
