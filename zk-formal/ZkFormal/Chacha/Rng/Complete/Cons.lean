import ZkFormal.Chacha.Rng.Complete.Rows

/-!
# ZkFormal.Chacha.Rng.Complete.Cons — every `genV3` constraint vanishes on honest row pairs

`HEnv Z X Y`: the integer environment `Z` reads row `X` (current) and `Y` (next).  On every
legal pair (`Step X Y`, with the `isFirst` side condition) every constraint has integer value
`0` (`row_ok`):

* `cB` (bits), `cH` (leading bit of `n`) read only the current row;
* `cM` is reduced to integer identities between the row's values (`cM_ok`), instantiated for
  draw rows (`cM_draw`, by `lemire` / `m1_lt_iff`) and padding (`cM_pad`);
* `cK` and the `gCont · _` constraints only bite inside a call (`Step.cont`).
-/

namespace ZkFormal.Chacha.Rng.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table ZkFormal.Chacha.Rng.Gen
open NearSpecV3

/-- `Z` reads row `X` (current) and row `Y` (next). -/
structure HEnv (Z : ZEnv) (X Y : Row) : Prop where
  cur : ∀ c, Z.cur c = rowCell X c
  nxt : ∀ c, Z.nxt c = rowCell Y c

theorem start_a_st {Y : Row} (hY : StartOk Y) : rowCell Y colA = rowCell Y colSt := by
  rcases hY with rfl | ⟨C, rfl⟩
  · rfl
  · show drawCell C 0 colA = drawCell C 0 colSt
    rw [g_a (g := drawCell C 0) (fun _ => rfl), g_st (g := drawCell C 0) (fun _ => rfl)]; rfl

theorem zev_gCont {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) :
    zev Z gCont = (rowCell X colA : Int) * (1 - (rowCell X colAcc : Int)) := by
  simp [gCont, h.cur]

/-! ## Booleanity and the leading bit -/

theorem complete_cB {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) : ∀ e ∈ cB, zev Z e = 0 := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have := rowCell_bool X hx
  simp only [ZkFormal.Chacha.Table.boolC, zev_mul, zev_sub, zev_c, zev_k, h.cur]
  rcases (show rowCell X x = 0 ∨ rowCell X x = 1 by omega) with e | e <;> rw [e] <;> decide

theorem sum_map_zero' {α : Type} : ∀ l : List α, (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_map_zero' l]

theorem sum_onehot : ∀ L, L < 14 → ((List.range 14).map fun i => if i = L then 1 else 0).sum = 1 := by
  decide

theorem complete_cH {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hv : Valid X) : ∀ e ∈ cH, zev Z e = 0 := by
  intro e he
  simp only [cH, List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at he
  cases X with
  | pad =>
    have h0 : ∀ c, Z.cur c = 0 := h.cur
    rcases he with (rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [zev_sub, zev_sumc, zev_c, h0]; simp [h0, sum_map_zero']
    · simp [h0]
    · rw [zev_mul, zev_c, h0]; simp
  | draw C d =>
    have hg : ∀ c, Z.cur c = drawCell C d c := h.cur
    have h1 := hv.1.2.2.1; have h2 := hv.1.2.2.2.1
    have hL := (topBit_facts h1 h2).1
    rcases he with (rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [zev_sub, zev_sumc, zev_c, g_a hg]
      have e : ((List.range 14).map fun x => Z.cur (colH x)) =
          (List.range 14).map fun x => if x = topBit C.n then 1 else 0 :=
        List.map_congr_left (fun x hx => g_H hg (List.mem_range.mp hx))
      rw [e, sum_onehot _ hL]; rfl
    · simp only [zev_mul, zev_sub, zev_c, zev_k, g_H hg hi, g_N hg hi]
      by_cases e : i = topBit C.n
      · subst e; rw [bt_lead h1 h2]; simp
      · simp [e]
    · rw [zev_mul, zev_c, zev_sumc, g_H hg hi]
      by_cases e : i = topBit C.n
      · subst e
        have e2 : ((List.range' (topBit C.n + 1) (13 - topBit C.n)).map fun x => Z.cur (colN x)) =
            (List.range' (topBit C.n + 1) (13 - topBit C.n)).map fun _ => 0 :=
          List.map_congr_left (fun x hx => by
            have := List.mem_range'_1.mp hx
            rw [g_N hg (by omega), bt_above h1 h2 (by omega)])
        rw [e2, sum_map_zero']; simp
      · simp [e]

/-! ## Lemire product, flags, call structure (`cM`) -/

theorem cM_ok {Z : ZEnv} {a acc st nn vl vh M0 C0 M1 M2 DL ZZ att kk ks : Nat}
    (ha : Z.cur colA = a) (hacc : Z.cur colAcc = acc) (hst : Z.cur colSt = st)
    (ha1 : a ≤ 1) (hacc1 : acc ≤ 1)
    (hvl : Z.cur colVlo = vl) (hvh : Z.cur colVhi = vh) (hks : Z.cur colKs = ks)
    (hn : zev Z nE = (nn : Int)) (hm0 : zev Z m0E = (M0 : Int)) (hc0 : zev Z c0E = (C0 : Int))
    (hm1 : zev Z m1E = (M1 : Int)) (hm2 : zev Z m2E = (M2 : Int)) (hdl : zev Z dlE = (DL : Int))
    (hz : zev Z zE = (ZZ : Int)) (hatt : zev Z attE = (att : Int)) (hk : zev Z kE = (kk : Int))
    (r1 : vl * nn = M0 + 65536 * C0) (r2 : vh * nn + C0 = M1 + 65536 * M2)
    (r3 : (acc = 1 ∧ M1 < ZZ ∧ DL = ZZ - 1 - M1) ∨ (acc = 0 ∧ ZZ ≤ M1 ∧ DL = M1 - ZZ))
    (r4 : acc = 1 → a = 1) (r5 : st = 1 → a = 1) (r6 : st = 1 → att = 0) (r7 : st = 1 → ks = kk)
    (r8 : Z.first = 0 ∨ a = st) (hst1 : st ≤ 1)
    (r9 : (Z.nxt colA : Int) - Z.nxt colSt = (a : Int) * (1 - (acc : Int)))
    (r10 : a = 1 → acc = 0 → zev Z (num colN 14 true) = (nn : Int) ∧ Z.nxt colKs = ks ∧
      zev Z kN = (kk : Int) + 1 ∧ zev Z (num colAtt 6 true) = (att : Int) + 1) :
    ∀ e ∈ cM, zev Z e = 0 := by
  have hg : zev Z gCont = (a : Int) * (1 - (acc : Int)) := by simp [gCont, ha, hacc]
  have gz : ∀ x : Int, (a = 1 → acc = 0 → x = 0) → (a : Int) * (1 - (acc : Int)) * x = 0 := by
    intro x hx
    rcases (show a = 0 ∨ a = 1 by omega) with e1 | e1
    · subst e1; simp
    rcases (show acc = 0 ∨ acc = 1 by omega) with e2 | e2
    · rw [hx e1 e2]; simp
    · subst e2; simp
  have c1 := congrArg (fun x : Nat => (x : Int)) r1
  have c2 := congrArg (fun x : Nat => (x : Int)) r2
  simp only [Int.natCast_mul, Int.natCast_add] at c1 c2
  intro e he
  simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [zev_sub, zev_mul, zev_add, zev_smul, zev_c, hvl, hn, hm0, hc0]; omega
  · simp only [zev_sub, zev_mul, zev_add, zev_smul, zev_c, hvh, hn, hc0, hm1, hm2]; omega
  · simp only [zev_sub, zev_mul, zev_c, zev_k, hacc, hz, hm1, hdl]
    rcases r3 with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> subst e1 <;> omega
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hacc, ha]
    rcases (show acc = 0 ∨ acc = 1 by omega) with e1 | e1
    · subst e1; simp
    · rw [r4 e1, e1]; simp
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hst, ha]
    rcases (show st = 0 ∨ st = 1 by omega) with e1 | e1
    · subst e1; simp
    · rw [r5 e1, e1]; simp
  · simp only [zev_mul, zev_c, hst, hatt]
    rcases (show st = 0 ∨ st = 1 by omega) with e1 | e1
    · subst e1; simp
    · rw [r6 e1]; simp
  · simp only [zev_mul, zev_sub, zev_c, hst, hks, hk]
    rcases (show st = 0 ∨ st = 1 by omega) with e1 | e1
    · subst e1; simp
    · rw [r7 e1]; simp
  · simp only [zev_mul, zev_isFirst, zev_sub, zev_c, ha, hst]
    rcases r8 with e1 | e1
    · rw [e1]; simp
    · rw [e1]; simp
  · simp only [zev_sub, zev_n, hg]; omega
  · rw [zev_mul, hg]; apply gz; intro e1 e2
    rw [zev_sub, (r10 e1 e2).1, hn]; simp
  · rw [zev_mul, hg]; apply gz; intro e1 e2
    rw [zev_sub, zev_n, zev_c, (r10 e1 e2).2.1, hks]; simp
  · rw [zev_mul, hg]; apply gz; intro e1 e2
    rw [zev_sub, (r10 e1 e2).2.2.1, zev_add, hk, zev_k]; simp
  · rw [zev_mul, hg]; apply gz; intro e1 e2
    rw [zev_sub, (r10 e1 e2).2.2.2, zev_add, hatt, zev_k]; simp

theorem stOf_one {d : Nat} (h : stOf d = 1) : d = 0 := by
  unfold stOf at h; split at h <;> omega

theorem cM_draw {Z : ZEnv} {C : Call} {d : Nat} {Y : Row} (h : HEnv Z (.draw C d) Y)
    (hC : CallOk C) (hd : d < nd C) (hf : Z.first = 0 ∨ (Z.first = 1 ∧ StartOk (.draw C d)))
    (hY : (d + 1 < nd C ∧ Y = .draw C (d + 1)) ∨ (d + 1 = nd C ∧ StartOk Y)) :
    ∀ e ∈ cM, zev Z e = 0 := by
  have hg : ∀ c, Z.cur c = drawCell C d c := h.cur
  have hn1 := hC.2.2.1; have hn2 := hC.2.2.2.1
  have hL := (topBit_facts hn1 hn2).1
  have hlm := lemire C d hn2
  have h64 := nd_le hC
  have hn : zev Z nE = (C.n : Int) := by rw [nE, znumC, gn_N hg hn2]
  have hz : zev Z zE = (zOf C.n : Int) := by
    rw [zE, zev_sel Z colH 14 _ (topBit C.n) hL (by rw [g_H hg hL, if_pos rfl])
      (fun x hx hne => by rw [g_H hg hx, if_neg hne]), zev_smul, hn, zOf]
    rw [Int.natCast_mul, Int.mul_comm]
  have hk : zev Z kE = (kOf C d : Int) := by
    rw [kE, zev_add, zev_smul, zev_c, g_ctr hg, idxE, znumC, gn_idx hg]
    have := Nat.div_add_mod (kOf C d) 16
    omega
  have hacc : accOf C d ≤ 1 := by unfold accOf; split <;> omega
  have hst1 : stOf d ≤ 1 := by unfold stOf; split <;> omega
  refine cM_ok (a := 1) (acc := accOf C d) (st := stOf d) (nn := C.n) (vl := vlo C d) (vh := vhi C d)
    (M0 := m0 C d) (C0 := c0 C d) (M1 := m1 C d) (M2 := m2 C d) (DL := dlOf C d) (ZZ := zOf C.n)
    (att := d) (kk := kOf C d) (ks := C.kstart)
    (g_a hg) (g_acc hg) (g_st hg) (by omega) hacc (g_vlo hg) (g_vhi hg) (g_ks hg) hn
    (by rw [m0E, znumC, gn_M0 hg hn2]) (by rw [c0E, znumC, gn_C0 hg hn2])
    (by rw [m1E, znumC, gn_M1 hg hn2]) (by rw [m2E, znumC, gn_M2 hg hn2])
    (by rw [dlE, znumC, gn_Dl hg hC hd]) hz
    (by rw [attE, znumC, gn_Att hg (by omega)]) hk
    hlm.2.2.1 hlm.2.2.2.1 ?r3 (fun _ => rfl) (fun _ => rfl)
    (fun e => stOf_one e) (fun e => by have := stOf_one e; unfold kOf; omega) ?r8 hst1 ?r9 ?r10
  case r3 =>
    have hiff := m1_lt_iff hC hd
    unfold dlOf accOf
    by_cases e : d + 1 = nd C
    · left; rw [if_pos e, if_pos e]; exact ⟨rfl, hiff.2 e, rfl⟩
    · right; rw [if_neg e, if_neg e]
      exact ⟨rfl, by have := mt hiff.1 e; omega, rfl⟩
  case r8 =>
    rcases hf with hf | ⟨-, hs⟩
    · exact Or.inl hf
    · right
      rcases hs with hs | ⟨C', hs⟩
      · cases hs
      · injection hs with _ hd0; subst hd0; rfl
  case r9 =>
    rcases hY with ⟨hd1, rfl⟩ | ⟨hd1, hYs⟩
    · have hgY : ∀ c, Z.nxt c = drawCell C (d + 1) c := h.nxt
      rw [hgY, hgY, g_a (g := drawCell C (d + 1)) (fun _ => rfl),
        g_st (g := drawCell C (d + 1)) (fun _ => rfl)]
      unfold accOf stOf; rw [if_neg (by omega), if_neg (by omega)]; rfl
    · rw [h.nxt, h.nxt, start_a_st hYs]; unfold accOf; rw [if_pos hd1]; simp
  case r10 =>
    intro _ e2
    rcases hY with ⟨hd1, rfl⟩ | ⟨hd1, -⟩
    · have hgY : ∀ c, Z.nxt c = drawCell C (d + 1) c := h.nxt
      refine ⟨by rw [znumN, gn_N hgY hn2], g_ks hgY, ?_, ?_⟩
      · rw [kN, zev_add, zev_smul, zev_n, g_ctr hgY, znumN, gn_idx hgY]
        have := Nat.div_add_mod (kOf C (d + 1)) 16
        unfold kOf at *; omega
      · rw [znumN, gn_Att hgY (by omega)]; push_cast; rfl
    · unfold accOf at e2; rw [if_pos hd1] at e2; omega

theorem cM_pad {Z : ZEnv} {Y : Row} (h : HEnv Z .pad Y) (hY : StartOk Y) :
    ∀ e ∈ cM, zev Z e = 0 := by
  have h0 : ∀ c, Z.cur c = 0 := h.cur
  have hz0 : ∀ col len, zev Z (num col len) = ((0 : Nat) : Int) := fun col len => by
    rw [znumC, nbits_zero (fun b _ => h0 _)]
  refine cM_ok (a := 0) (acc := 0) (st := 0) (nn := 0) (vl := 0) (vh := 0) (M0 := 0) (C0 := 0)
    (M1 := 0) (M2 := 0) (DL := 0) (ZZ := 0) (att := 0) (kk := 0) (ks := 0)
    (h0 _) (h0 _) (h0 _) (by omega) (by omega) (h0 _) (h0 _) (h0 _)
    (by rw [nE]; exact hz0 _ _) (by rw [m0E]; exact hz0 _ _) (by rw [c0E]; exact hz0 _ _)
    (by rw [m1E]; exact hz0 _ _) (by rw [m2E]; exact hz0 _ _) (by rw [dlE]; exact hz0 _ _)
    (by rw [zE]; exact zev_sel_zero Z colH 14 _ (fun x _ => h0 _)) (by rw [attE]; exact hz0 _ _)
    (by rw [kE, zev_add, zev_smul, zev_c, h0, idxE, hz0]; rfl)
    rfl rfl (Or.inr ⟨rfl, Nat.le_refl _, rfl⟩) (fun e => absurd e (by decide))
    (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    (Or.inr rfl) (by omega) ?_ (fun e => absurd e (by decide))
  rw [h.nxt, h.nxt, start_a_st hY]; simp

theorem complete_cM {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y)
    (hf : Z.first = 0 ∨ (Z.first = 1 ∧ StartOk X)) : ∀ e ∈ cM, zev Z e = 0 := by
  cases hs with
  | cont C hC d hd => exact cM_draw h hC (by omega) hf (Or.inl ⟨hd, rfl⟩)
  | last C hC d hd Y hY => exact cM_draw h hC (by omega) hf (Or.inr ⟨hd, hY⟩)
  | pad Y hY => exact cM_pad h hY

/-! ## The key is constant within a call (`cK`) -/

theorem complete_cK {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y) :
    ∀ e ∈ cK, zev Z e = 0 := by
  intro e he
  simp only [cK, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, l, hl, rfl⟩ := he
  rw [zev_mul, zev_gCont h]
  cases hs with
  | cont C hC d hd =>
    rw [zev_sub, zev_n, zev_c, h.nxt, h.cur]
    show _ * (((drawCell C (d + 1) (colK j l) : Nat) : Int) - (drawCell C d (colK j l) : Nat)) = 0
    rw [g_K (g := drawCell C (d + 1)) (fun _ => rfl) hj hl, g_K (g := drawCell C d) (fun _ => rfl) hj hl]
    simp
  | last C hC d hd Y hY =>
    show ((drawCell C d colA : Nat) : Int) * (1 - (drawCell C d colAcc : Nat)) * _ = 0
    rw [g_a (g := drawCell C d) (fun _ => rfl), g_acc (g := drawCell C d) (fun _ => rfl)]
    unfold accOf; rw [if_pos hd]; simp
  | pad Y hY => show ((0 : Nat) : Int) * _ * _ = 0; simp

/-! ## All constraints -/

/-- Every constraint vanishes (as an integer) on a legal row pair. -/
theorem row_ok {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y)
    (hf : Z.first = 0 ∨ (Z.first = 1 ∧ StartOk X)) : ∀ e ∈ constraints, zev Z e = 0 := by
  intro e he
  unfold constraints at he
  simp only [List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · exact complete_cB h e he
  · exact complete_cH h hs.valid e he
  · exact complete_cM h hs hf e he
  · exact complete_cK h hs e he

end ZkFormal.Chacha.Rng.Complete
