import FinalM5d.Whole

/-!
# FinalM5d.HbWhole — `HbBytes` from `Holds finalAirS` (no premise left)

`hb_bytes`: in any trace satisfying the deployed FINAL AIR, on every active `FIN` row every
statement-stream cell `hb_k` (`k < HBN`) is below 256 — the premise `FinRow.HbBytes` of
`final_template_sound`. The chain is in `FinalM5d.Whole`'s header.
-/

namespace FinalM5d.HbWhole

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.FinRow
open FinalM5d.Whole

variable {tr : Trace Fp} {pub : List Fp}

local notation "PR" => 2013265921

theorem ev_sumE {t r : Nat} (l : List Expr) :
    ev tr t r pub (sumE l) = (l.map (ev tr t r pub)).sum % PR := by
  induction l using sumE.induct with
  | case1 => simp [sumE]
  | case2 a => simp [sumE, Nat.mod_eq_of_lt (ev_lt a)]
  | case3 a b rest h ih1 ih2 =>
    rw [sumE, ev_add, ih1, ih2, Nat.add_mod_mod, Nat.mod_add_mod, ← List.sum_append, ← List.map_append,
      List.take_append_drop]

/-! ## `RNG`: every looked-up value is a byte -/

theorem rng_bit_sub : ((List.range 8).map fun i => bool (Rng.T.c "bit" i)) ⊆ Rng.constraints := by
  intro e he; unfold Rng.constraints; exact List.mem_append_left _ he

theorem rng_v_mem : Rng.T.c "v" - Rng.bitsVal 0 8 ∈ Rng.constraints := by
  unfold Rng.constraints; exact List.mem_append_right _ List.mem_cons_self

/-- On every `RNG` row, `v < 256`. -/
theorem rng_v_lt {r : Nat} (hc : ∀ e ∈ Rng.constraints, e.eval tr 2 r pub = 0) :
    ev tr 2 r pub (Rng.T.c "v") < 256 := by
  have hb : ∀ i, i < 8 → ev tr 2 r pub (Rng.T.c "bit" i) ≤ 1 := fun i hi =>
    bool_le (hc _ (rng_bit_sub (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
  have hv := ev_sub_eq (ev_of_eval (hc _ rng_v_mem))
  rw [hv, Rng.bitsVal, ev_sumE]
  have e8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [e8]
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ev_hmul, ev_K]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.zero_add]
  have sm : ∀ c x, c ≤ 128 → x ≤ 1 → c * x % PR = c * x := fun c x hc hx =>
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul hc hx) (by decide))
  rw [sm 1 _ (by omega) b0, sm 2 _ (by omega) b1, sm 4 _ (by omega) b2, sm 8 _ (by omega) b3,
    sm 16 _ (by omega) b4, sm 32 _ (by omega) b5, sm 64 _ (by omega) b6, sm 128 _ (by omega) b7]
  simp only [Nat.one_mul, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Every `RNG` interaction's first message element is `v`. -/
theorem rng_msg0 {i : Interaction} (hi : i ∈ Rng.table.interactions) :
    ∃ es, i.msg = Rng.T.c "v" :: es := by
  simp only [Rng.table, Rng.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **A value looked up on `R8` / `S2` / `S5` (by a single-element head `x`) is a byte.** -/
theorem lookup_lt (h : Holds finalAirS pub tr) {b : Nat} (hb : b = B_R8 ∨ b = B_S2 ∨ b = B_S5)
    {m : List Fp} {x : Fp} {m' : List Fp} (hm : m = x :: m') (ho : Occ finalAirS tr pub b false m) :
    x.toNat < 256 := by
  have hs := recv_sent h ho
  have hon : onlyIn finalAirS b true [2] = true := by
    rcases hb with rfl | rfl | rfl
    · exact only_R8_send
    · exact only_S2_send
    · exact only_S5_send
  obtain ⟨t, ht2, ht, r, hr, i, hi, -, -, -, hmv⟩ := occ_in hon hs
  simp only [List.mem_singleton] at ht2
  subst ht2
  rw [tab2] at hi
  obtain ⟨es, hes⟩ := rng_msg0 hi
  have hc : ∀ e ∈ Rng.constraints, e.eval tr 2 r pub = 0 := by
    have := h.constr 2 (by decide) r hr
    rw [tab2] at this; exact this
  have hv := rng_v_lt hc
  simp only [Interaction.msgVal, hes, List.map_cons, hm, List.cons.injEq] at hmv
  rw [← hmv.1]
  exact hv

/-! ## `S384`: a received data byte is looked up -/

/-- The `S384` constraints the flag argument needs. -/
theorem s384_mono_sub :
    ((List.range 127).map fun i => S384.T.c "f" (i + 1) * (1 - S384.T.c "f" i)) ⊆ S384.constraints := by
  intro e he; unfold S384.constraints
  simp only [List.mem_append]; simp only [he, true_or, or_true]

theorem s384_f0_mem : S384.T.c "f" 0 * (1 - S384.act) ∈ S384.constraints := by
  unfold S384.constraints
  simp only [List.mem_append, List.mem_cons]
  simp only [true_or, or_true]

theorem f_zero {r : Nat} (hc : ∀ e ∈ S384.constraints, e.eval tr 1 r pub = 0) :
    ∀ j, j < 128 → ev tr 1 r pub (S384.T.c "f" j) = 1 → ev tr 1 r pub (S384.T.c "f" 0) = 1
  | 0, _, h => h
  | j + 1, hj, h1 => by
    have := hc _ (s384_mono_sub (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩))
    exact f_zero hc j (by omega) (one_sub (gated this h1))

/-- The byte lookups of an `S384` row. -/
theorem s384_lk_sub :
    ((List.range 16).flatMap fun w =>
      [rcv B_S5 S384.act [S384.T.c "b" (8 * w + 5), S384.T.c "s5lo" w, S384.T.c "s5hi" w],
       rcv B_S2 S384.act [S384.T.c "b" (8 * w + 2), S384.T.c "s2lo" w, S384.T.c "s2hi" w]] ++
      ([0, 1, 3, 4, 6, 7].map fun i => rcv B_R8 S384.act [S384.T.c "b" (8 * w + i)])) ⊆
      S384.interactions := by
  intro e he; unfold S384.interactions
  simp only [List.mem_append]; simp only [he, true_or, or_true]

/-- The data-byte receives of `S384`, and the rest has nothing on `SB` (receive side). -/
theorem s384_sb_recv {i : Interaction} (hi : i ∈ S384.interactions) (hb : i.bus = B_SB)
    (hs : i.send = false) :
    ∃ j, j < 128 ∧ i = rcv B_SB (S384.T.c "f" j) [S384.T.c "id", S384.T.c "cnt" + K j, S384.T.c "b" j] := by
  unfold S384.interactions at hi
  simp only [List.mem_append] at hi
  rcases hi with (((h1 | h2) | h3) | h4) | h5
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h1
    exact ⟨j, List.mem_range.1 hj, rfl⟩
  · exact (not_mem_of_noneOn (by decide +kernel) h2 hb hs).elim
  · exact (not_mem_of_noneOn (by decide +kernel) h3 hb hs).elim
  · exact (not_mem_of_noneOn (by decide +kernel) h4 hb hs).elim
  · exact (not_mem_of_noneOn (by decide +kernel) h5 hb hs).elim

/-- **A byte an `S384` row receives on `SB` is below 256.** -/
theorem s384_recv_lt (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 1) {j : Nat}
    (hj : j < 128) (hf : (S384.T.c "f" j).eval tr 1 r pub = 1) :
    ev tr 1 r pub (S384.T.c "b" j) < 256 := by
  have hc : ∀ e ∈ S384.constraints, e.eval tr 1 r pub = 0 := by
    have := h.constr 1 (by decide) r hr
    rw [tab1] at this; exact this
  have f0 := f_zero hc j hj (ev_one hf)
  have hact : ev tr 1 r pub S384.act = 1 := one_sub (gated (hc _ s384_f0_mem) f0)
  have hact' := evalOne hact
  have hj' : j = 8 * (j / 8) + j % 8 := by omega
  have hw : j / 8 < 16 := by omega
  have hl : j % 8 < 8 := Nat.mod_lt _ (by decide)
  -- the lookup interaction of byte `j`
  have key : ∀ (b : Nat) (es : List Expr), (b = B_R8 ∨ b = B_S2 ∨ b = B_S5) →
      rcv b S384.act (S384.T.c "b" j :: es) ∈ S384.interactions →
      ev tr 1 r pub (S384.T.c "b" j) < 256 := by
    intro b es hb hmem
    have hmem' : rcv b S384.act (S384.T.c "b" j :: es) ∈ (finalAirS.tables[1]'(by decide)).interactions := by
      rw [tab1]; exact hmem
    have ho := occ_of (by decide) hr hmem' ((multNat_one rfl).2 hact')
    exact lookup_lt h hb rfl ho
  generalize hw' : j / 8 = w at hj' hw
  generalize hl' : j % 8 = l at hj' hl
  subst hj'
  have sub := fun e (he : e ∈ _) => s384_lk_sub (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩)
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))
  · exact key B_S2 [S384.T.c "s2lo" w, S384.T.c "s2hi" w] (.inr (.inl rfl)) (sub _ (by simp))
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))
  · exact key B_S5 [S384.T.c "s5lo" w, S384.T.c "s5hi" w] (.inr (.inr rfl)) (sub _ (by simp))
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))
  · exact key B_R8 [] (.inl rfl) (sub _ (by simp))

/-- **A byte sent on `SB` is below 256** (whoever sends it: `S384` is the only receiver). -/
theorem sb_lt (h : Holds finalAirS pub tr) {m : List Fp} (ho : Occ finalAirS tr pub B_SB true m)
    {x y z : Fp} (hm : m = [x, y, z]) : z.toNat < 256 := by
  obtain ⟨t, ht1, ht, r, hr, i, hi, hb, hs, hn, hmv⟩ := occ_in only_SB_recv (sent_recv h ho)
  simp only [List.mem_singleton] at ht1
  subst ht1
  rw [tab1] at hi
  obtain ⟨j, hj, rfl⟩ := s384_sb_recv hi hb hs
  have hf := (multNat_one rfl).1 hn
  have := s384_recv_lt h hr hj hf
  simp only [Interaction.msgVal, rcv, hm, List.map_cons, List.map_nil, List.cons.injEq] at hmv
  rw [← hmv.2.2.1]
  exact this

/-! ## `STMT` and `FIN` -/

theorem stmt_h_mem : Stmt.T.c "h" * (1 - Stmt.T.c "act") ∈ Stmt.table.constraints := by
  show _ ∈ Stmt.table.constraints
  simp only [Stmt.table]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem fin_hb_mem {k : Nat} (hk : k < HBN) :
    rcv B_HB Fin.act [K k, Fin.hb k] ∈ Fin.table.interactions := by
  simp only [Fin.table, Fin.interactions]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)))))

/-- **`HbBytes` from the whole AIR.** On every row of `FIN` with `act = 1`, in any trace
satisfying the deployed FINAL AIR, the statement-stream cells are bytes. -/
theorem hb_bytes (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 4)
    (hact : ev tr 4 r pub Fin.act = 1) : HbBytes tr 4 r pub := by
  intro k hk
  have hk' : k < HBN := by have e : HBN = 424 := by decide
                           omega
  -- FIN receives `HB (k, hb_k)`
  have hmem : rcv B_HB Fin.act [K k, Fin.hb k] ∈ (finalAirS.tables[4]'(by decide)).interactions := by
    rw [tab4]; exact fin_hb_mem hk'
  have ho := occ_of (by decide) hr hmem ((multNat_one rfl).2 (evalOne hact))
  -- only `STMT` sends `HB`
  obtain ⟨t, ht3, ht, r', hr', i, hi, hb, hs, hn, hmv⟩ := occ_in only_HB_send (recv_sent h ho)
  simp only [List.mem_singleton] at ht3
  subst ht3
  rw [tab3] at hi
  simp only [Stmt.table, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact absurd hb (by decide)
  have hh := (multNat_one rfl).1 hn
  -- `h = 1` gives `act = 1` on the `STMT` row
  have hcS : ∀ e ∈ Stmt.table.constraints, e.eval tr 3 r' pub = 0 := by
    have := h.constr 3 (by decide) r' hr'
    rw [tab3] at this; exact this
  have hactS : ev tr 3 r' pub (Stmt.T.c "act") = 1 := one_sub (gated (hcS _ stmt_h_mem) (ev_one hh))
  -- the byte: `b` of the `STMT` row = `hb_k`
  have heq : ev tr 3 r' pub (Stmt.T.c "b") = hbN tr 4 r pub k := by
    simp only [Interaction.msgVal, snd, rcv, List.map_cons, List.map_nil, List.cons.injEq] at hmv
    exact ev_eq_of_eval hmv.2.1
  -- `STMT` sends `SB (CLAIM, k, b)`
  have hmS : snd B_SB (Stmt.T.c "act") [K ID_CLAIM, Stmt.T.c "k", Stmt.T.c "b"] ∈
      (finalAirS.tables[3]'(by decide)).interactions := by
    rw [tab3]; exact List.mem_cons_self
  have hoS := occ_of (by decide) hr' hmS ((multNat_one rfl).2 (evalOne hactS))
  have := sb_lt h hoS rfl
  rw [← heq]
  exact this

theorem fin_constr (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 4) :
    ∀ e ∈ Fin.constraints, e.eval tr 4 r pub = 0 := by
  have := h.constr 4 (by decide) r hr
  rw [tab4] at this; exact fun e he => this e (List.mem_append_left _ he)

/-- `FIN`'s row 0 is active (`isFirst · (act − 1)`). -/
theorem fin_row0_act (h : Holds finalAirS pub tr) : ev tr 4 0 pub Fin.act = 1 := by
  have hr : 0 < tr.height 4 := Nat.two_pow_pos _
  have hm : Expr.isFirst * (Fin.act - 1) ∈ Fin.constraints := by
    unfold Fin.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h0 := ev_of_eval (fin_constr h hr _ hm)
  rcases ev_mul_eq_zero h0 with h1 | h1
  · have : ev tr 4 0 pub Expr.isFirst = 1 := by
      simp only [ev, Expr.eval, Expr.evalWith, rowEnv, ite_true]; rfl
    omega
  · have := ev_sub_eq h1
    change _ = ev tr 4 0 pub (.const 1) at this
    rw [ev_const] at this; exact this

section
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E

/-- **The FINAL template (class F1) from `Holds` of the deployed AIR**: `final_template_sound`
with `HbBytes` discharged (`hb_bytes`), on any active `FIN` row (row 0 is one: `fin_row0_act`).
Premises left: `FinInOK` (the upstream segment's), `ClassF1`, `Computed`. -/
theorem final_template_sound_holds (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 4)
    (hact : ev tr 4 r pub Fin.act = 1) {I : Intake} {out : MainOutD2}
    {tf : Bytes × Congestion × List Rcpt}
    (hf : Tail.FinInOK (fiN tr 4 r pub) I out tf) (hcl : Tail.ClassF1 I out)
    (hr' : Tail.Computed (colN "ro" tr 4 r pub) (colN "rs" tr 4 r pub) (colN "rsh" tr 4 r pub)
      (ev tr 4 r pub (.pub PV_N)) I out tf) :
    ∃ H o, decodeChunkInner (Link.win (hbN tr 4 r pub)) = .ok H ∧
      tailNew afDriver I out tf = .ok o ∧ headerOk H o = true :=
  Tail.final_template_sound (fin_constr h hr) hact (hb_bytes h hr hact) hf hcl hr'

end

end FinalM5d.HbWhole
