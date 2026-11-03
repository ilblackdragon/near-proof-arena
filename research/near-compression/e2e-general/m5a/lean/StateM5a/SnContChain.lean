import StateM5a.KeyDigest

/-!
# StateM5a.SnContChain — an `SNC` chunk's place in its head's key (`KCR` sent ⇒ received)

* **`snc_shape`**: an `SNC` row's prefix flags are `a_j = [j < n]` with `n ≤ 64` **even** (the
  constraint `a_{2m+1} = a_{2m}`), `n = 64` when the chunk continues, and `ha_m = a_{2m}`;
* **`snc_v`**: the `KCR` value an active row sends, `n + rl`, is even and at most
  `64·2^20` (no wrap-around);
* **`snc_head`**: every active `SNC` row with chunk index `c` belongs to a continued `SN` head
  `r0 = rid` whose `rl` is exactly `64·(c − 1) + (n + rl)` of that row.  This uses that a sent
  `KCR` message is received (bus balance), and that the extra tables have no `KCR` interaction
  (`hxRr`); the receivers are the head (`cont`, index 1) and the continuing `SNC` row of the
  previous index (`more`, index `c + 1`).

Consequently the hp bytes a chunk sends (offsets `32c + m`, `a_{2m} = 1`) all lie below the
head's `hplen = 32 + rl/2` (`SnContByte`).
-/

namespace StateM5a.SnContChain

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.KcChain StateM5a.KeyDigest

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Who receives on `KCR` -/

/-- Does an interaction list receive on bus `b`? -/
def rcvsOn (is : List Interaction) (b : Nat) : Bool := is.any fun i => i.bus == b && !i.send

theorem not_rcvs {is : List Interaction} {b : Nat} (h : rcvsOn is b = false) {i : Interaction}
    (hi : i ∈ is) (hb : i.bus = b) (hs : i.send = false) : False := by
  have := List.any_eq_false.1 h i hi
  simp [hb, hs] at this

theorem kcr_rcv_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 → t ≠ 8 →
    rcvsOn ((m5aAir D).tables[t]).interactions B_KCR = false
  | 0, _, _, _ => by show rcvsOn shaTable.interactions B_KCR = false; decide
  | 1, _, _, _ => by show rcvsOn Key.interactions B_KCR = false; decide
  | 2, _, _, _ => by show rcvsOn Br.interactions B_KCR = false; decide
  | 3, _, h, _ => absurd rfl h
  | 4, _, _, _ => by show rcvsOn Kcmp.interactions B_KCR = false; decide
  | 5, _, _, _ => by show rcvsOn Wsb.interactions B_KCR = false; decide
  | 6, _, _, _ => by show rcvsOn Wsn.interactions B_KCR = false; decide
  | 7, _, _, _ => by show rcvsOn Wsa.interactions B_KCR = false; decide
  | 8, _, _, h => absurd rfl h
  | 9, _, _, _ => by show rcvsOn Rng.interactions B_KCR = false; decide
  | 10, _, _, _ => by show rcvsOn Wsl.interactions B_KCR = false; decide
  | 11, _, _, _ => by show rcvsOn Wsp.interactions B_KCR = false; decide
  | n + 12, h, _, _ => absurd h (by simp [m5aAir])

theorem sn_kcr_r : Sn.interactions.filter (fun i => decide (i.bus = B_KCR ∧ i.send = false)) =
    [rcv B_KCR (Sn.c "cont") [Sn.c "rid", 1, Sn.c "rl"]] := by decide
theorem snc_kcr_r : Snc.interactions.filter (fun i => decide (i.bus = B_KCR ∧ i.send = false)) =
    [rcv B_KCR (Snc.c "more") [Snc.c "rid", Snc.c "c" + 1, Snc.c "rl"]] := by decide
theorem snc_kcr_s_mem : snd B_KCR (Snc.c "act") [Snc.c "rid", Snc.c "c", Snc.c "n" + Snc.c "rl"] ∈
    Snc.interactions := memD_mem (by decide)

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **The receivers of a `KCR` message**: a continued `SN` head or a continuing `SNC` row. -/
theorem kcr_receiver (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_KCR false) :
    (∃ r, r < tr.height 3 ∧ (Sn.c "cont").eval tr 3 r pub = 1 ∧
      m = [(Sn.c "rid").eval tr 3 r pub, (1 : Expr).eval tr 3 r pub, (Sn.c "rl").eval tr 3 r pub]) ∨
    (∃ r, r < tr.height 8 ∧ (Snc.c "more").eval tr 8 r pub = 1 ∧
      m = [(Snc.c "rid").eval tr 8 r pub, (Snc.c "c" + 1).eval tr 8 r pub, (Snc.c "rl").eval tr 8 r pub]) := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    by_cases e3 : t = 3
    · subst e3
      change i ∈ Sn.interactions at hi
      obtain rfl := filter_one_mem sn_kcr_r hi hb hs
      refine .inl ⟨r, hr, multNat_one_bit rfl hp, ?_⟩
      simp [rcv, Interaction.msgVal]
    by_cases e8 : t = 8
    · subst e8
      change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kcr_r hi hb hs
      refine .inr ⟨r, hr, multNat_one_bit rfl hp, ?_⟩
      simp [rcv, Interaction.msgVal]
    exact (not_rcvs (kcr_rcv_only D t hlt e3 e8) hi hb hs).elim
  · have hmem : (fullAir D extra nb np).tables[t] ∈ extra := by
      simp only [fullAir]
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem ..
    exact (hxRr _ hmem i hi hb).elim

end

/-! ## One `SNC` row -/

theorem m_snc_pair (m : Nat) (hm : m < 32) : Snc.a (2 * m + 1) - Snc.a (2 * m) ∈ Snc.constraints := by
  unfold Snc.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search m hm
theorem m_snc_ha (m : Nat) (hm : m < 32) : Snc.c "ha" m - Snc.a (2 * m) ∈ Snc.constraints := by
  unfold Snc.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search m hm

section Row
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat} (hc : ∀ e ∈ Snc.table.constraints, e.eval tr t r pub = 0)
include hc

/-- **The shape of an `SNC` row**: `a_j = [j < n]`, `n ≤ 64` even, `n = 64` if it continues. -/
theorem snc_shape :
    ev tr t r pub (Snc.c "n") ≤ 64 ∧ ev tr t r pub (Snc.c "n") % 2 = 0 ∧
    (∀ j, j < 64 → ev tr t r pub (Snc.c "a" j) = if j < ev tr t r pub (Snc.c "n") then 1 else 0) ∧
    (ev tr t r pub (Snc.c "more") = 1 → ev tr t r pub (Snc.c "n") = 64) := by
  obtain ⟨hS, hf⟩ := prefix_flags (fun j => ev tr t r pub (Snc.c "a" j)) 64
    (fun j hj => by have := bool_le (snc_h hc (m_snc_abool j hj)); rwa [snc_a_lt j hj] at this)
    (fun j hj h1 => by
      have e := snc_h hc (m_snc_apre j (by omega))
      rw [snc_a_lt j (by omega), snc_a_lt (j + 1) hj] at e
      change ev tr t r pub (Expr.mul _ _) = 0 at e
      rw [ev_mul_gate _ h1] at e
      exact ev_one_minus e)
  have hn : ev tr t r pub (Snc.c "n") = ((List.range 64).map fun j => ev tr t r pub (Snc.c "a" j)).sum := by
    rw [eq_of_sub (snc_h hc m_snc_n), ev_sumE, List.map_map]
    have e : (List.range 64).map (ev tr t r pub ∘ Snc.a) = (List.range 64).map fun j => ev tr t r pub (Snc.c "a" j) := by
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp, snc_a_lt j (List.mem_range.1 hj)]
    rw [e]
    exact Nat.mod_eq_of_lt (by omega)
  rw [← hn] at hS hf
  refine ⟨hS, ?_, hf, ?_⟩
  · refine Classical.byContradiction fun hodd => ?_
    obtain ⟨m, hm⟩ : ∃ m, ev tr t r pub (Snc.c "n") = 2 * m + 1 := ⟨ev tr t r pub (Snc.c "n") / 2, by omega⟩
    have e := eq_of_sub (snc_h hc (m_snc_pair m (by omega)))
    rw [snc_a_lt _ (by omega), snc_a_lt _ (by omega), hf _ (by omega), hf _ (by omega)] at e
    simp [hm] at e
  · intro hmo
    have e := FieldWsb.wsb_gate hmo (snc_h hc m_snc_more)
    have h63 := ev_one_minus e
    rw [snc_a_lt 63 (by decide), hf 63 (by decide)] at h63
    split at h63 <;> omega

/-- `ha_m = 1` puts the chunk's length past `2m + 1`. -/
theorem snc_ha_n (m : Nat) (hm : m < 32) (h : ev tr t r pub (Snc.c "ha" m) = 1) :
    2 * m + 2 ≤ ev tr t r pub (Snc.c "n") := by
  obtain ⟨-, hev, hf, -⟩ := snc_shape hc
  have e := eq_of_sub (snc_h hc (m_snc_ha m hm))
  rw [h, snc_a_lt _ (by omega), hf _ (by omega)] at e
  split at e <;> omega

end Row

/-! ## The `KCR` values -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
include hH hxK hxR

/-- **An active row's `KCR` value `n + rl`** is even and at most `64·2^20`, without wrap. -/
theorem snc_v : ∀ k r, r < tr.height 8 → ev tr 8 r pub (Snc.c "act") = 1 →
    tr.height 8 - ev tr 8 r pub (Snc.c "c") = k →
    ev tr 8 r pub (Snc.c "n" + Snc.c "rl") = ev tr 8 r pub (Snc.c "n") + ev tr 8 r pub (Snc.c "rl") ∧
    ev tr 8 r pub (Snc.c "n" + Snc.c "rl") % 2 = 0 ∧ ev tr 8 r pub (Snc.c "n" + Snc.c "rl") ≤ 64 * 2 ^ 20 := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  intro k
  induction k with
  | zero =>
    intro r hr ha hk
    have hc := snc_hc hH r hr
    obtain ⟨hn, hev, -, hm64⟩ := snc_shape hc
    have htot := snc_tot hH hxK hxR _ r hr ha rfl
    rcases snc_more_bool hc with hm | hm
    · rw [ev_hadd, snc_rl0 hc hm, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
      omega
    · exfalso
      have hm' := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
        (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kcr_r_mem) hr rfl (ev_one_eval hm)
      obtain ⟨t, ht, i, hi, hb, hs, hp, he⟩ := sender_m5a B_KCR 8 (by simp [m5aAir]) (kcr_only D) hxR
        (recv_sent hH hm')
      change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kcr_s hi hb hs
      have hta := eval_one_ev (multNat_one_bit rfl hp)
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e := toNat_eq he.2.1
      obtain ⟨-, h2⟩ := snc_c_range hH hxK hr ha
      obtain ⟨-, h2'⟩ := snc_c_range hH hxK ht hta
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e
      omega
  | succ k ih =>
    intro r hr ha hk
    have hc := snc_hc hH r hr
    obtain ⟨hn, hev, -, hm64⟩ := snc_shape hc
    rcases snc_more_bool hc with hm | hm
    · rw [ev_hadd, snc_rl0 hc hm, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
      omega
    · have hm' := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
        (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kcr_r_mem) hr rfl (ev_one_eval hm)
      obtain ⟨t, ht, i, hi, hb, hs, hp, he⟩ := sender_m5a B_KCR 8 (by simp [m5aAir]) (kcr_only D) hxR
        (recv_sent hH hm')
      change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kcr_s hi hb hs
      have hta := eval_one_ev (multNat_one_bit rfl hp)
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e1 := toNat_eq he.2.1
      have e2 := toNat_eq he.2.2.1
      obtain ⟨-, h2⟩ := snc_c_range hH hxK hr ha
      obtain ⟨-, h2'⟩ := snc_c_range hH hxK ht hta
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      obtain ⟨-, hev', hle'⟩ := ih t ht hta (by omega)
      rw [← e2] at hev' hle'
      have h64 := hm64 hm
      have htot := snc_tot hH hxK hxR _ r hr ha rfl
      obtain ⟨c1, -⟩ := snc_c_range hH hxK hr ha
      have e : ev tr 8 r pub (Snc.c "n" + Snc.c "rl") = 64 + ev tr 8 r pub (Snc.c "rl") := by
        rw [ev_hadd, h64, Nat.mod_eq_of_lt (by omega)]
      rw [e] at htot ⊢
      refine ⟨by rw [h64], by omega, ?_⟩
      have : 64 * (tr.height 8 - ev tr 8 r pub (Snc.c "c") + 1) ≤ 64 * 2 ^ 20 := by
        apply Nat.mul_le_mul_left; omega
      omega

/-- **An active `SNC` row belongs to a continued head `rid`**, whose `rl` is
`64·(c − 1) + (n + rl)` of the row. -/
theorem snc_head (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR) :
    ∀ c s, s < tr.height 8 → ev tr 8 s pub (Snc.c "act") = 1 → ev tr 8 s pub (Snc.c "c") = c + 1 →
      ∃ r0, r0 < tr.height 3 ∧ ev tr 8 s pub (Snc.c "rid") = r0 ∧ ev tr 3 r0 pub (Sn.c "cont") = 1 ∧
        ev tr 3 r0 pub (Sn.c "rl") = 64 * c + ev tr 8 s pub (Snc.c "n" + Snc.c "rl") := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  intro c
  induction c with
  | zero =>
    intro s hs ha hcs
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kcr_s_mem) hs rfl (ev_one_eval ha)
    rcases kcr_receiver hxRr ((holds_perm hH B_KCR).mem_iff.1 hm) with
      ⟨t, ht, hco, he⟩ | ⟨t, ht, hmo, he⟩
    · simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e0 := toNat_eq he.1
      have e2 := toNat_eq he.2.2.1
      refine ⟨t, ht, by rw [e0, sn_rid hH t ht], eval_one_ev hco, ?_⟩
      rw [← e2]; omega
    · exfalso
      simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e1 := toNat_eq he.2.1
      have hta := snc_more_act (snc_hc hH t ht) (eval_one_ev hmo)
      obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      omega
  | succ c ih =>
    intro s hs ha hcs
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kcr_s_mem) hs rfl (ev_one_eval ha)
    rcases kcr_receiver hxRr ((holds_perm hH B_KCR).mem_iff.1 hm) with
      ⟨t, ht, hco, he⟩ | ⟨t, ht, hmo, he⟩
    · exfalso
      simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e1 := toNat_eq he.2.1
      rw [show ev tr 3 t pub (1 : Expr) = 1 from ev_one] at e1
      omega
    · simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e0 := toNat_eq he.1
      have e1 := toNat_eq he.2.1
      have e2 := toNat_eq he.2.2.1
      have hct := snc_hc hH t ht
      have hta := snc_more_act hct (eval_one_ev hmo)
      obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      obtain ⟨r0, hr0, hrid, hco, hrl⟩ := ih t ht hta (by omega)
      obtain ⟨-, -, hv⟩ := snc_v hH hxK hxR _ s hs ha rfl
      have h64 := (snc_shape hct).2.2.2 (eval_one_ev hmo)
      have et : ev tr 8 t pub (Snc.c "n" + Snc.c "rl") =
          (ev tr 8 t pub (Snc.c "n") + ev tr 8 t pub (Snc.c "rl")) % P := ev_hadd _ _
      rw [h64, ← e2, Nat.mod_eq_of_lt (by omega)] at et
      refine ⟨r0, hr0, by rw [e0, hrid], hco, ?_⟩
      rw [hrl, et]
      omega

end

end StateM5a.SnContChain
