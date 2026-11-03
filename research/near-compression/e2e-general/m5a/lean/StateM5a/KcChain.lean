import StateM5a.Tape

/-!
# StateM5a.KcChain — the `SNC` key-continuation chain (`KC` / `KCR`) from `Holds`, and `SncDeeper`

An `SN` head whose key continues (`cont = 1`) sends `KC(rid, 1, …)` and receives
`KCR(rid, 1, rl)`; an active `SNC` row receives `KC(rid, c, …)`, sends `KCR(rid, c, n + rl)`, and
when it continues (`more = 1`) sends `KC(rid, c + 1, …)` and receives `KCR(rid, c + 1, rl)`.

* **`snc_c_range`** (from `KC` balance): every active `SNC` row has `1 ≤ c ≤ height`.  A row with
  chunk index `v ≠ 1` received its `KC` from a continuing `SNC` row with index `v − 1` (only `SN`
  sends index `1`), and a continuing row is active (`more ⇒ a₆₃ ⇒ a₀ = act`); so an index
  outside `[1, height]` would force every index in `[1, v]` (or `[1, P − 1]`) to occur — more
  distinct indices than rows.
* **`snc_tot`** (from `KCR` balance and the range): the value an active row sends,
  `n + rl`, is at most `64·(height − c + 1)` (a chunk holds `≤ 64` nibbles; a continuing row's
  `rl` is the `KCR` answer of a row with index `c + 1`).
* **`sncDeeper`**: `SncDeeper` from `Holds`: a descending continued head has
  `klen = Σ a + rl` with `1 ≤ Σ a ≤ 64` and `rl ≤ 64·(2^20 + 1)`, and `d < 2^21`, so
  `d < d + klen` without wrap-around.
* **`air_final'`**: `Tape.air_final` with `SncDeeper` discharged.

No uniqueness of the chain is needed for the bound (only the indices).
-/

namespace StateM5a.KcChain

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.DecodeShape StateM5a.DepthBound StateM5a.Tape StateM5a.Store StateM5a.BusWalk NearSpec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Who sends on `KC` / `KCR` -/

theorem kc_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 → t ≠ 8 →
    sendsOn ((m5aAir D).tables[t]).interactions B_KC = false
  | 0, _, _, _ => by show sendsOn shaTable.interactions B_KC = false; decide
  | 1, _, _, _ => by show sendsOn Key.interactions B_KC = false; decide
  | 2, _, _, _ => by show sendsOn Br.interactions B_KC = false; decide
  | 3, _, h, _ => absurd rfl h
  | 4, _, _, _ => by show sendsOn Kcmp.interactions B_KC = false; decide
  | 5, _, _, _ => by show sendsOn Wsb.interactions B_KC = false; decide
  | 6, _, _, _ => by show sendsOn Wsn.interactions B_KC = false; decide
  | 7, _, _, _ => by show sendsOn Wsa.interactions B_KC = false; decide
  | 8, _, _, h => absurd rfl h
  | 9, _, _, _ => by show sendsOn Rng.interactions B_KC = false; decide
  | 10, _, _, _ => by show sendsOn Wsl.interactions B_KC = false; decide
  | 11, _, _, _ => by show sendsOn Wsp.interactions B_KC = false; decide
  | n + 12, h, _, _ => absurd h (by simp [m5aAir])

theorem kcr_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 8 →
    sendsOn ((m5aAir D).tables[t]).interactions B_KCR = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_KCR = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_KCR = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_KCR = false; decide
  | 3, _, _ => by show sendsOn Sn.interactions B_KCR = false; decide
  | 4, _, _ => by show sendsOn Kcmp.interactions B_KCR = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_KCR = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_KCR = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_KCR = false; decide
  | 8, _, h => absurd rfl h
  | 9, _, _ => by show sendsOn Rng.interactions B_KCR = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_KCR = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_KCR = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem filter_one_mem {is : List Interaction} {b : Nat} {s : Bool} {x : Interaction}
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = [x]) {i : Interaction} (hi : i ∈ is)
    (hb : i.bus = b) (hs : i.send = s) : i = x := by
  have : i ∈ is.filter (fun i => decide (i.bus = b ∧ i.send = s)) :=
    List.mem_filter.2 ⟨hi, by simp [hb, hs]⟩
  rw [h] at this
  exact List.mem_singleton.1 this

theorem sn_kc_s : Sn.interactions.filter (fun i => decide (i.bus = B_KC ∧ i.send = true)) =
    [snd B_KC (Sn.c "cont") [Sn.c "rid", 1, Sn.c "d" + 62 + Sn.c "odd", Sn.c "kid", 1 - Sn.c "gA",
      Sn.c "kid2", Sn.c "g2", Sn.c "gsha", Sn.gfin]] := by decide
theorem snc_kc_s : Snc.interactions.filter (fun i => decide (i.bus = B_KC ∧ i.send = true)) =
    [snd B_KC (Snc.c "more") [Snc.c "rid", Snc.c "c" + 1, Snc.c "p" + 64, Snc.c "kA", Snc.c "fA",
      Snc.c "kB", Snc.c "gB", Snc.c "gO", Snc.c "gN"]] := by decide
theorem snc_kcr_s : Snc.interactions.filter (fun i => decide (i.bus = B_KCR ∧ i.send = true)) =
    [snd B_KCR (Snc.c "act") [Snc.c "rid", Snc.c "c", Snc.c "n" + Snc.c "rl"]] := by decide

theorem snc_kc_r_mem : rcv B_KC (Snc.c "act") [Snc.c "rid", Snc.c "c", Snc.c "p", Snc.c "kA", Snc.c "fA",
    Snc.c "kB", Snc.c "gB", Snc.c "gO", Snc.c "gN"] ∈ Snc.interactions := memD_mem (by decide)
theorem snc_kcr_r_mem : rcv B_KCR (Snc.c "more") [Snc.c "rid", Snc.c "c" + 1, Snc.c "rl"] ∈ Snc.interactions :=
  memD_mem (by decide)
theorem sn_kcr_r_mem : rcv B_KCR (Sn.c "cont") [Sn.c "rid", 1, Sn.c "rl"] ∈ Sn.interactions :=
  memD_mem (by decide)

section
variable {tr : Trace Fp} {pub : List Fp}

/-- Two possible senders. -/
theorem sender_m5a2 {D : Nat} {extra : List Table} {nb np : Nat} (b t0 t1 : Nat)
    (ht0 : t0 < (m5aAir D).tables.length) (ht1 : t1 < (m5aAir D).tables.length)
    (hS : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ t0 → t ≠ t1 →
      sendsOn ((m5aAir D).tables[t]).interactions b = false)
    (hx : ∀ T ∈ extra, sendsOn T.interactions b = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub b true) :
    (∃ r, r < tr.height t0 ∧ ∃ i ∈ ((m5aAir D).tables[t0]).interactions, i.bus = b ∧ i.send = true ∧
      0 < i.multNat tr t0 r pub ∧ m = i.msgVal tr t0 r pub) ∨
    (∃ r, r < tr.height t1 ∧ ∃ i ∈ ((m5aAir D).tables[t1]).interactions, i.bus = b ∧ i.send = true ∧
      0 < i.multNat tr t1 r pub ∧ m = i.msgVal tr t1 r pub) := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    by_cases e0 : t = t0
    · subst e0; exact .inl ⟨r, hr, i, hi, hb, hs, hp, rfl⟩
    by_cases e1 : t = t1
    · subst e1; exact .inr ⟨r, hr, i, hi, hb, hs, hp, rfl⟩
    exact (not_sends (hS t hlt e0 e1) hi hb hs).elim
  · have hmem : (fullAir D extra nb np).tables[t] ∈ extra := by
      simp only [fullAir]
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem ..
    exact (not_sends (hx _ hmem) hi hb hs).elim

theorem multNat_one_bit {i : Interaction} {g : Expr} (hm : i.mult = [g]) {t r : Nat}
    (h : 0 < i.multNat tr t r pub) : g.eval tr t r pub = 1 := by
  obtain ⟨b, hb, e⟩ := multNat_pos i h
  rw [hm, List.mem_singleton] at hb
  rw [← hb]; exact e

theorem toNat_eq {a b : Expr} {t r t' r' : Nat} (h : a.eval tr t r pub = b.eval tr t' r' pub) :
    ev tr t r pub a = ev tr t' r' pub b := congrArg Fp.toNat h

/-! ## `SNC` row facts -/

theorem snc_a_lt (j : Nat) (hj : j < 64) : Snc.a j = Snc.c "a" j := by simp [Snc.a, hj]

theorem m_snc_bool_more : bool (Snc.c "more") ∈ Snc.constraints := by unfold Snc.constraints; simp
theorem m_snc_a0 : Snc.a 0 - Snc.c "act" ∈ Snc.constraints := by unfold Snc.constraints; simp
theorem m_snc_more : Snc.c "more" * (1 - Snc.a 63) ∈ Snc.constraints := by unfold Snc.constraints; simp
theorem m_snc_rl : (1 - Snc.c "more") * Snc.c "rl" ∈ Snc.constraints := by unfold Snc.constraints; simp
theorem m_snc_n : Snc.c "n" - sumE ((List.range 64).map Snc.a) ∈ Snc.constraints := by
  unfold Snc.constraints; simp
theorem m_snc_abool (j : Nat) (hj : j < 64) : bool (Snc.a j) ∈ Snc.constraints := by
  unfold Snc.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search j hj
theorem m_snc_apre (j : Nat) (hj : j < 64) : Snc.a (j + 1) * (1 - Snc.a j) ∈ Snc.constraints := by
  unfold Snc.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search j hj

section Row
variable {t r : Nat} (hc : ∀ e ∈ Snc.table.constraints, e.eval tr t r pub = 0)
include hc

theorem snc_h {e : Expr} (he : e ∈ Snc.constraints) : ev tr t r pub e = 0 := hold rfl hc he

theorem snc_a_down : ∀ j, j < 64 → ev tr t r pub (Snc.a j) = 1 → ev tr t r pub (Snc.a 0) = 1
  | 0, _, h => h
  | j + 1, hj, h => by
    have e := snc_h hc (m_snc_apre j (by omega))
    rw [ev_hmul, h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at e
    exact snc_a_down j (by omega) (ev_one_minus e)

/-- A continuing row is active. -/
theorem snc_more_act (hm : ev tr t r pub (Snc.c "more") = 1) : ev tr t r pub (Snc.c "act") = 1 := by
  have e := FieldWsb.wsb_gate hm (snc_h hc m_snc_more)
  have h63 := snc_a_down hc 63 (by decide) (ev_one_minus e)
  rw [← eq_of_sub (snc_h hc m_snc_a0)]
  exact h63

theorem snc_more_bool : ev tr t r pub (Snc.c "more") = 0 ∨ ev tr t r pub (Snc.c "more") = 1 :=
  ev_bool (snc_h hc m_snc_bool_more)

theorem snc_rl0 (hm : ev tr t r pub (Snc.c "more") = 0) : ev tr t r pub (Snc.c "rl") = 0 :=
  FieldWsb.wsb_gate (ev_one_sub0 hm) (snc_h hc m_snc_rl)

theorem snc_n_le : ev tr t r pub (Snc.c "n") ≤ 64 := by
  rw [eq_of_sub (snc_h hc m_snc_n), ev_sumE, List.map_map]
  have : ((List.range 64).map (ev tr t r pub ∘ Snc.a)).sum ≤ 64 := by
    have := sum_le_length ((List.range 64).map (ev tr t r pub ∘ Snc.a))
      (by intro x hx; simp only [List.mem_map, List.mem_range, Function.comp] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bool_le (snc_h hc (m_snc_abool j hj)))
    simpa using this
  exact Nat.le_trans (Nat.mod_le _ _) this

end Row

/-! ## Chunk indices (`KC`) -/

variable {D : Nat} {extra : List Table} {nb np : Nat}

theorem snc_hc (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 8 → ∀ e ∈ Snc.table.constraints, e.eval tr 8 r pub = 0 :=
  fun r hr => hH.constr 8 (by rw [fullAir_len]; omega) r hr

theorem snc_log (hH : Holds (fullAir D extra nb np) pub tr) : tr.log 8 ≤ 20 :=
  (hH.logBound 8 (by rw [fullAir_len]; omega)).2

/-- Chunk index `v` occurs on an active `SNC` row. -/
def Present (tr : Trace Fp) (pub : List Fp) (v : Nat) : Prop :=
  ∃ r, r < tr.height 8 ∧ ev tr 8 r pub (Snc.c "act") = 1 ∧ ev tr 8 r pub (Snc.c "c") = v

theorem present_step (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) {v : Nat} (hv : Present tr pub v)
    (h1 : v ≠ 1) : Present tr pub ((v + P - 1) % P) := by
  obtain ⟨r, hr, ha, rfl⟩ := hv
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kc_r_mem) hr rfl (ev_one_eval ha)
  rcases sender_m5a2 B_KC 3 8 (by simp [m5aAir]) (by simp [m5aAir]) (kc_only D) hxK
      (recv_sent hH hm) with ⟨t, ht, i, hi, hb, hs, hp, he⟩ | ⟨t, ht, i, hi, hb, hs, hp, he⟩
  · change i ∈ Sn.interactions at hi
    obtain rfl := filter_one_mem sn_kc_s hi hb hs
    simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := toNat_eq he.2.1
    rw [show ev tr 3 t pub (1 : Expr) = 1 from ev_one] at this
    exact absurd this h1
  · change i ∈ Snc.interactions at hi
    obtain rfl := filter_one_mem snc_kc_s hi hb hs
    have hmo := multNat_one_bit rfl hp
    have hta := snc_more_act (snc_hc hH t ht) (eval_one_ev hmo)
    simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e := toNat_eq he.2.1
    rw [ev_hadd, ev_one] at e
    have := ev_lt (tr := tr) (t := 8) (r := t) (pub := pub) (Snc.c "c")
    have := ev_lt (tr := tr) (t := 8) (r := r) (pub := pub) (Snc.c "c")
    exact ⟨t, ht, hta, by omega⟩

theorem present_down (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) {v₀ : Nat} (hv₀ : v₀ < P) :
    ∀ d u, u + d = v₀ → 1 ≤ u → Present tr pub v₀ → Present tr pub u
  | 0, u, h, _, hp => by rw [← h] at hp; simpa using hp
  | d + 1, u, h, hu, hp => by
    have := present_down hH hxK hv₀ d (u + 1) (by omega) (by omega) hp
    have := present_step hH hxK this (by omega)
    rwa [show (u + 1 + P - 1) % P = u by omega] at this

theorem present_count {v₀ : Nat} (h : ∀ u, 1 ≤ u → u ≤ v₀ → Present tr pub u) : v₀ ≤ tr.height 8 := by
  have hsub : List.range' 1 v₀ ⊆ (List.range (tr.height 8)).map fun r => ev tr 8 r pub (Snc.c "c") := by
    intro u hu
    rw [List.mem_range'_1] at hu
    obtain ⟨r, hr, -, e⟩ := h u hu.1 (by omega)
    exact List.mem_map.2 ⟨r, List.mem_range.2 hr, e⟩
  have := List.Nodup.length_le_of_subset List.nodup_range' hsub
  simpa using this

/-- **Chunk indices are in `[1, height]`.** -/
theorem snc_c_range (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) {r : Nat} (hr : r < tr.height 8)
    (ha : ev tr 8 r pub (Snc.c "act") = 1) :
    1 ≤ ev tr 8 r pub (Snc.c "c") ∧ ev tr 8 r pub (Snc.c "c") ≤ tr.height 8 := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have hlt := ev_lt (tr := tr) (t := 8) (r := r) (pub := pub) (Snc.c "c")
  have hp : Present tr pub (ev tr 8 r pub (Snc.c "c")) := ⟨r, hr, ha, rfl⟩
  have up : ∀ v, v < P → 1 ≤ v → Present tr pub v → v ≤ tr.height 8 := fun v hv h1 hpv =>
    present_count (fun u hu hu' => present_down hH hxK hv (v - u) u (by omega) hu hpv)
  by_cases h0 : ev tr 8 r pub (Snc.c "c") = 0
  · have := present_step hH hxK hp (by omega)
    rw [h0] at this
    have := up _ (by decide) (by decide) this
    omega
  · exact ⟨by omega, up _ hlt (by omega) hp⟩

/-! ## Chain totals (`KCR`) -/

/-- **A row's `KCR` answer is at most `64·(height − c + 1)`.** -/
theorem snc_tot (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false) :
    ∀ k r, r < tr.height 8 → ev tr 8 r pub (Snc.c "act") = 1 →
      tr.height 8 - ev tr 8 r pub (Snc.c "c") = k →
      ev tr 8 r pub (Snc.c "n" + Snc.c "rl") ≤ 64 * (k + 1) := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  intro k
  induction k with
  | zero =>
    intro r hr ha hk
    have hc := snc_hc hH r hr
    rcases snc_more_bool hc with hm | hm
    · rw [ev_hadd, snc_rl0 hc hm, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
      have := snc_n_le hc; omega
    · -- a continuing row needs an index `c + 1 ≤ height`
      exfalso
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
    rcases snc_more_bool hc with hm | hm
    · rw [ev_hadd, snc_rl0 hc hm, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
      have := snc_n_le hc; omega
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
      have := ih t ht hta (by omega)
      rw [← e2] at this
      have hn := snc_n_le hc
      rw [ev_hadd]
      exact Nat.le_trans (Nat.mod_le _ _) (by omega)

/-! ## `SncDeeper` -/

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | y :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem m_sn_klen : Sn.c "klen" - sumE ((List.range KMAX).map Sn.a) - Sn.c "rl" ∈ Sn.constraints := by
  unfold Sn.constraints; simp

/-- **`SncDeeper` from `Holds`.** -/
theorem sncDeeper (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false) : SncDeeper tr pub := by
  intro r hr hg hcont
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hd := sn_depth hH hxN r hr hg
  -- the head's `rl` is an active `SNC` row's `KCR` answer
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_kcr_r_mem) hr rfl (ev_one_eval hcont)
  obtain ⟨t, ht, i, hi, hb, hs, hp, he⟩ := sender_m5a B_KCR 8 (by simp [m5aAir]) (kcr_only D) hxR
    (recv_sent hH hm)
  change i ∈ Snc.interactions at hi
  obtain rfl := filter_one_mem snc_kcr_s hi hb hs
  have hta := eval_one_ev (multNat_one_bit rfl hp)
  simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
  have e2 := toNat_eq he.2.2.1
  obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
  have htot := snc_tot hH hxK hxR _ t ht hta rfl
  rw [← e2] at htot
  -- `klen = Σ a + rl`, `1 ≤ Σ a ≤ 64`
  have ek := sub_val (eq_of_sub (hold rfl hc m_sn_klen))
  rw [ev_sumE, List.map_map] at ek
  have hS : ((List.range KMAX).map (ev tr 3 r pub ∘ Sn.a)).sum ≤ 64 := by
    have := sum_le_length ((List.range KMAX).map (ev tr 3 r pub ∘ Sn.a))
      (by intro x hx; simp only [List.mem_map, List.mem_range, Function.comp] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          rw [sn_a_lt j hj]; exact sn_a_bool hc j hj)
    simpa [KMAX] using this
  have hS1 : 1 ≤ ((List.range KMAX).map (ev tr 3 r pub ∘ Sn.a)).sum := by
    have ha0 := (FieldWalk2.sn_gdn_walk hc (eval_one_ev hg)).2.2
    have : ev tr 3 r pub (Sn.a 0) ∈ (List.range KMAX).map (ev tr 3 r pub ∘ Sn.a) :=
      List.mem_map.2 ⟨0, List.mem_range.2 (by decide), rfl⟩
    have := le_sum_of_mem this
    rw [sn_a_lt 0 (by decide), ha0] at this
    exact this
  rw [Nat.mod_eq_of_lt (by omega : ((List.range KMAX).map (ev tr 3 r pub ∘ Sn.a)).sum < P)] at ek
  rw [ev_hadd, ek, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

end

/-! ## The assembly without `SncDeeper` -/

section
variable {tr : Trace Fp} {pub : List Fp}

open NearSpecV3.D2 in
/-- **`air_final` with the continued-key premise discharged.**  Premises left: `Sha256CR`, the
per-row `LocalOK` (`hloc`) and `FinalChanges`. -/
theorem air_final' (hCR : Walk.Sha256CR) (σ : Store) (Dc : Dec Ref Pay Res) (hDc : StdDec Dc) (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    (hH : Holds (fullAir D (tapeTable (m5aTape writes prev post n) :: rest) nb np) pub tr) (hD : D ≤ 30)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hn : n < P) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (SemS σ (keyOf tr)) r)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  have hx : ∀ b, b = B_NIB ∨ b = B_KC ∨ b = B_KCR →
      ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions b = false := by
    intro b hb T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · apply List.any_eq_false.2
      intro i hi
      rcases hb with rfl | rfl | rfl <;>
        rcases tape_bus writes prev post n i hi with h | h <;> simp [h, B_WRITE, B_TCH, B_NIB, B_KC, B_KCR]
    · rcases hb with rfl | rfl | rfl
      · exact (hrN T hT).1
      · exact (hrN T hT).2.1
      · exact (hrN T hT).2.2
  exact air_final hCR σ Dc hDc D writes prev post n rest nb np hH hD hr (fun T hT => (hrN T hT).1) hn
    hprev hpost (sncDeeper hH (hx _ (.inl rfl)) (hx _ (.inr (.inl rfl))) (hx _ (.inr (.inr rfl)))) hloc cs
    hlen hcs T hT0 hF

end

end StateM5a.KcChain
