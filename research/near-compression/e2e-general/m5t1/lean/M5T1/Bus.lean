import M5T1.Air
import M5T1.RxRow
import ZkFormal.Udr.Np.Bus

/-!
# M5T1.Bus — bus facts from `Holds` (the `RNG` byte range; F-2)

`recv_sender`: on any trace satisfying `Holds A`, a receive with a non-zero multiplicity is
matched by a send of the same message on the same bus, by some row of some table (the exact
natural-count balance of `Holds`). Specialised to the assembled runtime AIR `fullAir tape xtape`
(the Lean tables plus the two public tapes): a tape never sends on `RNG` (a decidable condition on
the public tapes, `NoRng`), so every `RNG` receive is the `RNG` table's own send, and `RNG`'s
constraints make row `r` send `r < 256` (`rng_row`). Hence:

* `rng_recv`: every value received on `RNG` with a non-zero multiplicity is `< 256`;
* **`rx_hyps_of_holds`**: every active `RX` row of a `Holds (fullAir tape xtape)` trace satisfies
  `RxField.Hyps` — its constraints, `act = 1`, every byte column `< 256`, `r10 + 246 < 256`;
* **`rx_rel_of_holds`**: so its decoded values are in `RxRel` (`rx_rel_of_row`). The byte-range
  premise of M5-T1's row lemma is discharged.

No external (native-chip) bus is involved: every bus of `fullAir` is balanced among Lean tables and
the two explicit tapes, so `Holds (fullAir …)` is the circuit's own predicate (the prover adds no
other table; on T1 the tapes are the statement tape and the stand-in tape `XTAPE`).
-/

namespace M5T1.Bus

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1

/-! ## Generic: a receive has a sender -/

theorem sum_pos_mem {α : Type} (l : List α) (f : α → Nat) (h : 0 < (l.map f).sum) :
    ∃ x ∈ l, 0 < f x := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases ha : 0 < f a
    · exact ⟨a, List.mem_cons_self .., ha⟩
    · obtain ⟨x, hx, hfx⟩ := ih (by omega)
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem le_sum_mem {α : Type} (l : List α) (f : α → Nat) {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := ih hx; omega

section
variable {A : Air} {pub : List Fp} {tr : Trace Fp}

/-- **A receive is matched by a send.** -/
theorem recv_sender (H : Holds A pub tr) {t : Nat} (ht : t < A.tables.length) {r : Nat}
    (hr : r < tr.height t) {i : Interaction} (hi : i ∈ (A.tables[t]'ht).interactions)
    (hs : i.send = false) (hm : 0 < i.multNat tr t r pub) :
    ∃ t' r', ∃ ht' : t' < A.tables.length, r' < tr.height t' ∧
      ∃ i' ∈ (A.tables[t']'ht').interactions, i'.bus = i.bus ∧ i'.send = true ∧
        i'.msgVal tr t' r' pub = i.msgVal tr t r pub ∧ 0 < i'.multNat tr t' r' pub := by
  classical
  have hrecv : 0 < busCount A tr pub i.bus false (i.msgVal tr t r pub) := by
    rw [ZkFormal.Udr.Np.busCount_eq]
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ (List.mem_range.2 ht))
    rw [ZkFormal.Udr.Np.tableOf_lt ht, ZkFormal.Udr.Np.tableBusCount_eq]
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ (List.mem_range.2 hr))
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ hi)
    simp only [hs, and_self, if_true]
    exact hm
  rw [← H.balance, ZkFormal.Udr.Np.busCount_eq] at hrecv
  obtain ⟨t', ht', h1⟩ := sum_pos_mem _ _ hrecv
  have ht'' := List.mem_range.1 ht'
  rw [ZkFormal.Udr.Np.tableOf_lt ht'', ZkFormal.Udr.Np.tableBusCount_eq] at h1
  obtain ⟨r', hr', h2⟩ := sum_pos_mem _ _ h1
  obtain ⟨i', hi', h3⟩ := sum_pos_mem _ _ h2
  refine ⟨t', r', ht'', List.mem_range.1 hr', i', hi', ?_⟩
  by_cases hc : i'.bus = i.bus ∧ i'.send = true ∧ i'.msgVal tr t' r' pub = i.msgVal tr t r pub
  · exact ⟨hc.1, hc.2.1, hc.2.2, by simpa [hc] using h3⟩
  · simp [hc] at h3

end

/-! ## The runtime AIR's `RNG` -/

/-- The public tapes send nothing on `RNG`. -/
def NoRng (tape : List (Nat × Bool × List Nat)) : Prop := ∀ e ∈ tape, e.1 ≠ B_RNG

theorem fullAir_tables (tape xtape : List (Nat × Bool × List Nat)) :
    (fullAir tape xtape).tables =
      [shaTable, Rng.table, Scht.table, Msg.table, Dg.table, Rx.table, Rb.table, Acc.table, chipStub,
        tapeTable tape, tapeTable xtape] := rfl

/-- A table that never sends on bus `b`. -/
def NoSend (T : Table) (b : Nat) : Bool := T.interactions.all fun i => !(i.bus == b && i.send)

theorem noSend_sha : NoSend shaTable B_RNG = true := by decide +kernel
theorem noSend_scht : NoSend Scht.table B_RNG = true := by decide +kernel
theorem noSend_msg : NoSend Msg.table B_RNG = true := by decide +kernel
theorem noSend_dg : NoSend Dg.table B_RNG = true := by decide +kernel
theorem noSend_rx : NoSend Rx.table B_RNG = true := by decide +kernel
theorem noSend_rb : NoSend Rb.table B_RNG = true := by decide +kernel
theorem noSend_acc : NoSend Acc.table B_RNG = true := by decide +kernel
theorem noSend_chip : NoSend chipStub B_RNG = true := by decide +kernel

theorem noSend_spec {T : Table} {b : Nat} (h : NoSend T b = true) {i : Interaction}
    (hi : i ∈ T.interactions) (hb : i.bus = b) (hs : i.send = true) : False := by
  unfold NoSend at h
  have := List.all_eq_true.1 h i hi
  simp [hb, hs] at this

/-- Only the `RNG` table (index 1) sends on `RNG`. -/
theorem rng_senders {tape xtape : List (Nat × Bool × List Nat)} (h1 : NoRng tape) (h2 : NoRng xtape)
    {t : Nat} (ht : t < (fullAir tape xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((fullAir tape xtape).tables[t]'ht).interactions) (hb : i.bus = B_RNG)
    (hs : i.send = true) : t = 1 := by
  have hl : (fullAir tape xtape).tables.length = 11 := rfl
  have ht8 : t < 11 := hl ▸ ht
  simp only [fullAir_tables] at hi
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  · exact (noSend_spec noSend_sha hi hb hs).elim
  · rfl
  · exact (noSend_spec noSend_scht hi hb hs).elim
  · exact (noSend_spec noSend_msg hi hb hs).elim
  · exact (noSend_spec noSend_dg hi hb hs).elim
  · exact (noSend_spec noSend_rx hi hb hs).elim
  · exact (noSend_spec noSend_rb hi hb hs).elim
  · exact (noSend_spec noSend_acc hi hb hs).elim
  · exact (noSend_spec noSend_chip hi hb hs).elim
  · simp only [tapeTable, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_map] at hi
    obtain ⟨e, he, rfl⟩ := hi
    exact absurd hb (h1 e he)
  · simp only [tapeTable, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_map] at hi
    obtain ⟨e, he, rfl⟩ := hi
    exact absurd hb (h2 e he)
  · omega


/-! ## `RNG` row `r` sends `r` -/

section
variable {tape xtape : List (Nat × Bool × List Nat)} {pub : List Fp} {tr : Trace Fp}

theorem fullAir_len : (fullAir tape xtape).tables.length = 11 := rfl
theorem one_lt : 1 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

theorem ev_next (t r c : Nat) :
    ev tr t r pub (.col c true) = ev tr t ((r + 1) % tr.height t) pub (.col c false) := rfl

theorem rng_height (H : Holds (fullAir tape xtape) pub tr) : tr.height 1 ≤ 256 := by
  have h := (H.logBound 1 one_lt).2
  have h8 : ((fullAir tape xtape).tables[1]'one_lt).maxLog = 8 := rfl
  rw [h8] at h
  unfold Trace.height
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) h) (by decide)

theorem rng_constr (H : Holds (fullAir tape xtape) pub tr) {r : Nat} (hr : r < tr.height 1) :
    ∀ e ∈ Rng.constraints, ev tr 1 r pub e = 0 := fun e he =>
  ev_of_eval (H.constr 1 one_lt r hr e he)

/-- **`RNG` row `r` holds `v = r`.** -/
theorem rng_row (H : Holds (fullAir tape xtape) pub tr) :
    ∀ r, r < tr.height 1 → ev tr 1 r pub (.col 0 false) = r := by
  have hh := rng_height H
  intro r
  induction r with
  | zero =>
    intro hr
    have h := rng_constr H hr (.mul .isFirst (.col 0 false)) (by unfold Rng.constraints; exact List.mem_cons_self ..)
    rw [ev_mul] at h
    have h1 : ev tr 1 0 pub .isFirst = 1 := rfl
    rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at h
    exact h
  | succ r ih =>
    intro hr
    have ih' := ih (by omega)
    have h := rng_constr H (r := r) (by omega)
      (.mul .isTransition (.add (.add (.col 0 true) (.neg (.col 0 false))) (.neg (.const 1)))) (by unfold Rng.constraints; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have ht : ev tr 1 r pub .isTransition = 1 := by
      show (Expr.eval .isTransition tr 1 r pub).toNat = 1
      simp only [Expr.eval, Expr.evalWith, rowEnv, show ¬ (r + 1 = tr.height 1) by omega, ite_false]
      rfl
    rw [ev_mul_gate _ ht] at h
    simp only [ev_add, ev_neg, ev_const, ev_next, Nat.mod_eq_of_lt hr, ih'] at h
    have := ev_lt (tr := tr) (t := 1) (r := r + 1) (pub := pub) (.col 0 false)
    omega
end

/-! ## Every `RNG` receive is a byte; the `RX` row hypotheses -/

section
variable {tape xtape : List (Nat × Bool × List Nat)} {pub : List Fp} {tr : Trace Fp}

theorem eval_of_ev {e : Expr} {t r n : Nat} (h : ev tr t r pub e = n) (hn : n < 2013265921) :
    e.eval tr t r pub = (n : Fp) := by
  apply Fp.toNat_inj.1
  have : ((n : Fp)).toNat = n % 2013265921 := Fp.toNat_ofNat n
  rw [this, Nat.mod_eq_of_lt hn]
  exact h

/-- **Every value received on `RNG` (non-zero multiplicity) is `< 256`.** -/
theorem rng_recv (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {t r : Nat} (ht : t < (fullAir tape xtape).tables.length) (hr : r < tr.height t)
    {i : Interaction} (hi : i ∈ ((fullAir tape xtape).tables[t]'ht).interactions)
    (hb : i.bus = B_RNG) (hs : i.send = false) (hm : 0 < i.multNat tr t r pub) {e : Expr}
    (he : i.msg = [e]) : ev tr t r pub e < 256 := by
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, _⟩ := recv_sender H ht hr hi hs hm
  have h1' := rng_senders h1 h2 ht' hi' (hb'.trans hb) hs'
  subst h1'
  have hi1 : i' = sndBits B_RNG ((List.range 20).map fun t => Rng.T.c "m" t) [Rng.T.c "v"] := by
    have : ((fullAir tape xtape).tables[1]'ht').interactions =
        [sndBits B_RNG ((List.range 20).map fun t => Rng.T.c "m" t) [Rng.T.c "v"]] := rfl
    rw [this] at hi'
    exact List.mem_singleton.1 hi'
  subst hi1
  simp only [Interaction.msgVal, he, sndBits, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at hmv
  have hv := rng_row H r' hr'
  have : ev tr t r pub e = ev tr 1 r' pub (.col 0 false) := by
    unfold ev; rw [← hmv]; rfl
  have hh := rng_height H
  omega

theorem rx_lt : 5 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

theorem multNat_one {g : Expr} {t r : Nat} (hg : g.eval tr t r pub = 1) (bus : Nat) (msg : List Expr) :
    (rcv bus g msg).multNat tr t r pub = 1 := by
  simp [rcv, Interaction.multNat, Interaction.multNat.go, hg]

theorem act_eval {r : Nat} (hact : RxField.cb tr 5 r pub "act" 0 = 1) :
    (Rx.c "act").eval tr 5 r pub = 1 := by
  have := eval_of_ev (e := Rx.c "act") (t := 5) (r := r) hact (by decide)
  rw [this]; rfl

theorem rx_byte (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 5) (hact : RxField.cb tr 5 r pub "act" 0 = 1) :
    ∀ g w, (g, w) ∈ Rx.byteGroups → ∀ k < w, RxField.cb tr 5 r pub g k < 256 := by
  intro g w hg k hk
  have hi : rcv B_RNG (Rx.c "act") [Rx.c g k] ∈ ((fullAir tape xtape).tables[5]'rx_lt).interactions := by
    show _ ∈ Rx.interactions
    have hf : rcv B_RNG (Rx.c "act") [Rx.c g k] ∈
        Rx.byteGroups.flatMap fun (g, w) => (List.range w).map fun k => rcv B_RNG (Rx.c "act") [Rx.c g k] :=
      List.mem_flatMap.2 ⟨(g, w), hg, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩
    simp only [Rx.interactions, List.mem_append]
    simp only [hf, true_or]
  exact rng_recv H h1 h2 rx_lt hr hi rfl rfl (by rw [multNat_one (act_eval hact)]; decide) rfl

/-- **The `RX` row hypotheses from `Holds`**: an active row satisfies `RxField.Hyps` (the
constraints, `act = 1`, the `RNG` facts). -/
theorem rx_hyps_of_holds (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 5) (hact : RxField.cb tr 5 r pub "act" 0 = 1) :
    RxField.Hyps tr 5 r pub where
  cons := fun e he => ev_of_eval (H.constr 5 rx_lt r hr e he)
  act := hact
  bytes := rx_byte H h1 h2 hr hact
  r10 := by
    have hi : rcv B_RNG (Rx.c "act") [Rx.c "r10" 0 + K 246] ∈
        ((fullAir tape xtape).tables[5]'rx_lt).interactions := by
      show _ ∈ Rx.interactions
      simp only [Rx.interactions, List.mem_append, List.mem_cons, true_or, or_true]
    have h := rng_recv H h1 h2 rx_lt hr hi rfl rfl (by rw [multNat_one (act_eval hact)]; decide) rfl
    have hc : ev tr 5 r pub (Rx.c "r10" 0 + K 246) = (RxField.cb tr 5 r pub "r10" 0 + 246) % 2013265921 := by
      show ev tr 5 r pub (Expr.add _ (Expr.const 246)) = _
      rw [ev_add, ev_const]; rfl
    have hb := rx_byte H h1 h2 hr hact "r10" 1 (by decide) 0 (by decide)
    rw [hc] at h
    omega

/-- **`rx_rel_of_holds`**: every active `RX` row of a `Holds (fullAir tape xtape)` trace has its
decoded values in `RxRel`. -/
theorem rx_rel_of_holds (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 5) (hact : RxField.cb tr 5 r pub "act" 0 = 1) :
    RxRel (RxField.decode tr 5 r pub) :=
  RxField.rx_rel_of_row (rx_hyps_of_holds H h1 h2 hr hact)
end

#print axioms recv_sender
#print axioms rng_recv
#print axioms rx_hyps_of_holds
#print axioms rx_rel_of_holds

end M5T1.Bus
