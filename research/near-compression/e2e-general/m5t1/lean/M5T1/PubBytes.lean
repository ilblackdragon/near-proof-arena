import M5T1.Bus
import M5T1.EnterC
import M5T1.ResumeF
import M5T1.Se

/-!
# M5T1.PubBytes — every public value of a lane F leaf is a byte, in-circuit (F-6)

Lane D's finding F-M9-1: lane F's prover gave each AIR as many public values as its constraints
read, so a record field no constraint read (the F-2 enter output's Wasm part) was not in the
proof, and the leaf predicates (`EnterC.EntHoldsC`, `SeC.SeHoldsC`, `ResumeC.RsHoldsC`) *assumed*
that the public values are bytes (`∀ i < N, pv pub i < 256`) — a statement-side check the tree
would have to repeat before hashing `h(B)`. F-6 puts one `RNG` receive per public value on the
boundary table's first row (`Ids.pubBytes`): every public value of the full boundary pair (and,
for the resume leaf, `RX`'s public totals) is read by the leaf's own AIR, so the prover's per-AIR
public-value count is the whole layout, and its byte range is a consequence of `Holds`.

* `RngAir`, `rng_row_gen`, `rng_recv_gen`: `Bus.rng_recv` for any AIR whose table 1 is `RNG` and
  in which no other table sends on `RNG` (the enter AIR `[ENT, RNG]`, the STATE engine half's
  `[SE, RNG, XTAPE]`, the resume AIR).
* `pub_byte_gen`: a public value received on `RNG` on row 0 of some table is a byte.
* **`ent_bytes`**, **`se_bytes`**, **`rb_bytes`**: on every satisfying trace of the exported
  enter AIR (`Ent.entAirB`), the STATE engine half (`Se.fullSe xtape`, `NoRng xtape`), and the
  resume AIR (`fullAir tape xtape`, `NoRng` tapes), every public value is a byte.
* **`ent_core`**: `Holds entAirB → Holds entAir` (same constraints), so every F-3 lemma applies.
* The leaf predicates from the circuit, without a byte premise: **`entHoldsC_of`**,
  **`seHoldsC_of`**, **`rsHolds_of_circuit`**.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.PubBytes

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus M5T1.SegRt

-- `pubBytes n` is a list of `n` lookups: never unfold it while unifying (only `mem_pubBytes` opens it)
attribute [local irreducible] pubBytes

/-! ## 1. `RNG` in a general AIR -/

/-- An AIR whose table 1 is `RNG` and in which no other table sends on `RNG`. -/
structure RngAir (A : Air) : Prop where
  len : 1 < A.tables.length
  rng : A.tables[1]'len = Rng.table
  only : ∀ t (ht : t < A.tables.length) (i : Interaction), i ∈ (A.tables[t]'ht).interactions →
    i.bus = B_RNG → i.send = true → t = 1

section
variable {A : Air} {pub : List Fp} {tr : Trace Fp}

theorem rng_height_gen (H : Holds A pub tr) (hA : RngAir A) : tr.height 1 ≤ 256 := by
  have h := (H.logBound 1 hA.len).2
  have h8 : (A.tables[1]'hA.len).maxLog = 8 := by rw [hA.rng]; rfl
  rw [h8] at h
  unfold Trace.height
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) h) (by decide)

theorem rng_constr_gen (H : Holds A pub tr) (hA : RngAir A) {r : Nat} (hr : r < tr.height 1) :
    ∀ e ∈ Rng.constraints, ev tr 1 r pub e = 0 := fun e he =>
  ev_of_eval (H.constr 1 hA.len r hr e (by rw [hA.rng]; exact he))

/-- **`RNG` row `r` holds `v = r`** (any `RngAir`). -/
theorem rng_row_gen (H : Holds A pub tr) (hA : RngAir A) :
    ∀ r, r < tr.height 1 → ev tr 1 r pub (.col 0 false) = r := by
  have hh := rng_height_gen H hA
  intro r
  induction r with
  | zero =>
    intro hr
    have h := rng_constr_gen H hA hr (.mul .isFirst (.col 0 false))
      (by unfold Rng.constraints; exact List.mem_cons_self ..)
    rw [ev_mul] at h
    have h1 : ev tr 1 0 pub .isFirst = 1 := rfl
    rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at h
    exact h
  | succ r ih =>
    intro hr
    have ih' := ih (by omega)
    have h := rng_constr_gen H hA (r := r) (by omega)
      (.mul .isTransition (.add (.add (.col 0 true) (.neg (.col 0 false))) (.neg (.const 1))))
      (by unfold Rng.constraints; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have ht : ev tr 1 r pub .isTransition = 1 := by
      show (Expr.eval .isTransition tr 1 r pub).toNat = 1
      simp only [Expr.eval, Expr.evalWith, rowEnv, show ¬ (r + 1 = tr.height 1) by omega, ite_false]
      rfl
    rw [ev_mul_gate _ ht] at h
    simp only [ev_add, ev_neg, ev_const, ev_next, Nat.mod_eq_of_lt hr, ih'] at h
    have := ev_lt (tr := tr) (t := 1) (r := r + 1) (pub := pub) (.col 0 false)
    omega

/-- **Every value received on `RNG` (non-zero multiplicity) is `< 256`** (any `RngAir`). -/
theorem rng_recv_gen (H : Holds A pub tr) (hA : RngAir A)
    {t r : Nat} (ht : t < A.tables.length) (hr : r < tr.height t)
    {i : Interaction} (hi : i ∈ (A.tables[t]'ht).interactions)
    (hb : i.bus = B_RNG) (hs : i.send = false) (hm : 0 < i.multNat tr t r pub) {e : Expr}
    (he : i.msg = [e]) : ev tr t r pub e < 256 := by
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, _⟩ := recv_sender H ht hr hi hs hm
  have h1' := hA.only t' ht' i' hi' (hb'.trans hb) hs'
  subst h1'
  have hi1 : i' = sndBits B_RNG ((List.range 20).map fun t => Rng.T.c "m" t) [Rng.T.c "v"] := by
    have e1 : A.tables[1]'ht' = Rng.table := hA.rng
    rw [e1] at hi'
    exact List.mem_singleton.1 hi'
  subst hi1
  simp only [Interaction.msgVal, he, sndBits, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at hmv
  have hv := rng_row_gen H hA r' hr'
  have : ev tr t r pub e = ev tr 1 r' pub (.col 0 false) := by
    unfold ev; rw [← hmv]; rfl
  have hh := rng_height_gen H hA
  omega

/-- **A public value received on `RNG` on row 0 of some table is a byte.** -/
theorem pub_byte_gen (H : Holds A pub tr) (hA : RngAir A) {t : Nat} (ht : t < A.tables.length)
    {i : Nat} (hmem : rcv B_RNG .isFirst [.pub i] ∈ (A.tables[t]'ht).interactions) :
    pv pub i < 256 := by
  have hpos : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  have h1 : (Expr.isFirst).eval tr t 0 pub = 1 := rfl
  have h := rng_recv_gen H hA ht hpos hmem rfl rfl (by rw [multNat_one h1]; decide) rfl
  exact h

theorem mem_pubBytes {n i : Nat} (hi : i < n) : rcv B_RNG .isFirst [.pub i] ∈ pubBytes n := by
  unfold pubBytes
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

end

/-! ## 2. The three leaf AIRs -/

/-- The enter AIR `[ENT, RNG]`. -/
theorem ent_rngAir : RngAir Ent.entAirB where
  len := by decide
  rng := rfl
  only := by
    intro t ht i hi hb hs
    have hl : Ent.entAirB.tables.length = 2 := rfl
    obtain _ | _ | t := t
    · exact (noSend_spec (by decide +kernel : NoSend Ent.tableB B_RNG = true) hi hb hs).elim
    · rfl
    · omega

/-- The STATE engine half `[SE, RNG, SH, chip stub, XTAPE]` (F-7; a tape that sends nothing on `RNG`). -/
theorem se_rngAir {xtape : List (Nat × Bool × List Nat)} (h2 : NoRng xtape) :
    RngAir (Se.fullSe xtape) where
  len := by simp [Se.fullSe, Se.seAir]
  rng := rfl
  only := by
    intro t ht i hi hb hs
    have hl : (Se.fullSe xtape).tables.length = 5 := rfl
    obtain _ | _ | _ | _ | _ | t := t
    · exact (noSend_spec (by decide +kernel : NoSend Se.table B_RNG = true) hi hb hs).elim
    · rfl
    · exact (noSend_spec (by decide +kernel : NoSend Sh.table B_RNG = true) hi hb hs).elim
    · exact (noSend_spec (by decide +kernel : NoSend chipStub B_RNG = true) hi hb hs).elim
    · simp only [Se.fullSe, Se.seAir, tapeTable, List.cons_append, List.nil_append,
        List.getElem_cons_succ, List.getElem_cons_zero, List.mem_map] at hi
      obtain ⟨e, he, rfl⟩ := hi
      exact absurd hb (h2 e he)
    · omega

/-- The resume AIR (`fullAir tape xtape`, tapes that send nothing on `RNG`). -/
theorem rs_rngAir {tape xtape : List (Nat × Bool × List Nat)} (h1 : NoRng tape) (h2 : NoRng xtape) :
    RngAir (fullAir tape xtape) where
  len := one_lt
  rng := rfl
  only := fun _ ht _ hi hb hs => rng_senders h1 h2 ht hi hb hs

/-- **Every public value of the enter leaf is a byte.** -/
theorem ent_bytes {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAirB pub tr) :
    ∀ i < 1284, pv pub i < 256 := by
  have hN : Ent.NUM_PUB = 1284 := by decide
  intro i hi
  have hm : rcv B_RNG .isFirst [.pub i] ∈ pubBytes Ent.NUM_PUB := mem_pubBytes (hN ▸ hi)
  exact pub_byte_gen H ent_rngAir (t := 0) (by decide) hm

/-- **Every public value of the STATE engine half is a byte.** -/
theorem se_bytes {xtape : List (Nat × Bool × List Nat)} {pub : List Fp} {tr : Trace Fp}
    (H : Holds (Se.fullSe xtape) pub tr) (h2 : NoRng xtape) : ∀ i < 900, pv pub i < 256 := by
  have hN : Se.NUM_PUB = 900 := by decide
  intro i hi
  have hm : rcv B_RNG .isFirst [.pub i] ∈ pubBytes Se.NUM_PUB := mem_pubBytes (hN ▸ hi)
  refine pub_byte_gen H (se_rngAir h2) (t := 0) (by simp [Se.fullSe, Se.seAir]) ?_
  show _ ∈ Se.interactions5 ++ Se.interactions7
  simp only [Se.interactions5, List.mem_append]
  exact .inl (.inr hm)

/-- **Every public value of the resume leaf is a byte.** -/
theorem rb_bytes {tape xtape : List (Nat × Bool × List Nat)} {pub : List Fp} {tr : Trace Fp}
    (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape) :
    ∀ i < 1531, pv pub i < 256 := by
  have hN : Rx.NUM_PUB = 1531 := by decide
  intro i hi
  have hm : rcv B_RNG .isFirst [.pub i] ∈ pubBytes Rx.NUM_PUB := mem_pubBytes (hN ▸ hi)
  refine pub_byte_gen H (rs_rngAir h1 h2) (t := 6) (by rw [fullAir_len]; decide) ?_
  show _ ∈ Rb.interactions
  simp only [Rb.interactions, List.mem_append]
  exact .inr hm

/-- **`Holds entAirB → Holds entAir`**: the exported enter AIR has `entAir`'s constraints (the
`RNG` lookups only add facts), so every F-3 lemma about `entAir` applies to it. -/
theorem ent_core {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAirB pub tr) :
    Holds Ent.entAir pub tr where
  logBound := fun t ht => by
    have ht0 : t = 0 := by have : Ent.entAir.tables.length = 1 := rfl; omega
    subst ht0
    exact H.logBound 0 (by decide)
  constr := fun t ht r hr e he => by
    have ht0 : t = 0 := by have : Ent.entAir.tables.length = 1 := rfl; omega
    subst ht0
    exact H.constr 0 (by decide) r hr e he
  bits := fun t ht r hr i hi => by
    have ht0 : t = 0 := by have : Ent.entAir.tables.length = 1 := rfl; omega
    subst ht0
    exact absurd hi (by simp [Ent.entAir, Ent.table])
  balance := fun b m => by
    simp [busCount, busCount.go, Ent.entAir, Ent.table, tableBusCount]

/-! ## 3. The leaf predicates from the circuit (no byte premise) -/

open M5T1.EnterC in
/-- **The enter leaf predicate from the exported AIR.** -/
theorem entHoldsC_of {vmc : NearSpecV3.Wasm.CallCut.CallArgs → ArenaCore.Bytes}
    {pre : NearSpecV3.Wasm.CallCut.CallArgs → Nat} {posOK : ArenaCore.Bytes → Prop}
    {d d' : ArenaCore.Bytes} {w : EntW} (H : Holds Ent.entAirB w.1 w.2.1)
    (hd : d = NearSpecV3.E2E.Bnd.bdigest (bytesOf w.1 0 450))
    (hd' : d' = NearSpecV3.E2E.Bnd.bdigest (bytesOf w.1 450 834))
    (hc : EntChecks vmc pre posOK w.1 w.2.2) : EntHoldsC vmc pre posOK d d' w :=
  ⟨ent_core H, ent_bytes H, hd, hd', hc⟩

open M5T1.ResumeC M5T1.AccDef in
/-- **The resume leaf predicate from the circuit and the chip contract** (F-4's `rsHolds_of`
without its byte premise). -/
theorem rsHolds_of_circuit {tape xtape : ResumeC.Tp} {d d' : ArenaCore.Bytes} {w : RsW}
    (H : Holds (fullAir tape xtape) w.1 w.2.1)
    (hd : d = NearSpecV3.E2E.Bnd.bdigest (bytesOf w.1 RbSem.BIN 834))
    (hd' : d' = NearSpecV3.E2E.Bnd.bdigest (bytesOf w.1 RbSem.BOUT 450))
    (hr1 : NoRng tape) (hr2 : NoRng xtape)
    (hi1 : MsgRow.NoSendOn B_IF384 tape) (hi2 : MsgRow.NoSendOn B_IF384 xtape)
    (hd1 : AccSem.NoRecvOn B_ACCD tape) (hd2 : AccSem.NoRecvOn B_ACCD xtape)
    (hC : ChipOK w.2.1) : RsHoldsC tape xtape d d' w :=
  ResumeF.rsHolds_of H (rb_bytes H hr1 hr2) hd hd' hr1 hr2 hi1 hi2 hd1 hd2 hC

#print axioms rng_recv_gen
#print axioms ent_bytes
#print axioms se_bytes
#print axioms rb_bytes
#print axioms ent_core
#print axioms entHoldsC_of
#print axioms rsHolds_of_circuit

end M5T1.PubBytes
