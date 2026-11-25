import FinalM5d.InitSel

/-!
# FinalM5d.InitBus — G-4's open INIT items from `Holds` of the deployed INIT AIR (G-5)

**`initAirS`** is the AIR the prover runs for INIT: `initAir`'s six Lean tables, then lane B's chip
stub `chipStubOn B_IF384` (as `Whole.finalAirS` for FINAL: `S384` receives on `IF384`, so `Holds
initAir` alone is unsatisfiable). `precheck_holds_init`: a precheck-accepted trace extends to
`Holds initAirS` with the native chip's sends as the stub's.

G-4 left two premises of the main-slot selection open (bus level); both are proved here:

* **`init_blk_act0`**: `BLK`'s row 0 is active. `INI` (row 0 active, every later row inactive) sends
  `IX (mi)` once; only `BLK` receives `IX`, with multiplicity `kn`, which is `0` on every row but 0
  (`contRow · kn'`, and `kn + kh + ks = act` on inactive rows) and `= act` on row 0.
* **`init_ix_blk`**, **`init_lay_head`**, **`init_slot`**: the main index agrees across the three
  tables over the buses — `BLK.ix = INI.mi` (`IX`), `LAY`'s head row receives exactly `INI`'s
  `(post + 56, shard limbs, mi)` (`LAY`), and `INI`'s `SLOT` receive `(b2i, mi, sst, sln)` is the
  message of the unique selected `BLK` row `(bi − 1, si − 1, s + 4, v₀)` (`SLOT`).
* **`init_main_index`**: G-4's `blk_main_slot` / `lay_first_pair` on the deployed AIR with these
  facts: one `BLK` row `r0` is selected — the first new slot at index `ix` — and `ix = INI.mi =`
  the value of the first `LAY` pair whose key limbs are `INI`'s shard limbs; `INI`'s slot
  `(b2i, mi, sst, sln)` is row `r0`'s.

Still open for INIT (named, `Leaf.lean`): the row ↔ decoded-structure correspondence of the walks
(`decodeClaimE` / `decodeLayout`), and the SHA-384 message contract (`S384Msg`).
-/

namespace FinalM5d.InitBus

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.Whole
open FinalM5d.InitSel FinalM5d.InitT StateM5a.Bus

/-- **The deployed INIT AIR**: `initAir` + the `IF384` chip stub (table 6). -/
def initAirS : Air :=
  { initAir with tables := initAir.tables ++ [StateM5a.ChipStub.chipStubOn B_IF384] }

theorem initAirS_len : initAirS.tables.length = 7 := rfl
theorem tabS3 : initAirS.tables[3]'(by decide) = Blk.table := rfl
theorem tabS4 : initAirS.tables[4]'(by decide) = Ini.table := rfl
theorem tabS5 : initAirS.tables[5]'(by decide) = Lay.table := rfl

/-! ## Who sends / receives the three join buses -/

theorem only_IX_send : onlyIn initAirS B_IX true [4] = true := by decide +kernel
theorem only_IX_recv : onlyIn initAirS B_IX false [3] = true := by decide +kernel
theorem only_LAY_send : onlyIn initAirS B_LAY true [4] = true := by decide +kernel
theorem only_LAY_recv : onlyIn initAirS B_LAY false [5] = true := by decide +kernel
theorem only_SLOT_send : onlyIn initAirS B_SLOT true [3] = true := by decide +kernel
theorem only_SLOT_recv : onlyIn initAirS B_SLOT false [4] = true := by decide +kernel

/-- The interaction of `l` on `(b, s)` is `j` when it is the only one. -/
theorem only_one {l : List Interaction} {b : Nat} {s : Bool} {j : Interaction}
    (hf : l.filter (fun i => i.bus == b && i.send == s) = [j]) {i : Interaction} (hi : i ∈ l)
    (hb : i.bus = b) (hs : i.send = s) : i = j := by
  have : i ∈ l.filter (fun i => i.bus == b && i.send == s) :=
    List.mem_filter.2 ⟨hi, by simp [hb, hs]⟩
  rw [hf] at this
  exact List.mem_singleton.1 this

theorem blk_ix_f : Blk.interactions.filter (fun i => i.bus == B_IX && i.send == false) =
    [rcv B_IX Blk.kn [Blk.T.c "ix"]] := by rfl
theorem ini_ix_f : Ini.interactions.filter (fun i => i.bus == B_IX && i.send == true) =
    [snd B_IX Ini.act [Ini.T.c "mi"]] := by rfl
theorem lay_lay_f : Lay.interactions.filter (fun i => i.bus == B_LAY && i.send == false) =
    [rcv B_LAY Lay.k0 [Lay.s, Lay.T.c "sh" 0, Lay.T.c "sh" 1, Lay.T.c "sh" 2, Lay.T.c "ix"]] := by rfl
theorem ini_lay_f : Ini.interactions.filter (fun i => i.bus == B_LAY && i.send == true) =
    [snd B_LAY Ini.act [Ini.post + K POST_LAY, lim8 (fun j => Ini.T.c "sh" j) 0,
      lim8 (fun j => Ini.T.c "sh" j) 1, lim8 (fun j => Ini.T.c "sh" j) 2, Ini.T.c "mi"]] := by rfl
theorem blk_slot_f : Blk.interactions.filter (fun i => i.bus == B_SLOT && i.send == true) =
    [snd B_SLOT (Blk.T.c "sel") [Blk.T.c "bi" - 1, Blk.T.c "si" - 1, Blk.s + K 4, Blk.v 0]] := by rfl
theorem ini_slot_f : Ini.interactions.filter (fun i => i.bus == B_SLOT && i.send == false) =
    [rcv B_SLOT Ini.act [Ini.T.c "b2i", Ini.T.c "mi", Ini.T.c "sst", Ini.T.c "sln"]] := by rfl

theorem mem_of_f {l : List Interaction} {p : Interaction → Bool} {j : Interaction}
    (hf : l.filter p = [j]) : j ∈ l :=
  (List.mem_filter.1 (by rw [hf]; exact List.mem_singleton_self j)).1

variable {tr : Trace Fp} {pub : List Fp}

theorem height_pos (t : Nat) : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _

theorem blk_cS (h : Holds initAirS pub tr) {r : Nat} (hr : r < tr.height 3) :
    ∀ c ∈ Blk.constraints, c.eval tr 3 r pub = 0 :=
  fun c hc => h.constr 3 (by decide) r hr c (by rw [tabS3]; exact hc)
theorem ini_cS (h : Holds initAirS pub tr) {r : Nat} (hr : r < tr.height 4) :
    ∀ c ∈ Ini.constraints, c.eval tr 4 r pub = 0 :=
  fun c hc => h.constr 4 (by decide) r hr c (by rw [tabS4]; exact hc)
theorem lay_cS (h : Holds initAirS pub tr) {r : Nat} (hr : r < tr.height 5) :
    ∀ c ∈ Lay.constraints, c.eval tr 5 r pub = 0 :=
  fun c hc => h.constr 5 (by decide) r hr c (by rw [tabS5]; exact hc)

/-! ## `INI`: one active row -/

theorem ini_act0 (h : Holds initAirS pub tr) : ev tr 4 0 pub Ini.act = 1 := by
  have c := ev_of_eval (ini_cS h (height_pos 4) (.isFirst * (Ini.act - 1)) (by simp [Ini.constraints]))
  rw [ev_mul1 ev_first] at c
  have := sub0 c
  rw [ev_one_e] at this
  exact this

theorem ini_act_succ (h : Holds initAirS pub tr) {r : Nat} (hr : r + 1 < tr.height 4) :
    ev tr 4 (r + 1) pub Ini.act = 0 := by
  have c := ev_of_eval (ini_cS h (r := r) (by omega) (.isTransition * Ini.T.n "act") (by simp [Ini.constraints]))
  rw [ev_mul1 (ev_trans hr), ev_next hr] at c
  exact c

/-- `INI`'s multiplicity-`act` interactions occur on row 0 only. -/
theorem ini_row0 (h : Holds initAirS pub tr) {r : Nat} (hr : r < tr.height 4)
    (h1 : Ini.act.eval tr 4 r pub = 1) : r = 0 := by
  rcases r with _ | r
  · rfl
  · have := ini_act_succ h hr
    rw [ev_one h1] at this
    exact absurd this (by decide)

/-! ## `BLK`'s count row and `LAY`'s head row are row 0 -/

theorem blk_facts (h : Holds initAirS pub tr) :
    (∀ r, r < tr.height 3 → ev tr 3 r pub (Blk.T.c "act") ≤ 1) ∧
    (∀ r, r + 1 < tr.height 3 → ev tr 3 (r + 1) pub (Blk.T.c "act") ≤ ev tr 3 r pub (Blk.T.c "act")) ∧
    ev tr 3 (tr.height 3 - 1) pub (Blk.T.c "act") = 0 :=
  act_facts (tr := tr) (t := 3) (pub := pub) (T := Blk.T) (fun r hr c hc => blk_cS h hr c (by
    unfold Blk.constraints; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc))))

/-- On a row where `act = 0`, every kind flag of a `k₁ + k₂ + k₃ − act` row is `0` (booleans). -/
theorem flag3_zero {t r : Nat} {a b c x : Expr} (hs : ev tr t r pub (a + b + c - x) = 0)
    (hx : ev tr t r pub x = 0) (ha : ev tr t r pub a ≤ 1) (hb : ev tr t r pub b ≤ 1)
    (hc : ev tr t r pub c ≤ 1) : ev tr t r pub a = 0 := by
  have e := sub0 hs
  rw [hx, ev_plus, ev_plus] at e
  have : (ev tr t r pub a + ev tr t r pub b) % 2013265921 = ev tr t r pub a + ev tr t r pub b :=
    Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt (by omega)] at e
  omega

theorem blk_kn_succ (h : Holds initAirS pub tr) {r : Nat} (hr : r + 1 < tr.height 3) :
    ev tr 3 (r + 1) pub Blk.kn = 0 := by
  obtain ⟨ab, am, -⟩ := blk_facts h
  have hc1 := blk_cS h hr
  have b1 := ab (r + 1) hr
  have b0 := ab r (by omega)
  have mono := am r hr
  rcases (show ev tr 3 (r + 1) pub (Blk.T.c "act") = 0 ∨ ev tr 3 (r + 1) pub (Blk.T.c "act") = 1 by omega)
    with ha | ha
  · exact flag3_zero (ev_of_eval (hc1 (Blk.kn + Blk.kh + Blk.ks - Blk.act) (by simp [Blk.constraints])))
      ha (bool_le (hc1 _ (by simp [Blk.constraints] : bool (Blk.T.c "kn") ∈ Blk.constraints)))
      (bool_le (hc1 _ (by simp [Blk.constraints] : bool (Blk.T.c "kh") ∈ Blk.constraints)))
      (bool_le (hc1 _ (by simp [Blk.constraints] : bool (Blk.T.c "ks") ∈ Blk.constraints)))
  · have hr0 : ev tr 3 r pub (Blk.T.c "act") = 1 := by omega
    have c := ev_of_eval (blk_cS h (r := r) (by omega) (contRow Blk.T * Blk.T.n "kn") (by simp [Blk.constraints]))
    rw [ev_mul1 (ev_contRow hr hr0 ha), ev_next hr] at c
    exact c

theorem blk_kn0 (h : Holds initAirS pub tr) :
    ev tr 3 0 pub Blk.kn = ev tr 3 0 pub (Blk.T.c "act") := by
  have c := ev_of_eval (blk_cS h (height_pos 3) (.isFirst * (Blk.kn - Blk.act)) (by simp [Blk.constraints]))
  rw [ev_mul1 ev_first] at c
  exact sub0 c

theorem blk_row0 (h : Holds initAirS pub tr) {r : Nat} (hr : r < tr.height 3)
    (h1 : Blk.kn.eval tr 3 r pub = 1) : r = 0 := by
  rcases r with _ | r
  · rfl
  · have := blk_kn_succ h hr
    rw [ev_one h1] at this
    exact absurd this (by decide)

theorem lay_facts (h : Holds initAirS pub tr) :
    (∀ r, r < tr.height 5 → ev tr 5 r pub (Lay.T.c "act") ≤ 1) ∧
    (∀ r, r + 1 < tr.height 5 → ev tr 5 (r + 1) pub (Lay.T.c "act") ≤ ev tr 5 r pub (Lay.T.c "act")) ∧
    ev tr 5 (tr.height 5 - 1) pub (Lay.T.c "act") = 0 :=
  act_facts (tr := tr) (t := 5) (pub := pub) (T := Lay.T) (fun r hr c hc => lay_cS h hr c (by
    unfold Lay.constraints
    repeat (first | exact hc | apply List.mem_append_left)))

theorem lay_k0_succ (h : Holds initAirS pub tr) {r : Nat} (hr : r + 1 < tr.height 5) :
    ev tr 5 (r + 1) pub Lay.k0 = 0 := by
  obtain ⟨ab, am, -⟩ := lay_facts h
  have hc1 := lay_cS h hr
  have b1 := ab (r + 1) hr
  have b0 := ab r (by omega)
  have mono := am r hr
  rcases (show ev tr 5 (r + 1) pub (Lay.T.c "act") = 0 ∨ ev tr 5 (r + 1) pub (Lay.T.c "act") = 1 by omega)
    with ha | ha
  · -- `k0 + kb + ki + km + kp = act = 0`, all boolean
    have e := sub0 (ev_of_eval (hc1 (Lay.k0 + Lay.kb + Lay.ki + Lay.km + Lay.kp - Lay.act)
      (by simp [Lay.constraints])))
    have bl : ∀ s, bool (Lay.T.c s) ∈ Lay.constraints → ev tr 5 (r + 1) pub (Lay.T.c s) ≤ 1 :=
      fun s hs => bool_le (hc1 _ hs)
    have q0 := bl "k0" (by simp [Lay.constraints])
    have q1 := bl "kb" (by simp [Lay.constraints])
    have q2 := bl "ki" (by simp [Lay.constraints])
    have q3 := bl "km" (by simp [Lay.constraints])
    have q4 := bl "kp" (by simp [Lay.constraints])
    have ha' : ev tr 5 (r + 1) pub Lay.act = 0 := ha
    rw [ha', ev_plus, ev_plus, ev_plus, ev_plus] at e
    unfold Lay.k0 Lay.kb Lay.ki Lay.km Lay.kp at e
    have m1 : (ev tr 5 (r + 1) pub (Lay.T.c "k0") + ev tr 5 (r + 1) pub (Lay.T.c "kb")) % 2013265921 =
        ev tr 5 (r + 1) pub (Lay.T.c "k0") + ev tr 5 (r + 1) pub (Lay.T.c "kb") := Nat.mod_eq_of_lt (by omega)
    rw [m1] at e
    have m2 : (ev tr 5 (r + 1) pub (Lay.T.c "k0") + ev tr 5 (r + 1) pub (Lay.T.c "kb") +
        ev tr 5 (r + 1) pub (Lay.T.c "ki")) % 2013265921 = ev tr 5 (r + 1) pub (Lay.T.c "k0") +
        ev tr 5 (r + 1) pub (Lay.T.c "kb") + ev tr 5 (r + 1) pub (Lay.T.c "ki") := Nat.mod_eq_of_lt (by omega)
    rw [m2] at e
    have m3 : (ev tr 5 (r + 1) pub (Lay.T.c "k0") + ev tr 5 (r + 1) pub (Lay.T.c "kb") +
        ev tr 5 (r + 1) pub (Lay.T.c "ki") + ev tr 5 (r + 1) pub (Lay.T.c "km")) % 2013265921 =
        ev tr 5 (r + 1) pub (Lay.T.c "k0") + ev tr 5 (r + 1) pub (Lay.T.c "kb") +
        ev tr 5 (r + 1) pub (Lay.T.c "ki") + ev tr 5 (r + 1) pub (Lay.T.c "km") := Nat.mod_eq_of_lt (by omega)
    rw [m3, Nat.mod_eq_of_lt (by omega)] at e
    show ev tr 5 (r + 1) pub (Lay.T.c "k0") = 0
    omega
  · have hr0 : ev tr 5 r pub (Lay.T.c "act") = 1 := by omega
    have c := ev_of_eval (lay_cS h (r := r) (by omega) (contRow Lay.T * Lay.T.n "k0") (by simp [Lay.constraints]))
    rw [ev_mul1 (ev_contRow hr hr0 ha), ev_next hr] at c
    exact c

theorem lay_k0_0 (h : Holds initAirS pub tr) : ev tr 5 0 pub Lay.k0 = 1 := by
  have c := ev_of_eval (lay_cS h (height_pos 5) (.isFirst * (Lay.k0 - 1)) (by simp [Lay.constraints]))
  rw [ev_mul1 ev_first] at c
  have := sub0 c
  rw [ev_one_e] at this
  exact this

/-! ## The `IX` bus: `BLK`'s row 0 is active and its `ix` is `INI`'s `mi` -/

/-- **G-4's premise, proved: `BLK`'s row 0 is active.** -/
theorem init_blk_act0 (h : Holds initAirS pub tr) : ev tr 3 0 pub (Blk.T.c "act") = 1 := by
  have hmem : snd B_IX Ini.act [Ini.T.c "mi"] ∈ (initAirS.tables[4]'(by decide)).interactions := by
    rw [tabS4]; exact mem_of_f ini_ix_f
  have ho := occ_of (by decide) (height_pos 4) hmem ((multNat_one rfl).2 (evalOne (ini_act0 h)))
  obtain ⟨t, ht3, ht, r, hr, i, hi, hb, hs, hn, -⟩ := occ_in only_IX_recv (sent_recv h ho)
  simp only [List.mem_singleton] at ht3
  subst ht3
  rw [tabS3] at hi
  obtain rfl := only_one blk_ix_f hi hb hs
  have hk := (multNat_one rfl).1 hn
  obtain rfl := blk_row0 h hr hk
  rw [← blk_kn0 h]
  exact ev_one hk

/-- **`IX`: `BLK.ix = INI.mi`** (row 0 of each). -/
theorem init_ix_blk (h : Holds initAirS pub tr) :
    ev tr 3 0 pub (Blk.T.c "ix") = ev tr 4 0 pub (Ini.T.c "mi") := by
  have hmem : rcv B_IX Blk.kn [Blk.T.c "ix"] ∈ (initAirS.tables[3]'(by decide)).interactions := by
    rw [tabS3]; exact mem_of_f blk_ix_f
  have hk : ev tr 3 0 pub Blk.kn = 1 := by rw [blk_kn0 h]; exact init_blk_act0 h
  have ho := occ_of (by decide) (height_pos 3) hmem ((multNat_one rfl).2 (evalOne hk))
  obtain ⟨t, ht4, ht, r, hr, i, hi, hb, hs, hn, hmv⟩ := occ_in only_IX_send (recv_sent h ho)
  simp only [List.mem_singleton] at ht4
  subst ht4
  rw [tabS4] at hi
  obtain rfl := only_one ini_ix_f hi hb hs
  obtain rfl := ini_row0 h hr ((multNat_one rfl).1 hn)
  simp only [Interaction.msgVal, snd, rcv, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmv
  exact (ev_eq_of_eval hmv).symm

/-! ## The `LAY` bus: `LAY`'s head row receives `INI`'s start, shard limbs and `mi` -/

theorem init_lay_head (h : Holds initAirS pub tr) :
    ev tr 5 0 pub Lay.s = ev tr 4 0 pub (Ini.post + K POST_LAY) ∧
    (∀ q, q < 3 → ev tr 5 0 pub (Lay.T.c "sh" q) = ev tr 4 0 pub (lim8 (fun j => Ini.T.c "sh" j) q)) ∧
    ev tr 5 0 pub (Lay.T.c "ix") = ev tr 4 0 pub (Ini.T.c "mi") := by
  have hmem : rcv B_LAY Lay.k0 [Lay.s, Lay.T.c "sh" 0, Lay.T.c "sh" 1, Lay.T.c "sh" 2, Lay.T.c "ix"] ∈
      (initAirS.tables[5]'(by decide)).interactions := by
    rw [tabS5]; exact mem_of_f lay_lay_f
  have ho := occ_of (by decide) (height_pos 5) hmem ((multNat_one rfl).2 (evalOne (lay_k0_0 h)))
  obtain ⟨t, ht4, ht, r, hr, i, hi, hb, hs, hn, hmv⟩ := occ_in only_LAY_send (recv_sent h ho)
  simp only [List.mem_singleton] at ht4
  subst ht4
  rw [tabS4] at hi
  obtain rfl := only_one ini_lay_f hi hb hs
  obtain rfl := ini_row0 h hr ((multNat_one rfl).1 hn)
  simp only [Interaction.msgVal, snd, rcv, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmv
  obtain ⟨e0, e1, e2, e3, e4⟩ := hmv
  refine ⟨(ev_eq_of_eval e0).symm, fun q hq => ?_, (ev_eq_of_eval e4).symm⟩
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl
  · exact (ev_eq_of_eval e1).symm
  · exact (ev_eq_of_eval e2).symm
  · exact (ev_eq_of_eval e3).symm

/-! ## The `SLOT` bus: `INI`'s slot is the selected `BLK` row's -/

theorem init_slot (h : Holds initAirS pub tr) {r0 : Nat} (hr0 : r0 < tr.height 3)
    (hsel : ∀ r, r < tr.height 3 → r ≠ r0 → ev tr 3 r pub Blk.sel = 0) :
    ev tr 4 0 pub (Ini.T.c "b2i") = ev tr 3 r0 pub (Blk.T.c "bi" - 1) ∧
    ev tr 4 0 pub (Ini.T.c "mi") = ev tr 3 r0 pub (Blk.T.c "si" - 1) ∧
    ev tr 4 0 pub (Ini.T.c "sst") = ev tr 3 r0 pub (Blk.s + K 4) ∧
    ev tr 4 0 pub (Ini.T.c "sln") = ev tr 3 r0 pub (Blk.v 0) := by
  have hmem : rcv B_SLOT Ini.act [Ini.T.c "b2i", Ini.T.c "mi", Ini.T.c "sst", Ini.T.c "sln"] ∈
      (initAirS.tables[4]'(by decide)).interactions := by
    rw [tabS4]; exact mem_of_f ini_slot_f
  have ho := occ_of (by decide) (height_pos 4) hmem ((multNat_one rfl).2 (evalOne (ini_act0 h)))
  obtain ⟨t, ht3, ht, r, hr, i, hi, hb, hs, hn, hmv⟩ := occ_in only_SLOT_send (recv_sent h ho)
  simp only [List.mem_singleton] at ht3
  subst ht3
  rw [tabS3] at hi
  obtain rfl := only_one blk_slot_f hi hb hs
  have h1 := ev_one ((multNat_one rfl).1 hn)
  have hr' : r = r0 := by
    refine Classical.byContradiction fun hne => ?_
    have := hsel r hr hne
    unfold Blk.sel at this
    omega
  subst hr'
  simp only [Interaction.msgVal, snd, rcv, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmv
  obtain ⟨e0, e1, e2, e3⟩ := hmv
  exact ⟨(ev_eq_of_eval e0).symm, (ev_eq_of_eval e1).symm, (ev_eq_of_eval e2).symm,
    (ev_eq_of_eval e3).symm⟩

/-! ## Together: the main index on the deployed AIR -/

/-- **The main-slot selection on the deployed INIT AIR** (G-4's two theorems with their bus
premises discharged): one `BLK` row `r0` is selected, it is a new slot at index `ix` and the first
such, `ix = INI.mi`; `INI`'s slot `(b2i, mi, sst, sln)` is row `r0`'s `(bi − 1, si − 1, s + 4, v₀)`;
one `LAY` row `r1` is the first pair whose key limbs are `INI`'s shard limbs, and its value byte is
`INI.mi` (bytes 1..7 zero); `LAY` starts at `post + 56`. -/
theorem init_main_index (h : Holds initAirS pub tr) :
    ∃ r0, r0 < tr.height 3 ∧ ev tr 3 r0 pub Blk.sel = 1 ∧ BlkNew tr 3 r0 pub ∧
      (∀ r, r < r0 → ¬ BlkNew tr 3 r pub) ∧
      ev tr 3 r0 pub (Blk.T.c "ix") = ev tr 4 0 pub (Ini.T.c "mi") ∧
      ev tr 4 0 pub (Ini.T.c "b2i") = ev tr 3 r0 pub (Blk.T.c "bi" - 1) ∧
      ev tr 4 0 pub (Ini.T.c "mi") = ev tr 3 r0 pub (Blk.T.c "si" - 1) ∧
      ev tr 4 0 pub (Ini.T.c "sst") = ev tr 3 r0 pub (Blk.s + K 4) ∧
      ev tr 4 0 pub (Ini.T.c "sln") = ev tr 3 r0 pub (Blk.v 0) ∧
    ∃ r1, r1 < tr.height 5 ∧ ev tr 5 r1 pub Lay.hit = 1 ∧ LayMatch tr 5 r1 pub ∧
      (∀ r, r < r1 → ¬ LayMatch tr 5 r pub) ∧
      ev tr 5 r1 pub (Lay.y 8) = ev tr 4 0 pub (Ini.T.c "mi") ∧
      (∀ j, j < 7 → ev tr 5 r1 pub (Lay.y (9 + j)) = 0) ∧
      (∀ q, q < 3 → ev tr 5 r1 pub (Lay.T.c "sh" q) = ev tr 4 0 pub (lim8 (fun j => Ini.T.c "sh" j) q)) ∧
      ev tr 5 0 pub Lay.s = ev tr 4 0 pub (Ini.post + K POST_LAY) := by
  obtain ⟨r0, hr0, hs0, hn0, hf0, hu0, hix0⟩ := blk_main_slot (fun r hr => blk_cS h hr) (init_blk_act0 h)
  obtain ⟨s0, s1, s2, s3⟩ := init_slot h hr0 hu0
  obtain ⟨r1, hr1, hh1, hm1, hf1, -, hy8, hy, hix1, hsh1, -⟩ := lay_first_pair (fun r hr => lay_cS h hr)
  obtain ⟨l0, l1, l2⟩ := init_lay_head h
  refine ⟨r0, hr0, hs0, hn0, hf0, hix0.trans (init_ix_blk h), s0, s1, s2, s3, r1, hr1, hh1, hm1, hf1,
    hy8.trans (hix1.trans l2), hy, fun q hq => (hsh1 q hq).trans (l1 q hq), l0⟩

/-! ## Non-vacuity: precheck-accepted traces give `Holds initAirS` with the chip's sends -/

theorem init_ifOK : initAir.tables.all (fun T => StateM5a.ChipStub.ifOK T.interactions) = true := by
  decide +kernel

/-- **The deployment** (lane B's `holds_of_holdsX` for the INIT AIR, as `precheck_holds_final`). -/
theorem precheck_holds_init {tr : Trace Fp}
    (hX : StateM5a.ChipStub.HoldsX initAir pub tr B_IF384)
    (chip : List (List Fp)) (hchip : chip.Perm (busList initAir tr pub B_IF384 false))
    (hlen : chip.length ≤ 2 ^ 22) :
    ∃ tr' : Trace Fp,
      (∀ t < initAir.tables.length, tr'.log t = tr.log t ∧ tr'.cell t = tr.cell t) ∧
      Holds initAirS pub tr' ∧ busList initAirS tr' pub B_IF384 true = chip := by
  have hok : ∀ T ∈ initAir.tables, StateM5a.ChipStub.ifOK T.interactions = true :=
    fun T hT => List.all_eq_true.1 init_ifOK T hT
  have hns : ∀ T ∈ initAir.tables, ∀ i ∈ T.interactions, ¬ (i.bus = B_IF384 ∧ i.send = true) :=
    fun T hT i hi ⟨hb, hs⟩ => by
      have := (StateM5a.ChipStub.of_ifOK (hok T hT) hi hb).1; rw [hs] at this; exact absurd this (by decide)
  have h8 : ∀ m ∈ chip, m.length = 8 := fun m hm =>
    StateM5a.ChipStub.busList_len _ tr pub B_IF384 false
      (fun T hT i hi hb _ => (StateM5a.ChipStub.of_ifOK (hok T hT) hi hb).2) m (hchip.mem_iff.1 hm)
  obtain ⟨tr', h1, h2, h3, -⟩ :=
    StateM5a.ChipStub.holds_of_holdsX (by decide) hX hns chip hchip h8 hlen
  exact ⟨tr', h1, h2, h3⟩

end FinalM5d.InitBus
