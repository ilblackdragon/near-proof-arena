import WasmBase.Main.SegShaSpec

/-!
# WasmBase.Main.SegSha — the bus-103 bridge: the native SHA-512 chip as a named hypothesis (E2E M4b)

`wasmBaseSegAir` receives on bus 103 (`Seg.busIf`) from the native SHA-512 compression chip v4,
which is not a Lean table.  Four tables receive on it: MEMB (19), MPATH (20), CUTI (30), CUTO (31);
no table sends on it (`seg_if_shape`), and every bus-103 count is a bit (`seg_if_bits`: MEMB's and
MPATH's `act`, `act·(1 − ro)` by `BitS`; CUT's `kD + kP` from the one-hot `kD + kP + kX = 1`).

**`Holds (wasmBaseSegAir …)` is unsatisfiable** (`seg_holds_false`): it balances bus 103 over the Lean
tables alone, and CUTI's first row receives on it with count 1.  The segment relation is
`HoldsX` (`Main/SegHoldsX.lean`: `Holds` without the bus-103 balance) plus the chip hypothesis.

## The chip hypothesis (`ChipIf compress A pub tr chip`)

* `contract : Sha512IfContract compress chip` — lane B's contract (`StateM5a.Sha512If`): the chip's
  sends are the 16 messages `(cid, m, limbs w_2m, limbs w_2m+1)` of each of its compressions, over
  `h ‖ block ‖ compress h block`, distinct `cid`s, 64-bit inputs;
* `cidLt : ∀ x ∈ chip, x.cid < P` — the chip's ids are `128·k` with `k` below its height `≤ 2^24`;
* `balance` — bus 103's LogUp balance **with** the chip's sends (each with count 1):
  `(#chip sends of m + #Lean sends of m) ≡ #Lean receives of m (mod p)` for every message `m`
  (`ifF` is a chip message as a field message).

`compress` is a parameter; the instance is `SegShaSpec.compressW` (FIPS 180-4 SHA-512 compression
of the block's big-endian bytes, `compressW_ok : CompressOK compressW`).  Nothing else about the
chip is assumed.

## What follows

* `if_recv_mem`: every bus-103 receive with count 1 is a chip message;
* `consumer_sound` (**row-layout independent**): a consumer whose 16 receives under one field `cid`
  are `cid, m, W(2m), W(2m+1)` (`m < 16`) for triples `W k` has `W k = limbs(words_k)` with
  `words = h ‖ block ‖ compress h block`, `h`, `block` 64-bit;
* `consumer_node_sha384` (row-layout independent): with `W = IV384 ‖ l ‖ r ‖ padW ‖ out`, the
  triples `l`, `r` decode to 6-word digests `dl`, `dr`, and `out` is the limbs of the 6 words whose
  bytes are `sha384 (bytes dl ++ bytes dr)` (lane B's `nodeH` with `compressW`, `nodeH_sha384`);
  `comp_node_sha384` is the same at lane B's record level (`compRecv`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-! ## Bus 103 in the segment AIR -/

theorem seg_if_shape (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters,
      i.bus = 103 → i.send = false ∧ (t = 19 ∨ t = 20 ∨ t = 30 ∨ t = 31) := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length),
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != 103 ||
        (!i.send && (t == 19 || t == 20 || t == 30 || t == 31))) = true := by
    decide
  intro t ht i hi hb
  have := List.all_eq_true.mp (h0 t (by simpa [e] using ht)) i (by simpa [e] using hi)
  simp only [hb, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, beq_iff_eq] at this
  exact ⟨this.1, by omega⟩

theorem memb_if_bits :
    Memb.table.inters.all (fun i => i.bus != 103 || BitS (bcOf Memb.table) (beOf Memb.table) i.count) = true := by
  decide

theorem mpath_if_bits :
    Mpath.table.inters.all (fun i => i.bus != 103 || BitS (bcOf Mpath.table) (beOf Mpath.table) i.count) = true := by
  decide

theorem cuti_if_count :
    Cut.In.table.inters.all (fun i => i.bus != 103 || decide (i.count = Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP")) = true := by
  decide

theorem cuto_if_count :
    Cut.Out.table.inters.all (fun i => i.bus != 103 || decide (i.count = Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP")) = true := by
  decide

theorem seg_t30 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[30]'(by simp [seg_air_len]) = Cut.In.table := rfl
theorem seg_t31' (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[31]'(by simp [seg_air_len]) = Cut.Out.table := rfl

theorem bit_of_bool {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := bool_cases h

/-- The CUT one-hot: `kD + kP` is a bit on every row of a table carrying `streamConstraints`. -/
theorem cut_kDkP_bit (cs : List String) (rw : Row)
    (hc : ∀ e ∈ [Chips.bool (Cut.c cs "kD"), Chips.bool (Cut.c cs "kP"), Chips.bool (Cut.c cs "kX"),
      Cut.c cs "kD" + Cut.c cs "kP" + Cut.c cs "kX" - 1], e.eval rw = 0) :
    (Cut.c cs "kD" + Cut.c cs "kP").eval rw = 0 ∨ (Cut.c cs "kD" + Cut.c cs "kP").eval rw = 1 := by
  have h1 := hc (Chips.bool (Cut.c cs "kD")) (by simp)
  have h2 := hc (Chips.bool (Cut.c cs "kP")) (by simp)
  have h3 := hc (Chips.bool (Cut.c cs "kX")) (by simp)
  have h4 := hc (Cut.c cs "kD" + Cut.c cs "kP" + Cut.c cs "kX" - 1) (by simp)
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat'] at h1 h2 h3 h4 ⊢
  rcases bit_of_bool h1 with a | a <;> rcases bit_of_bool h2 with b | b <;>
    rcases bit_of_bool h3 with c | c <;> rw [a, b] <;> rw [a, b, c] at h4 <;> first
    | (left; decide) | (right; decide) | (exfalso; revert h4; decide)

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

theorem cut_kDkP_row {t : Nat} (ht : t = 30 ∨ t = 31) {r : Nat} (hr : r < tr.height t) :
    (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP").eval (tr.row pub t r) = 0 ∨
      (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP").eval (tr.row pub t r) = 1 := by
  have eIO : Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP" = Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP" := by
    decide
  rcases ht with rfl | rfl
  · refine cut_kDkP_bit Cut.In.cols _ fun e he => ?_
    have := H.constr 30 (by simp [seg_air_len]) r hr e
    rw [seg_t30] at this
    exact this (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl | rfl <;> simp [Cut.In.table, Cut.streamConstraints])
  · rw [eIO]
    refine cut_kDkP_bit Cut.Out.cols _ fun e he => ?_
    have := H.constr 31 (by simp [seg_air_len]) r hr e
    rw [seg_t31'] at this
    exact this (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl | rfl <;>
                   simp [Cut.Out.table, Cut.Out.constraints, Cut.streamConstraints])

/-- **Bus 103 in a segment trace**: every occurrence is a receive with a bit count. -/
theorem seg_if_bits :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = extBus → o.2.1 = false ∧ o.2.2.2 ≤ 1 := by
  intro o ho hb
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb
  obtain ⟨hs, htt⟩ := seg_if_shape nloc ngl t ht i hi hb
  refine ⟨hs, ?_⟩
  simp only
  have bit_le : ∀ x : F, x = 0 ∨ x = 1 → x.toNat ≤ 1 := by
    intro x hx; rcases hx with rfl | rfl <;> decide
  rcases htt with rfl | rfl | rfl | rfl
  · have hc := List.all_eq_true.mp memb_if_bits i (by rw [← seg_t19 nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or] at hc
    exact bit_le _ (bitS_sound H.toC ht hr i.count (by rw [seg_t19]; exact hc))
  · have hc := List.all_eq_true.mp mpath_if_bits i (by rw [← seg_t20 nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or] at hc
    exact bit_le _ (bitS_sound H.toC ht hr i.count (by rw [seg_t20]; exact hc))
  · have hc := List.all_eq_true.mp cuti_if_count i (by rw [← seg_t30 nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hc
    rw [hc]; exact bit_le _ (cut_kDkP_row H (Or.inl rfl) hr)
  · have hc := List.all_eq_true.mp cuto_if_count i (by rw [← seg_t31' nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hc
    have eIO : Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP" = Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP" := by
      decide
    rw [hc, eIO]; exact bit_le _ (cut_kDkP_row H (Or.inr rfl) hr)

/-- No Lean table sends on bus 103. -/
theorem seg_if_send_zero (m : List F) : busNat (wasmBaseSegAir nloc ngl) tr pub extBus true m = 0 :=
  busNat_zero fun o ho hb hs _ => absurd hs (by rw [(seg_if_bits H o ho hb).1]; decide)

end

/-- **`Holds (wasmBaseSegAir …)` is unsatisfiable.**  It demands bus 103 balance over the Lean
tables alone; CUTI's first row (`kX = 0` there, so `kD + kP = 1`) receives on bus 103 with count 1,
and no Lean table sends on it.  So every theorem stated from `Holds (wasmBaseSegAir …)` is vacuous;
the segment relation is `HoldsX` plus the chip hypothesis `ChipIf`. -/
theorem seg_holds_false {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseSegAir nloc ngl) pub tr) : False := by
  have HX : HoldsX (wasmBaseSegAir nloc ngl) pub tr := H
  have ht : 30 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have h0 : 0 < tr.height 30 := by have := H.heightPos 30 ht; omega
  -- `kX = 0` on the first row, so `kD + kP = 1`
  have hkx := H.constr 30 ht 0 h0 (.first * Cut.c Cut.In.cols "kX")
    (by rw [seg_t30]; simp [Cut.In.table, Cut.streamConstraints])
  have hsum := H.constr 30 ht 0 h0 (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP" + Cut.c Cut.In.cols "kX" - 1)
    (by rw [seg_t30]; simp [Cut.In.table, Cut.streamConstraints])
  have hcnt : (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP").eval (tr.row pub 30 0) = 1 := by
    simp only [Expr.eval_mul', Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat'] at hkx hsum ⊢
    have e1 : Expr.first.eval (tr.row pub 30 0) = 1 := by simp [Expr.eval, Trace.row]
    rw [e1] at hkx
    grind
  -- CUTI's first interface receive on row 0
  let i : Inter := ⟨busIf, false, Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP",
    [Cut.c Cut.In.cols "cid", Expr.c 0 + 12 * Cut.c Cut.In.cols "j"] ++
      (wordsAt (Cut.c Cut.In.cols) "h" 8).getD (2 * 0) zeroW ++ (wordsAt (Cut.c Cut.In.cols) "h" 8).getD (2 * 0 + 1) zeroW⟩
  have hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[30]'ht).inters := by
    rw [seg_t30]
    simp only [Cut.In.table, List.mem_append]
    left; right
    simp only [Cut.ifInters, List.mem_append]
    left
    exact List.mem_map.2 ⟨0, by simp, rfl⟩
  have hocc := occ_of_inter ht h0 hi (by show (Expr.eval _ (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP")).toNat = 1; rw [hcnt]; decide)
  have hbits := seg_if_bits HX
  have hge : 1 ≤ busNat (wasmBaseSegAir nloc ngl) tr pub extBus false (i.msg.map (·.eval (tr.row pub 30 0))) :=
    count_le_busNat hocc rfl rfl rfl
  have hlt := busNat_ltX HX extBus false (i.msg.map (·.eval (tr.row pub 30 0))) (fun o ho hb _ => (hbits o ho hb).2)
  have hbal := H.balance extBus (i.msg.map (·.eval (tr.row pub 30 0)))
  rw [seg_if_send_zero HX, Nat.zero_mod, Nat.mod_eq_of_lt hlt] at hbal
  omega

/-! ## The chip hypothesis -/

/-- A chip message as the field message on bus 103. -/
def ifF (x : IfMsg) : List F :=
  ((x.cid : Nat) : F) :: ((x.pair : Nat) : F) :: (x.a ++ x.b).map (fun n => ((n : Nat) : F))

/-- **The chip hypothesis** (named): `chip` is the native chip's bus-103 traffic. -/
structure ChipIf (compress : List Nat → List Nat → List Nat) (A : Air) (pub : List F) (tr : Trace)
    (chip : List IfMsg) : Prop where
  contract : Sha512IfContract compress chip
  cidLt : ∀ x ∈ chip, x.cid < P
  balance : ∀ m, ((chip.map ifF).count m + busNat A tr pub extBus true m) % P =
    busNat A tr pub extBus false m % P

/-- **A bus-103 receive with count 1 is a chip message.** -/
theorem if_recv_mem {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hC : ChipIf compress (wasmBaseSegAir nloc ngl) pub tr chip)
    {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = extBus) (hc : o.2.2.2 = 1) :
    o.2.2.1 ∈ chip.map ifF := by
  have hbits := seg_if_bits H
  have hs := (hbits o ho hb).1
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltX H extBus false o.2.2.1 (fun o ho hb _ => (hbits o ho hb).2)
  have hbal := hC.balance o.2.2.1
  rw [seg_if_send_zero H, Nat.add_zero, Nat.mod_eq_of_lt hlt] at hbal
  refine List.count_pos_iff.mp ?_
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, Nat.zero_mod] at hbal
  omega

/-! ## A consumer of one compression (row-layout independent) -/

/-- Limbs of a word as field elements. -/
def wF (w : Nat) : List F := (StateM5a.wlimbs w).map fun n => ((n : Nat) : F)

theorem wlimbs_lt {w : Nat} (hw : w < 2 ^ 64) : ∀ n ∈ StateM5a.wlimbs w, n < P := by
  have := P_val
  simp only [StateM5a.wlimbs, List.mem_cons, List.not_mem_nil, or_false]
  rintro n (rfl | rfl | rfl) <;> omega

theorem map_cast_inj {a b : List Nat} (ha : ∀ n ∈ a, n < P) (hb : ∀ n ∈ b, n < P)
    (h : a.map (fun n => ((n : Nat) : F)) = b.map (fun n => ((n : Nat) : F))) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x a ih => cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [natEq h.1 (ha x List.mem_cons_self) (hb y List.mem_cons_self),
        ih (fun n hn => ha n (List.mem_cons_of_mem _ hn)) (fun n hn => hb n (List.mem_cons_of_mem _ hn)) h.2]

theorem wF_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : wF x = wF y) : x = y :=
  wlimbs_inj (map_cast_inj (wlimbs_lt hx) (wlimbs_lt hy) h)

theorem w64_of_all (l : List Nat) (h : l.all (fun w => decide (w < 2 ^ 64)) = true) : W64 l :=
  fun w hw => by simpa using List.all_eq_true.mp h w hw

theorem wF_length (w : Nat) : (wF w).length = 3 := rfl

/-- **The consumer lemma.**  A consumer whose 16 bus-103 messages under one `cid` are
`cid, m, W(2m), W(2m+1)` (`m < 16`), all chip messages, sees one chip compression: `W k` is the limbs
of word `k` of `h ‖ block ‖ compress h block` for 64-bit `h` (8 words), `block` (16 words). -/
theorem consumer_sound {compress : List Nat → List Nat → List Nat} (hok : CompressOK compress)
    {chip : List IfMsg} (hcon : Sha512IfContract compress chip) (hlt : ∀ x ∈ chip, x.cid < P)
    {cid : F} {W : Nat → List F} (hW3 : ∀ k, k < 32 → (W k).length = 3)
    (hin : ∀ m, m < 16 → (cid :: ((m : Nat) : F) :: (W (2 * m) ++ W (2 * m + 1))) ∈ chip.map ifF) :
    ∃ h blk : List Nat, h.length = 8 ∧ blk.length = 16 ∧ W64 h ∧ W64 blk ∧
      ∀ k, k < 32 → W k = wF ((h ++ blk ++ compress h blk).getD k 0) := by
  obtain ⟨comps, rfl, hnd, hshape⟩ := hcon
  have hP := P_val
  have wlen : ∀ c ∈ comps, (c.words compress).length = 32 := by
    intro c hc
    simp [Comp.words, (hshape c hc).1, (hshape c hc).2.1, (hok c.h c.blk).1]
  have w64 : ∀ c ∈ comps, ∀ k, (c.words compress).getD k 0 < 2 ^ 64 := by
    intro c hc k
    rw [List.getD_eq_getElem?_getD]
    rcases e : (c.words compress)[k]? with _ | w
    · simp
    · have hm := List.mem_of_getElem? e
      simp only [Comp.words, List.mem_append] at hm
      simp only [Option.getD_some]
      rcases hm with (hm | hm) | hm
      · exact (hshape c hc).2.2.1 w hm
      · exact (hshape c hc).2.2.2 w hm
      · exact (hok c.h c.blk).2 w hm
  have hfrom : ∀ m, m < 16 → ∃ c ∈ comps, ((c.cid : Nat) : F) = cid ∧
      W (2 * m) = wF ((c.words compress).getD (2 * m) 0) ∧
      W (2 * m + 1) = wF ((c.words compress).getD (2 * m + 1) 0) := by
    intro m hm
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 (hin m hm)
    obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.1 hx
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hxc
    have hm'' := List.mem_range.1 hm'
    simp only [ifF, List.cons.injEq, List.map_append] at hxe
    obtain ⟨e1, e2, e3⟩ := hxe
    have em : m' = m := natEq e2 (by omega) (by omega)
    subst em
    have ⟨ea, eb⟩ := List.append_inj e3 (by rw [hW3 (2 * m') (by omega)]; rfl)
    exact ⟨c, hc, e1, ea.symm, eb.symm⟩
  obtain ⟨c, hcm, hcid, -⟩ := hfrom 0 (by decide)
  have cidlt : ∀ c' ∈ comps, c'.cid < P := by
    intro c' hc'
    exact hlt _ (List.mem_flatMap.2 ⟨c', hc', List.mem_map.2 ⟨0, List.mem_range.2 (by decide), rfl⟩⟩)
  have hall : ∀ k, k < 32 → W k = wF ((c.words compress).getD k 0) := by
    intro k hk
    obtain ⟨c', hc', hcid', e0, e1⟩ := hfrom (k / 2) (by omega)
    have := nodup_key hnd hc' hcm (natEq (hcid'.trans hcid.symm) (cidlt c' hc') (cidlt c hcm))
    subst this
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have : k = 2 * (k / 2) := by omega
      rw [this]; exact e0
    · have : k = 2 * (k / 2) + 1 := by omega
      rw [this]; exact e1
  obtain ⟨h8, h16, wh, wb⟩ := hshape c hcm
  exact ⟨c.h, c.blk, h8, h16, wh, wb, hall⟩

/-- Limbs of a word list, as a flat field list (an 18-limb digest is `limbsF` of 6 words). -/
def limbsF (ws : List Nat) : List F := ws.flatMap wF

/-- **A node consumer** (row-layout independent): words `IV384 ‖ l ‖ r ‖ padW ‖ out ‖ ox`, with `l`, `r`,
`out` given as 6 field triples each.  Then `l`, `r` decode to 64-bit digests `dl`, `dr` and `out`
is the limbs of the 6 words `dout` with `wbytes dout = sha384 (wbytes dl ++ wbytes dr)`. -/
theorem consumer_node_sha384 {chip : List IfMsg} (hcon : Sha512IfContract SegSha.compressW chip)
    (hlt : ∀ x ∈ chip, x.cid < P) {cid : F} {W : Nat → List F} (hW3 : ∀ k, k < 32 → (W k).length = 3)
    (hiv : ∀ k, k < 8 → W k = wF (NearSpecV3.E2E.Bnd.IV384.getD k 0))
    (hpad : ∀ k, k < 4 → W (20 + k) = wF (padW.getD k 0))
    (hin : ∀ m, m < 16 → (cid :: ((m : Nat) : F) :: (W (2 * m) ++ W (2 * m + 1))) ∈ chip.map ifF) :
    ∃ dl dr dout : List Nat, dl.length = 6 ∧ dr.length = 6 ∧ dout.length = 6 ∧
      W64 dl ∧ W64 dr ∧ W64 dout ∧
      (∀ k, k < 6 → W (8 + k) = wF (dl.getD k 0)) ∧ (∀ k, k < 6 → W (14 + k) = wF (dr.getD k 0)) ∧
      (∀ k, k < 6 → W (24 + k) = wF (dout.getD k 0)) ∧
      wbytes dout = NearSpecV3.E2E.Bnd.sha384 (wbytes (dl ++ dr)) := by
  obtain ⟨h, blk, h8, h16, wh, wb, hW⟩ := consumer_sound compressW_ok hcon hlt hW3 hin
  have hco := compressW_ok h blk
  have g1 : ∀ k, k < 8 → (h ++ blk ++ compressW h blk).getD k 0 = h.getD k 0 := by
    intro k hk; simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_left (by omega)]
  have g2 : ∀ k, k < 16 → (h ++ blk ++ compressW h blk).getD (8 + k) 0 = blk.getD k 0 := by
    intro k hk; simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
    simp [h8]
  have g3 : ∀ k, k < 8 → (h ++ blk ++ compressW h blk).getD (24 + k) 0 = (compressW h blk).getD k 0 := by
    intro k hk; simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp [h8, h16]; omega)]
    have : 24 + k - 8 - 16 = k := by omega
    simp [h8, h16, this]
  have getw : ∀ (l : List Nat), W64 l → ∀ k, l.getD k 0 < 2 ^ 64 := by
    intro l hl k
    rw [List.getD_eq_getElem?_getD]
    rcases e : l[k]? with _ | w
    · simp
    · exact hl w (List.mem_of_getElem? e)
  -- `h = IV384`
  have hh : h = NearSpecV3.E2E.Bnd.IV384 := by
    apply List.ext_getElem? ; intro k
    by_cases hk : k < 8
    · have e := (hW k (by omega)).symm.trans (hiv k hk)
      rw [g1 k hk] at e
      have := wF_inj (getw h wh k) (by
        have : ∀ k, NearSpecV3.E2E.Bnd.IV384.getD k 0 < 2 ^ 64 := getw _ (w64_of_all _ (by decide))
        exact this k) e
      simp only [List.getD_eq_getElem?_getD] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by simp [NearSpecV3.E2E.Bnd.IV384]; omega)] at this ⊢
      simp only [Option.getD_some] at this; rw [this]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [NearSpecV3.E2E.Bnd.IV384]; omega)]
  subst hh
  -- the block is `dl ‖ dr ‖ padW`
  refine ⟨blk.take 6, (blk.drop 6).take 6, (compressW NearSpecV3.E2E.Bnd.IV384 blk).take 6, by simp [h16], by simp [h16],
    by simp [hco.1], fun w hw => wb w (List.mem_of_mem_take hw),
    fun w hw => wb w (List.mem_of_mem_drop (List.mem_of_mem_take hw)),
    fun w hw => hco.2 w (List.mem_of_mem_take hw), ?_, ?_, ?_, ?_⟩
  · intro k hk; rw [hW (8 + k) (by omega), g2 k (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk]
  · intro k hk; rw [hW (14 + k) (by omega), show 14 + k = 8 + (6 + k) by omega, g2 (6 + k) (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hk]
  · intro k hk; rw [hW (24 + k) (by omega), g3 k (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk]
  · -- the padding words force `blk = dl ‖ dr ‖ padW`
    have hp : blk.drop 12 = padW := by
      apply List.ext_getElem? ; intro k
      by_cases hk : k < 4
      · have e := (hW (20 + k) (by omega)).symm.trans (hpad k hk)
        rw [show 20 + k = 8 + (12 + k) by omega, g2 (12 + k) (by omega)] at e
        have := wF_inj (getw blk wb _) (by
          have : ∀ k, padW.getD k 0 < 2 ^ 64 := getw _ (w64_of_all _ (by decide))
          exact this k) e
        rw [List.getElem?_drop]
        simp only [List.getD_eq_getElem?_getD] at this
        rw [List.getElem?_eq_getElem (show 12 + k < blk.length by omega),
          List.getElem?_eq_getElem (show k < padW.length by simp [padW]; omega)] at this ⊢
        simp only [Option.getD_some] at this; rw [this]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [padW]; omega)]
    have eb : blk = blk.take 6 ++ (blk.drop 6).take 6 ++ padW := by
      rw [← hp, List.append_assoc, show blk.drop 12 = (blk.drop 6).drop 6 by simp [List.drop_drop],
        List.take_append_drop, List.take_append_drop]
    rw [sha384_node _ _ (by simp [h16]) (by simp [h16]), ← eb]

/-- **Lane B's record-level node** (`comp_node`) with the chip's compression is SHA-384:
`o = enc (nodeH compressW dl dr)` and the digest's bytes are `sha384 (bytes dl ++ bytes dr)`. -/
theorem comp_node_sha384 {chip : List IfMsg} (hC : Sha512IfContract compressW chip) {cid : Nat}
    {l r o ox : List (List Nat)} (hl : l.length = 6) (hr : r.length = 6) (ho : o.length = 6) (hox : ox.length = 2)
    (hin : ∀ x ∈ compRecv cid (StateM5a.IV384.map StateM5a.wlimbs ++ (l ++ r ++ padW.map StateM5a.wlimbs) ++ (o ++ ox)), x ∈ chip) :
    ∃ dl dr : Dig, l = StateM5a.Sha512If.enc dl ∧ r = StateM5a.Sha512If.enc dr ∧
      o = StateM5a.Sha512If.enc (nodeH compressW dl dr) ∧
      wbytes (nodeH compressW dl dr).1 = NearSpecV3.E2E.Bnd.sha384 (wbytes (dl.1 ++ dr.1)) := by
  obtain ⟨dl, dr, e1, e2, e3⟩ := comp_node compressW_ok hC hl hr ho hox hin
  exact ⟨dl, dr, e1, e2, e3, nodeH_sha384 dl dr⟩

end SegSha

#print axioms SegSha.seg_holds_false
#print axioms SegSha.seg_if_bits
#print axioms SegSha.if_recv_mem
#print axioms SegSha.consumer_sound
#print axioms SegSha.consumer_node_sha384
#print axioms SegSha.comp_node_sha384

end WasmBase
