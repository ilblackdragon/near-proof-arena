import WasmBase.PrepSound
import WasmBase.PrepDec
/-!
# WasmBase.PrepDecSound — what the PREP AIR's decoder tables prove (A-T4)

* **Proved [K], the byte-read layer:**
  * `cb_pos`, `cb_live_of_lt`, `cb_live_lt`, `cb_last`, `cb_drop` — `CB`'s `pos` column is the row
    index and its live rows are exactly `r < len` (public 32);
  * `occLB`, `lb_read_sound` — every byte read on `busLB` with count 1 (the HDR and CODE window
    reads, whose counts are boolean columns) carries `[r, byte_r]` for a live `CB` row `r < len`
    (`CB` answers only on live rows: `mult · (1 − live) = 0`).
* **`PrepDecodeSound`** — the full AIR obligation `Holds prepAir ⇒ DecodeCert` of the SHA message.
  Still to prove: `CB` row `r` holds `m[r]` (the `busCB` permutation with the SHA byte slots, via the
  classical frame contract `sha_digest_contract_closed`); the HDR induction (row `r` = `walk m r`);
  the CODE window decode (= `decInstr`); the CODE / FUNC layout.
-/
namespace WasmBase
namespace PrepDecSound

open ZkFormal.Algebra Chips Chips.Prep

set_option linter.unusedSimpArgs false

/-- The cached CODE / FUNC record matrices of a trace (tables 4, 5; columns 0–7). -/
def cmOf (tr : Trace) : List (List Nat) :=
  (List.range (tr.height 4)).map fun r => (List.range 8).map fun i => (tr.cell 4 r i).toNat
def fmOf (tr : Trace) : List (List Nat) :=
  (List.range (tr.height 5)).map fun r => (List.range 8).map fun i => (tr.cell 5 r i).toNat
/-- The FUNC rows' body indices (live rows). -/
def ksOf (tr : Trace) : List Nat :=
  ((List.range (tr.height 5)).filter fun r => tr.cell 5 r FuncP.live = 1).map
    fun r => (tr.cell 5 r FuncP.kk).toNat

/-- Every table height a power of two at most `2^22` (the backend's committed shapes). -/
def PowHeights (tr : Trace) : Prop :=
  ∀ t, t < prepAir.tables.length → tr.height t = 2 ^ Nat.log2 (tr.height t) ∧
    1 ≤ Nat.log2 (tr.height t) ∧ Nat.log2 (tr.height t) ≤ 22

/-- **The PREP decoder obligation**: an accepted PREP trace's cached matrices are the hashed code's
decoded bodies. -/
def PrepDecodeSound : Prop :=
  ∀ pub tr, Holds prepAir pub tr → PowHeights tr →
    ∃ m : ArenaCore.Bytes, ArenaCore.sha256 m = PrepSound.hashOf pub ∧
      PrepDec.DecodeCert (m.map (·.toNat)) (tr.height 4) (tr.height 5) (cmOf tr) (fmOf tr) (ksOf tr)


/-! ## 1. `CB`: positions and the live range -/

theorem tbl2 : prepAir.tables[2]'(by decide) = CB.table := rfl

theorem cbc {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r : Nat} (hr : r < tr.height 2)
    {e : Expr} (he : e ∈ CB.constraints) : e.eval (tr.row pub 2 r) = 0 :=
  H.constr 2 (by decide) r hr e (by rw [tbl2]; exact he)

theorem cb_pos {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) :
    ∀ r, r < tr.height 2 → tr.cell 2 r CB.pos = (r : F) := by
  intro r
  induction r with
  | zero =>
    intro hr
    have c := cbc H hr (e := .first * v CB.pos) (by simp [CB.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool] at c
    have h : tr.cell 2 0 CB.pos = 0 := by grind
    rw [h]; rfl
  | succ r ih =>
    intro hr
    have c := cbc H (r := r) (by omega) (e := .trans * (nv CB.pos - v CB.pos - 1)) (by simp [CB.constraints])
    have hl : (r + 1 == tr.height 2) = false := by simp; omega
    have hm : (r + 1) % tr.height 2 = r + 1 := Nat.mod_eq_of_lt hr
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool, hl, hm, Bool.false_eq_true, ite_false] at c
    rw [ih (by omega)] at c
    have : tr.cell 2 (r + 1) CB.pos = (r : F) + 1 := by grind
    rw [this]
    have e : ((r + 1 : Nat) : F) = (r : F) + 1 := by fp_ring
    exact e.symm

theorem cb_live_bit {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r : Nat}
    (hr : r < tr.height 2) : tr.cell 2 r CB.live = 0 ∨ tr.cell 2 r CB.live = 1 := by
  have c := cbc H hr (e := bool (v CB.live)) (by simp [CB.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool] at c
  exact bool_cases c

/-- The public length as a natural. -/
def lenOf (pub : List F) : Nat := (pub.getD pubLen 0).toNat

theorem len_of_cast {pub : List F} {r : Nat} (hr : r + 1 < P) (e : ((r : F) + 1) = pub.getD pubLen 0) :
    r + 1 = lenOf pub := by
  have e2 : ((r + 1 : Nat) : F) = (r : F) + 1 := by fp_ring
  have e' : ((r + 1 : Nat) : F) = pub.getD pubLen 0 := by rw [e2]; exact e
  have := congrArg Fp.toNat e'
  rw [Fp.toNat_cast_of_lt hr] at this
  exact this

/-- The last row, if live, is position `len − 1`. -/
theorem cb_last {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) (hP : tr.height 2 < P)
    {r : Nat} (hr : r + 1 = tr.height 2) (hl : tr.cell 2 r CB.live = 1) : r + 1 = lenOf pub := by
  have c := cbc H (r := r) (by omega) (e := .last * (v CB.live * (v CB.pos + 1 - pv pubLen)))
    (by simp [CB.constraints])
  have hlast : (r + 1 == tr.height 2) = true := by simp; omega
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool, hlast, ite_true, hl] at c
  rw [cb_pos H r (by omega)] at c
  exact len_of_cast (by omega) (by grind)

/-- A live row followed by a dead one is position `len − 1`. -/
theorem cb_drop {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) (hP : tr.height 2 < P)
    {r : Nat} (hr : r + 1 < tr.height 2) (hl : tr.cell 2 r CB.live = 1)
    (h0 : tr.cell 2 (r + 1) CB.live = 0) : r + 1 = lenOf pub := by
  have c := cbc H (r := r) (by omega)
    (e := .trans * (v CB.live * (1 - nv CB.live) * (v CB.pos + 1 - pv pubLen))) (by simp [CB.constraints])
  have hlast : (r + 1 == tr.height 2) = false := by simp; omega
  have hm : (r + 1) % tr.height 2 = r + 1 := Nat.mod_eq_of_lt hr
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool, hlast, hm, Bool.false_eq_true, ite_false, hl, h0] at c
  rw [cb_pos H r (by omega)] at c
  exact len_of_cast (by omega) (by grind)

/-- Live rows are below the length. -/
theorem cb_live_lt {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) (hP : tr.height 2 < P) :
    ∀ k r, r + k + 1 = tr.height 2 → tr.cell 2 r CB.live = 1 → r + 1 ≤ lenOf pub := by
  intro k
  induction k with
  | zero => intro r hr hl; exact Nat.le_of_eq (cb_last H hP (by omega) hl)
  | succ k ih =>
    intro r hr hl
    rcases cb_live_bit H (r := r + 1) (by omega) with h0 | h1
    · exact Nat.le_of_eq (cb_drop H hP (by omega) hl h0)
    · have := ih (r + 1) (by omega) h1; omega

/-- Rows below the length are live (and exist). -/
theorem cb_live_of_lt {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) (hP : tr.height 2 < P) :
    ∀ r, r < lenOf pub → r < tr.height 2 ∧ tr.cell 2 r CB.live = 1 := by
  have h0 : 0 < tr.height 2 := by have := H.heightPos 2 (by decide); omega
  intro r
  induction r with
  | zero =>
    intro _
    have c := cbc H (r := 0) h0 (e := .first * (v CB.live - 1)) (by simp [CB.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, Expr.eval_nxt, Expr.eval_pub, Expr.eval_c, Expr.eval, Trace.row, v, nv, pv, Chips.bool] at c
    exact ⟨h0, by simp at c; grind⟩
  | succ r ih =>
    intro hr
    obtain ⟨hr1, hl⟩ := ih (by omega)
    by_cases hlast : r + 1 = tr.height 2
    · exfalso; have := cb_last H hP hlast hl; omega
    · refine ⟨by omega, ?_⟩
      rcases cb_live_bit H (r := r + 1) (by omega) with h0' | h1
      · exfalso; have := cb_drop H hP (by omega) hl h0'; omega
      · exact h1


theorem bus_ne {T : Table} {b : Nat} (h : (T.inters.map (·.bus)).all (· != b) = true)
    {i : Inter} (hi : i ∈ T.inters) : i.bus ≠ b := by
  have := List.all_eq_true.1 h i.bus (List.mem_map_of_mem hi)
  simpa using this

/-! ## 2. `busLB`: every byte read is a live `CB` row -/

theorem hdr_u_bit {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r i : Nat}
    (hr : r < tr.height 3) (hi : i < 6) :
    tr.cell 3 r (Hdr.uc i) = 0 ∨ tr.cell 3 r (Hdr.uc i) = 1 := by
  have hm : bool (v (Hdr.uc i)) ∈ Hdr.constraints := by
    unfold Hdr.constraints
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_self⟩)
  have c := H.constr 3 (by decide) r hr _ (by show bool (v (Hdr.uc i)) ∈ Hdr.table.constraints; exact hm)
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Trace.row, v] at c
  exact bool_cases c

theorem code_u_bit {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r i : Nat}
    (hr : r < tr.height 4) (hi : i < 11) :
    tr.cell 4 r (CodeP.uc i) = 0 ∨ tr.cell 4 r (CodeP.uc i) = 1 := by
  have hm : bool (v (CodeP.uc i)) ∈ CodeP.constraints := by
    unfold CodeP.constraints
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_self⟩)
  have c := H.constr 4 (by decide) r hr _ (by show bool (v (CodeP.uc i)) ∈ CodeP.table.constraints; exact hm)
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Trace.row, v] at c
  exact bool_cases c

theorem toNat_bit {x : F} (h : x = 0 ∨ x = 1) : x.toNat ≤ 1 := by rcases h with rfl | rfl <;> decide

/-- **Every occurrence on `busLB`**: a `CB` answer `[pos, byte]` with count `mult`, or a read with a
bit count. -/
theorem occLB {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {o : Occ}
    (ho : o ∈ occs prepAir tr pub) (hb : o.1 = busLB) :
    (∃ r, r < tr.height 2 ∧
      o = (busLB, false, [tr.cell 2 r CB.pos, tr.cell 2 r CB.byte], (tr.cell 2 r CB.mult).toNat)) ∨
    (o.2.1 = true ∧ o.2.2.2 ≤ 1) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.1 ho
  simp only at hb
  match t, ht with
  | 0, _ =>
    exact absurd hb (bus_ne (T := Prep.phdrTable) (by decide) hi)
  | 1, _ =>
    exact absurd hb (bus_ne (T := Prep.shaTableD) (by decide) hi)
  | 2, _ =>
    have hi' : i ∈ CB.inters := hi
    simp only [CB.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi'
    rcases hi' with rfl | rfl
    · simp [busCB, busLB] at hb
    · exact .inl ⟨r, hr, by simp [Trace.row, v]⟩
  | 3, _ =>
    have hi' : i ∈ Hdr.inters := hi
    simp only [Hdr.inters, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false] at hi'
    rcases hi' with ⟨j, hj, rfl⟩ | rfl
    · exact .inr ⟨rfl, by simpa [Trace.row, v] using toNat_bit (hdr_u_bit H hr hj)⟩
    · simp [busBody, busLB] at hb
  | 4, _ =>
    have hi' : i ∈ CodeP.inters := hi
    simp only [CodeP.inters, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false] at hi'
    rcases hi' with ⟨j, hj, rfl⟩ | rfl
    · exact .inr ⟨rfl, by simpa [Trace.row, v] using toNat_bit (code_u_bit H hr hj)⟩
    · simp [busFn, busLB] at hb
  | 5, _ =>
    exact absurd hb (bus_ne (T := Prep.FuncP.table) (by decide) hi)
  | n + 6, h => exact absurd h (by simp [prepAir])

theorem cb_mult_live {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r : Nat}
    (hr : r < tr.height 2) (hm : tr.cell 2 r CB.mult ≠ 0) : tr.cell 2 r CB.live = 1 := by
  have c := cbc H hr (e := v CB.mult * (1 - v CB.live)) (by simp [CB.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Trace.row, v] at c
  rcases mul_eq_zero' c with h | h
  · exact absurd h hm
  · grind

/-- **The byte reads are code bytes**: every read on `busLB` with count 1 carries `[r, byte_r]` for
a live `CB` row `r < len`. -/
theorem lb_read_sound {pub : List F} {tr : Trace} (H : Holds prepAir pub tr)
    (hP : tr.height 2 < P) {o : Occ} (ho : o ∈ occs prepAir tr pub) (hb : o.1 = busLB)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ r, r < lenOf pub ∧ r < tr.height 2 ∧ o.2.2.1 = [(r : F), tr.cell 2 r CB.byte] := by
  refine lookup_sound H busLB
    (fun msg => ∃ r, r < lenOf pub ∧ r < tr.height 2 ∧ msg = [(r : F), tr.cell 2 r CB.byte])
    ?_ ?_ ho hb hs hc
  · intro o' ho' hb' hs' hc'
    rcases occLB H ho' hb' with ⟨r, hr, rfl⟩ | ⟨hs2, -⟩
    · have hm : tr.cell 2 r CB.mult ≠ 0 := by
        intro h0; apply hc'; show (tr.cell 2 r CB.mult).toNat = 0; rw [h0]; rfl
      have hl := cb_mult_live H hr hm
      have hlt : r < lenOf pub := by
        have := cb_live_lt H hP (tr.height 2 - r - 1) r (by omega) hl; omega
      exact ⟨r, hlt, hr, by simp [cb_pos H r hr]⟩
    · simp [hs2] at hs'
  · intro o' ho' hb' hs'
    rcases occLB H ho' hb' with ⟨r, hr, rfl⟩ | ⟨-, h⟩
    · simp at hs'
    · exact h

end PrepDecSound
end WasmBase
