import WasmBase.PrepSound
import WasmBase.PrepDec
/-!
# WasmBase.PrepDecSound — what the PREP AIR's decoder tables prove (A-T4)

* **`cb_lookup_sound` [K]** — the byte link: every byte lookup on `busLB` with count 1 (the HDR and
  CODE window reads) carries `[p, m[p]]` with `p < |m|`, for the SHA-256 table's message `m` (the
  bytes the public code hash is the digest of).  Proof: `CB`'s `pos` column is the row index and
  its live rows are exactly `pos < len`; each message byte is received by a SHA byte slot (the
  classical frame contract, `sha_digest_contract_closed`) from `CB` on `busCB`, whose counts are bits,
  so `CB` row `i` holds `m[i]`; `CB` answers `busLB` only on live rows (`mult · (1 − live) = 0`).
* **`PrepDecodeSound`** — the full AIR obligation `Holds prepAir ⇒ DecodeCert` (the window decode
  of each CODE row = `PrepDec.decInstr`, the HDR rows = `PrepDec.walk`, the CODE/FUNC layout).  Its
  byte-link layer is `cb_lookup_sound`; the row-level layers are stated, not yet proved here.
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

end PrepDecSound
end WasmBase
