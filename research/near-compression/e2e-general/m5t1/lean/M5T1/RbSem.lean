import M5T1.EnterC
import M5T1.Bus

/-!
# M5T1.RbSem — the resume edge's boundary rules, on any satisfying trace (F-4)

`RB` (table 6 of `fullAir`) carries `BndLay.rbCons` on row 0, over the public boundary pair
(`B_in` = 834 B call record at offset 247, `B_out` = 450 B engine record at offset 1081). On every
`Holds (fullAir tape xtape)` trace whose public values are bytes:

* the input record is a call record (`phase 6`, `inCall`, a Wasm part) with `vmAcc = bdigest []`
  and `gasUsed = gasBurnt`, `compute`, `balanceBurnt` = `RX`'s public totals in (`in_facts`);
* **`rb_out`**: the output record is `resRec B st a₁ a₂ g cm tb` — the input record with `phase 1`,
  out of the call, `receiptIdx + 1`, `rPrepaid = rBurnt = rUsed = 0`, `vmAcc = bdigest []`, the
  totals out, and the three fields the rules leave to other tables as the output's own bytes
  (`stRoot`: `STMA`; `outcomeAcc`, `outRcpt0`: `ACC`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false

namespace M5T1.RbSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd
open ArenaCore.Bytes (beN beN_length beToNat beToNat_beN)

abbrev Tp := List (Nat × Bool × List Nat)

/-- Offsets of the boundary pair in the resume leaf's public values (`Rx.PL`). -/
def BIN : Nat := 247
def BOUT : Nat := 1081
theorem bin_eq : Rx.PL.off "bin" = BIN := by decide
theorem bout_eq : Rx.PL.off "bout" = BOUT := by decide

/-! ## 0. Little-endian sums -/

/-- `Σ_{k<n} 256^k · y k`, recursively. -/
def sumLE (y : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => y 0 + 256 * sumLE (fun i => y (i + 1)) n

theorem sumLE_lt (y : Nat → Nat) : ∀ n, (∀ k < n, y k < 256) → sumLE y n < 256 ^ n
  | 0, _ => by simp [sumLE]
  | n + 1, h => by
    have h0 := h 0 (by omega)
    have := sumLE_lt (fun i => y (i + 1)) n (fun k hk => h (k + 1) (by omega))
    simp only [sumLE, Nat.pow_succ]
    have : 256 * sumLE (fun i => y (i + 1)) n + 256 ≤ 256 ^ n * 256 := by
      rw [Nat.mul_comm (256 ^ n)]; omega
    omega

/-- **Digits of a little-endian sum.** -/
theorem sumLE_digit (y : Nat → Nat) : ∀ n, (∀ k < n, y k < 256) →
    ∀ k < n, sumLE y n / 256 ^ k % 256 = y k
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    have h0 := h 0 (by omega)
    simp only [sumLE]
    cases k with
    | zero => simp; omega
    | succ k =>
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show (y 0 + 256 * sumLE (fun i => y (i + 1)) n) / 256 = sumLE (fun i => y (i + 1)) n by omega]
      exact sumLE_digit (fun i => y (i + 1)) n (fun j hj => h (j + 1) (by omega)) k (by omega)

/-- **A number's digits sum to it** (mod `256^n`). -/
theorem sumLE_of_digits (v : Nat) : ∀ n, sumLE (fun k => v / 256 ^ k % 256) n = v % 256 ^ n
  | 0 => by simp [sumLE, Nat.mod_one]
  | n + 1 => by
    simp only [sumLE]
    have := sumLE_of_digits (v / 256) n
    have e : (fun i => v / 256 ^ (i + 1) % 256) = (fun k => v / 256 / 256 ^ k % 256) := by
      funext i; rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    rw [e, this, Nat.pow_succ, Nat.mul_comm (256 ^ n), Nat.mod_mul, Nat.pow_zero, Nat.div_one]

/-- **A carry chain adds its carry-in**: `x k + ci k = y k + 256 · ci (k+1)` for `k < n` gives
`Σ x + ci 0 = Σ y + 256^n · ci n`. -/
theorem sumLE_chain (x y ci : Nat → Nat) : ∀ n, (∀ k < n, x k + ci k = y k + 256 * ci (k + 1)) →
    sumLE x n + ci 0 = sumLE y n + 256 ^ n * ci n
  | 0, _ => by simp [sumLE]
  | n + 1, h => by
    have h0 := h 0 (by omega)
    have := sumLE_chain (fun i => x (i + 1)) (fun i => y (i + 1)) (fun i => ci (i + 1)) n
      (fun k hk => h (k + 1) (by omega))
    simp only [sumLE, Nat.pow_succ] at this ⊢
    rw [Nat.mul_comm (256 ^ n) 256, Nat.mul_assoc]
    omega

/-- Big-endian bytes from little-endian digit facts. -/
theorem bytesOf_le (pub : List Fp) (a w : Nat) (y : Nat → Nat) (hy : ∀ k < w, y k < 256)
    (h : ∀ k < w, pv pub (a + (w - 1 - k)) = y k) : bytesOf pub a w = beN w (sumLE y w) :=
  bytesOf_num pub a w _ fun k hk => by rw [h k hk, sumLE_digit y w hy k hk]

/-- Little-endian digit `k` of a big-endian field read from its bytes. -/
theorem digit_of_bytes (pub : List Fp) (a : Nat) : ∀ (w v : Nat), beN w v = bytesOf pub a w →
    ∀ k < w, pv pub (a + (w - 1 - k)) % 256 = v / 256 ^ k % 256
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | w + 1, v, h, k, hk => by
    rw [bytesOf_add, beN] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [beN_length, bytesOf_length])
    cases k with
    | zero =>
      have := congrArg (fun l => (l.headD 0).toNat) h2
      simp only [List.headD_cons, bytesOf, List.range_one, List.map_cons, List.map_nil,
        Nat.add_zero] at this
      have e : ∀ n : Nat, (UInt8.ofNat n).toNat = n % 256 := fun n => by simp
      rw [e, e, Nat.mod_mod] at this
      simp only [Nat.pow_zero, Nat.div_one, show w + 1 - 1 - 0 = w by omega]
      exact this.symm
    | succ k =>
      have := digit_of_bytes pub a w (v / 256) h1 k (by omega)
      rw [show w + 1 - 1 - (k + 1) = w - 1 - k by omega, this, Nat.pow_succ', ← Nat.div_div_eq_div_mul]

/-! ## 1. Row 0 of `RB` -/

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp}

theorem rb_lt : 6 < (fullAir tape xtape).tables.length := by rw [Bus.fullAir_len]; decide

theorem rb_row0 (H : Holds (fullAir tape xtape) pub tr) :
    ∀ e ∈ Rb.table.constraints, ev tr 6 0 pub e = 0 := by
  intro e he
  have hpos : 0 < tr.height 6 := by unfold Trace.height; exact Nat.two_pow_pos _
  exact ev_of_eval (H.constr 6 rb_lt 0 hpos e he)

theorem ev_pub6 (i : Nat) : ev tr 6 0 pub (.pub i) = pv pub i := rfl

theorem ev_first6 : ev tr 6 0 pub .isFirst = 1 := rfl

theorem gpe {a b : Nat} (h : ev tr 6 0 pub (gate (Expr.pub a - Expr.pub b)) = 0) :
    pv pub a = pv pub b := by
  unfold gate at h
  rw [show (Expr.isFirst * (Expr.pub a - Expr.pub b)) = Expr.mul .isFirst (Expr.pub a - Expr.pub b)
    from rfl, ev_mul_gate _ ev_first6] at h
  have ha := ev_lt (tr := tr) (t := 6) (r := 0) (pub := pub) (.pub a)
  have hb := ev_lt (tr := tr) (t := 6) (r := 0) (pub := pub) (.pub b)
  rw [show (Expr.pub a - Expr.pub b) = Expr.add (.pub a) (.neg (.pub b)) from rfl, ev_add, ev_neg,
    ev_pub6, ev_pub6] at h
  rw [ev_pub6] at ha hb
  omega

theorem gce {a v : Nat} (hv : v < 2013265921) (h : ev tr 6 0 pub (gate (Expr.pub a - K v)) = 0) :
    pv pub a = v := by
  unfold gate at h
  rw [show (Expr.isFirst * (Expr.pub a - K v)) = Expr.mul .isFirst (Expr.pub a - K v) from rfl,
    ev_mul_gate _ ev_first6] at h
  have ha := ev_lt (tr := tr) (t := 6) (r := 0) (pub := pub) (.pub a)
  rw [show (Expr.pub a - K v) = Expr.add (.pub a) (.neg (.const v)) from rfl, ev_add, ev_neg,
    ev_const, ev_pub6, Nat.mod_eq_of_lt hv] at h
  rw [ev_pub6] at ha
  omega
end

/-! ## 2. Membership of the rule constraints -/

def SI : Side := Rb.SI
def SO : Side := Rb.SO
def PG : String → Nat → Expr := fun g k => Rx.pub g k
def CY : Nat → Expr := fun k => Rb.c "cri" k

theorem mem_rb {e : Expr} (h : e ∈ rbCons SI SO PG CY) : e ∈ Rb.table.constraints :=
  List.mem_append_right _ h

theorem mem_field {p : String × Nat} (hp : p ∈ engF) {e : Expr}
    (he : e ∈ resCons SI SO PG CY p.1 p.2 (resRule p.1)) : e ∈ Rb.table.constraints := by
  apply mem_rb
  unfold rbCons
  simp only [List.mem_append]
  exact .inr (List.mem_flatMap.2 ⟨p, hp, he⟩)

theorem mem_in {e : Expr}
    (he : e ∈ constF SI "phase" 6 ∨ e ∈ constF SI "inCall" 1 ∨ e ∈ constF SI "wasmTag" 1 ∨
      e ∈ ((List.range 42).map fun j => gate (SI.b "vmAcc" j - K (emptyDig.getD j 0))) ∨
      e ∈ eqLE SI "gasUsed" (PG "gin") ∨ e ∈ eqLE SI "gasBurnt" (PG "gin") ∨
      e ∈ eqLE SI "compute" (PG "cin") ∨ e ∈ eqLE SI "balanceBurnt" (PG "tbin")) :
    e ∈ Rb.table.constraints := by
  apply mem_rb
  unfold rbCons
  simp only [List.mem_append]
  rcases he with h | h | h | h | h | h | h | h
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)

/-! ## 3. Field semantics (public-value level) -/

theorem si_b (f : String) (j : Nat) : SI.b f j = .pub (BIN + callF.off f + j) := by
  simp [SI, Rb.SI, Side.b, bin_eq]

theorem so_b (f : String) (j : Nat) : SO.b f j = .pub (BOUT + engF.off f + j) := by
  simp [SO, Rb.SO, Side.b, bout_eq]

theorem fw_engF_callF {p : String × Nat} (hp : p ∈ engF) : fw callF p.1 = fw engF p.1 := by
  simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
include H

theorem copy_r {p : String × Nat} (hp : p ∈ engF) (hr : resRule p.1 = .copy) :
    ∀ j < fw engF p.1, pv pub (BIN + callF.off p.1 + j) = pv pub (BOUT + engF.off p.1 + j) := by
  intro j hj
  have hm : gate (SI.b p.1 j - SO.b p.1 j) ∈ resCons SI SO PG CY p.1 p.2 (resRule p.1) := by
    rw [hr]
    have : fw SI.L p.1 = fw engF p.1 := fw_engF_callF hp
    exact List.mem_map.2 ⟨j, List.mem_range.2 (this ▸ hj), rfl⟩
  have h := rb_row0 H _ (mem_field hp hm)
  rw [si_b, so_b] at h
  exact gpe h


theorem constF_sem (S : Side) (f : String) (v : Nat)
    (hm : ∀ e ∈ constF S f v, e ∈ Rb.table.constraints) :
    ∀ k < fw S.L f, pv pub (S.base + S.L.off f + (fw S.L f - 1 - k)) = v / 256 ^ k % 256 := by
  intro k hk
  have h := rb_row0 H _ (hm _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  exact gce (by have := Nat.mod_lt (v / 256 ^ k) (show 0 < 256 by decide); omega) h

theorem eqLE_sem (S : Side) (f : String) (b : Nat)
    (hm : ∀ e ∈ eqLE S f (fun k => Expr.pub (b + k)), e ∈ Rb.table.constraints) :
    ∀ k < fw S.L f, pv pub (S.base + S.L.off f + (fw S.L f - 1 - k)) = pv pub (b + k) := by
  intro k hk
  exact gpe (rb_row0 H _ (hm _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)))

theorem dig_sem' (S : Side) (f : String) (hm : ∀ e ∈ ((List.range 42).map fun j =>
      gate (S.b f j - K (emptyDig.getD j 0))), e ∈ Rb.table.constraints) :
    ∀ j < 42, pv pub (S.base + S.L.off f + j) = emptyDig.getD j 0 := by
  intro j hj
  exact gce (by have := emptyDig_lt j; omega)
    (rb_row0 H _ (hm _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))

/-- The carry bits of `receiptIdx + 1` are bits. -/
theorem cri_bit : ∀ k < 7, ev tr 6 0 pub (Rb.c "cri" k) ≤ 1 := by
  intro k hk
  have h := rb_row0 H (bool (Rb.c "cri" k))
    (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  unfold bool at h
  rw [show (Rb.c "cri" k * (Rb.c "cri" k - 1)) = Expr.mul (Rb.c "cri" k)
    (Expr.add (Rb.c "cri" k) (.neg (.const 1))) from rfl] at h
  rcases ev_mul_eq_zero h with h | h
  · omega
  · have hl := ev_lt (tr := tr) (t := 6) (r := 0) (pub := pub) (Rb.c "cri" k)
    simp only [ev_add, ev_neg, ev_const] at h
    omega
end


section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp}

theorem lin_sem (a b c d : Expr) (ha : ev tr 6 0 pub a < 256) (hb : ev tr 6 0 pub b ≤ 1)
    (hc : ev tr 6 0 pub c < 256) (hd : ev tr 6 0 pub d ≤ 1)
    (h : ev tr 6 0 pub (gate (a + b - c - K 256 * d)) = 0) :
    ev tr 6 0 pub a + ev tr 6 0 pub b = ev tr 6 0 pub c + 256 * ev tr 6 0 pub d := by
  unfold gate at h
  rw [show (Expr.isFirst * (a + b - c - K 256 * d)) = Expr.mul .isFirst
      (Expr.add (Expr.add (Expr.add a b) (.neg c)) (.neg (.mul (.const 256) d))) from rfl,
    ev_mul_gate _ ev_first6] at h
  simp only [ev_add, ev_neg, ev_mul, ev_const] at h
  omega

variable (H : Holds (fullAir tape xtape) pub tr)
include H

/-- **`receiptIdx` out = in + 1** (digit level): with `x k`, `y k` the little-endian bytes of the
input / output field, `Σ x + 1 = Σ y`. -/
theorem inc_sem (hb : ∀ i < 1531, pv pub i < 256) :
    sumLE (fun k => pv pub (BIN + callF.off "receiptIdx" + (7 - k))) 8 + 1 =
      sumLE (fun k => pv pub (BOUT + engF.off "receiptIdx" + (7 - k))) 8 := by
  have hof1 : BIN + callF.off "receiptIdx" + 7 < 1531 := by decide
  have hof2 : BOUT + engF.off "receiptIdx" + 7 < 1531 := by decide
  let ci : Nat → Nat := fun k => if k = 0 then 1 else if k = 8 then 0 else ev tr 6 0 pub (Rb.c "cri" (k - 1))
  have hc := sumLE_chain (fun k => pv pub (BIN + callF.off "receiptIdx" + (7 - k)))
    (fun k => pv pub (BOUT + engF.off "receiptIdx" + (7 - k))) ci 8 ?_
  · simpa [ci] using hc
  intro k hk
  have hm : incCons SI SO "receiptIdx" CY ⊆ Rb.table.constraints := by
    intro e he
    have hp : ("receiptIdx", 8) ∈ engF := by decide
    exact mem_field hp (by show e ∈ resCons SI SO PG CY "receiptIdx" 8 .inc; exact he)
  have h := rb_row0 H _ (hm (List.mem_map.2 ⟨k, List.mem_range.2 (by show k < 8; exact hk), rfl⟩))
  have e1 : ev tr 6 0 pub (SI.le "receiptIdx" k) = pv pub (BIN + callF.off "receiptIdx" + (7 - k)) := by
    simp only [Side.le, si_b]; rfl
  have e2 : ev tr 6 0 pub (SO.le "receiptIdx" k) = pv pub (BOUT + engF.off "receiptIdx" + (7 - k)) := by
    simp only [Side.le, so_b]; rfl
  have hcb := cri_bit H
  have hw : fw SO.L "receiptIdx" = 8 := by decide
  have hK : ∀ v, v < 2013265921 → ev tr 6 0 pub (K v) = v := fun v hv => by
    show ev tr 6 0 pub (.const v) = v; rw [ev_const, Nat.mod_eq_of_lt hv]
  simp only [hw] at h
  rcases (by omega : k = 0 ∨ (0 < k ∧ k < 7) ∨ k = 7) with rfl | ⟨k0, k7⟩ | rfl
  · have := lin_sem _ _ _ _ (by rw [e1]; exact hb _ (by omega)) (by rw [hK 1 (by decide)]; exact Nat.le_refl 1)
      (by rw [e2]; exact hb _ (by omega)) (hcb 0 (by decide)) (by simpa [CY] using h)
    rw [e1, e2, hK 1 (by decide)] at this
    simp only [ci, ite_true, show (0 + 1 = 0) = False by simp, show (0 + 1 = 8) = False by simp,
      ite_false, Nat.add_sub_cancel]
    exact this
  · have := lin_sem _ _ _ _ (by rw [e1]; exact hb _ (by omega)) (hcb (k - 1) (by omega))
      (by rw [e2]; exact hb _ (by omega)) (hcb k (by omega))
      (by simpa [CY, show k ≠ 0 by omega, show k + 1 ≠ 8 by omega] using h)
    rw [e1, e2] at this
    simp only [ci, show k ≠ 0 by omega, show k ≠ 8 by omega, show k + 1 ≠ 0 by omega,
      show k + 1 ≠ 8 by omega, ite_false, Nat.add_sub_cancel]
    exact this
  · have := lin_sem _ _ _ _ (by rw [e1]; exact hb _ (by omega)) (hcb 6 (by decide))
      (by rw [e2]; exact hb _ (by omega)) (by rw [hK 0 (by decide)]; omega) (by simpa [CY] using h)
    rw [e1, e2, hK 0 (by decide)] at this
    simp only [ci]
    simpa using this
end

/-! ## 4. The output record -/

/-- **The resume edge's output record** (F-4): the input record out of the call, `receiptIdx + 1`,
`rPrepaid = rBurnt = rUsed = 0`, `vmAcc = bdigest []`, the totals `g`/`cm`/`tb`, the state root
`st` and the accumulators `a₁`, `[a₂]`. -/
def resRec (B : BndRec) (sr a1 a2 : ArenaCore.Bytes) (g cm tb : Nat) : BndRec :=
  ⟨B.claimDigest, 1, B.blockIdx, B.receiptIdx + 1, B.actionIdx, false, B.t, sr, B.ctxRoot, g, g, tb,
    cm, 0, 0, 0, a1, [a2], B.proposalsAcc, B.bwAcc, bdigest [], none⟩

/-- The value of a little-endian public group. -/
def valG (pub : List Fp) (g : String) (w : Nat) : Nat := sumLE (fun k => pv pub (Rx.PL.off g + k)) w

/-- The output record's bytes of field `f`. -/
def outB (pub : List Fp) (f : String) (w : Nat) : ArenaCore.Bytes := bytesOf pub (BOUT + engF.off f) w

theorem sumLE_congr {x y : Nat → Nat} : ∀ n, (∀ k < n, x k = y k) → sumLE x n = sumLE y n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumLE]
    rw [h 0 (by omega), sumLE_congr n (fun k hk => h (k + 1) (by omega))]

theorem wf_ranges {B : BndRec} (h : B.WF) : B.receiptIdx < 256 ^ 8 ∧ B.gasUsed < 256 ^ 8 ∧
    B.gasBurnt < 256 ^ 8 ∧ B.balanceBurnt < 256 ^ 16 ∧ B.compute < 256 ^ 8 := by
  obtain ⟨cd, ph, bi, ri, ai, ic, t, sr, cr, gu, gb, bb, co, rp, rb, ru, oa, orl, pa, ba, va, wa⟩ := B
  obtain ⟨h, -⟩ := h
  simp only [BndRec.codec, mapC, pairC, natC] at h
  obtain ⟨-, -, -, hri, -, -, -, -, -, hgu, hgb, hbb, hco, -⟩ := h
  exact ⟨hri, hgu, hgb, hbb, hco⟩

theorem in_fieldsR {pub : List Fp} {B : BndRec} (hwf : B.WF) {w : WasmBnd} (hw : B.wasm = some w)
    {d : ArenaCore.Bytes} (ho : B.outRcptAcc = [d]) (he : B.encode = bytesOf pub BIN 834) :
    ∀ p ∈ callF, recVal B p.1 = bytesOf pub (BIN + callF.off p.1) p.2 := by
  rw [enc_call _ hw ho, show (834 : Nat) = callF.width from by decide,
    bytesOf_lay pub callF BIN callF_nodup] at he
  have := flat_inj callF _ _ (·.2) (len_call hwf hw ho) (fun p _ => bytesOf_length _ _ _) he
  simpa using this

/-- The input record's phase is `6` (a call record). -/
theorem phase_six {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp}
    (H : Holds (fullAir tape xtape) pub tr) {B : BndRec} (hwf : B.WF)
    (he : B.encode = bytesOf pub BIN 834) : B.phase = 6 := by
  obtain ⟨rest, hr⟩ := enc_prefix B
  have hcd : B.claimDigest.length = 42 := hwf.1.1
  have hph : B.phase < 256 ^ 8 := hwf.1.2.1
  rw [hr, show (834 : Nat) = 42 + (8 + 784) from rfl, bytesOf_add, bytesOf_add] at he
  obtain ⟨-, he⟩ := List.append_inj he (by rw [hcd, bytesOf_length])
  obtain ⟨he, -⟩ := List.append_inj he (by rw [beN_length, bytesOf_length])
  have h6 := constF_sem H SI "phase" 6 (fun e h => mem_in (.inl h))
  have : bytesOf pub (BIN + 42) 8 = beN 8 6 := bytesOf_num pub _ 8 6 (fun k hk => by
    have := h6 k hk
    have e1 : callF.off "phase" = 42 := by decide
    have e2 : fw callF "phase" = 8 := by decide
    simpa [SI, Rb.SI, bin_eq, e1, e2] using this)
  rw [this] at he
  have := congrArg beToNat he
  rw [beToNat_beN, beToNat_beN, Nat.mod_eq_of_lt hph] at this
  simpa using this

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
  (hb : ∀ i < 1531, pv pub i < 256)
include H hb

theorem in_num {B : BndRec} (hin : ∀ p ∈ callF, recVal B p.1 = bytesOf pub (BIN + callF.off p.1) p.2)
    {f : String} {w v : Nat} (hf : (f, w) ∈ callF) (hv : recVal B f = beN w v)
    (hlt : BIN + callF.off f + w ≤ 1531) :
    ∀ k < w, pv pub (BIN + callF.off f + (w - 1 - k)) = v / 256 ^ k % 256 := by
  intro k hk
  have := digit_of_bytes pub (BIN + callF.off f) w v (hv.symm.trans (hin _ hf)) k hk
  rwa [Nat.mod_eq_of_lt (hb _ (by omega))] at this

/-- An input counter equal to a public group (`eqLE`), as numbers. -/
theorem in_val {B : BndRec} (hin : ∀ p ∈ callF, recVal B p.1 = bytesOf pub (BIN + callF.off p.1) p.2)
    {f g : String} {w v : Nat} (hf : (f, w) ∈ callF) (hv : recVal B f = beN w v) (hvl : v < 256 ^ w)
    (hlt : BIN + callF.off f + w ≤ 1531) (hw : fw callF f = w)
    (hm : ∀ e ∈ eqLE SI f (fun k => Expr.pub (Rx.PL.off g + k)), e ∈ Rb.table.constraints) :
    v = valG pub g w := by
  have h1 := in_num H hb hin hf hv hlt
  have h2 := eqLE_sem H SI f (Rx.PL.off g) hm
  unfold valG
  rw [← Nat.mod_eq_of_lt hvl, ← sumLE_of_digits v w]
  apply sumLE_congr
  intro k hk
  rw [← h1 k hk]
  have := h2 k (by rw [show SI.L = callF from rfl, hw]; exact hk)
  simpa [SI, Rb.SI, bin_eq, hw] using this

attribute [local irreducible] bdigest in
/-- **The resume edge's boundary rules, at record level.** If the input record `B` (a call record:
`wasm = some w`, one outgoing digest) is the public `B_in`, then it has `vmAcc = bdigest []`, its
counters are `RX`'s public totals in, `receiptIdx + 1` does not overflow, and the public `B_out`
is `resRec B` with the output's own `stRoot` / accumulator bytes and `RX`'s totals out. -/
theorem rb_out {B : BndRec} (hwf : B.WF) {w : WasmBnd} (hw : B.wasm = some w) {d : ArenaCore.Bytes}
    (ho : B.outRcptAcc = [d]) (he : B.encode = bytesOf pub BIN 834) :
    B.inCall = true ∧ B.vmAcc = bdigest [] ∧ B.gasUsed = valG pub "gin" 8 ∧
    B.gasBurnt = valG pub "gin" 8 ∧ B.compute = valG pub "cin" 8 ∧
    B.balanceBurnt = valG pub "tbin" 16 ∧ B.receiptIdx + 1 < 2 ^ 64 ∧
    (resRec B (outB pub "stRoot" 42) (outB pub "outcomeAcc" 42) (outB pub "outRcpt0" 42)
      (valG pub "gout" 8) (valG pub "cout" 8) (valG pub "tbout" 16)).encode = bytesOf pub BOUT 450 := by
  have hin := in_fieldsR hwf hw ho he
  obtain ⟨hri, hgu, hgb, hbb, hco⟩ := wf_ranges hwf
  -- the input side
  have hic : B.inCall = true := by rw [hwf.2, hw]; rfl
  have hvm : B.vmAcc = bdigest [] := by
    have h1 := hin ("vmAcc", 42) (by decide)
    have h2 := dig_sem' H SI "vmAcc" (fun e h => mem_in (.inr (.inr (.inr (.inl h)))))
    have h3 := bytesOf_dig pub (BIN + callF.off "vmAcc") emptyDig (fun j hj => by
      have := h2 j (by simpa [emptyDig] using hj); simpa [SI, Rb.SI, bin_eq] using this)
    rw [emptyDig_eq]
    exact h1.trans h3
  have hg1 : B.gasUsed = valG pub "gin" 8 := in_val H hb hin (f := "gasUsed") (by decide) rfl hgu
    (by decide) (by decide) (fun e h => mem_in (.inr (.inr (.inr (.inr (.inl h))))))
  have hg2 : B.gasBurnt = valG pub "gin" 8 := in_val H hb hin (f := "gasBurnt") (by decide) rfl hgb
    (by decide) (by decide) (fun e h => mem_in (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  have hc : B.compute = valG pub "cin" 8 := in_val H hb hin (f := "compute") (by decide) rfl hco
    (by decide) (by decide) (fun e h => mem_in (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
  have ht : B.balanceBurnt = valG pub "tbin" 16 := in_val H hb hin (f := "balanceBurnt") (by decide) rfl
    hbb (by decide) (by decide) (fun e h => mem_in (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
  -- receiptIdx + 1
  have hx : sumLE (fun k => pv pub (BIN + callF.off "receiptIdx" + (7 - k))) 8 = B.receiptIdx := by
    rw [← Nat.mod_eq_of_lt hri, ← sumLE_of_digits]
    exact sumLE_congr 8 (in_num H hb hin (f := "receiptIdx") (by decide) rfl (by decide))
  have hinc := inc_sem H hb
  rw [hx] at hinc
  have hy8 := sumLE_lt (fun k => pv pub (BOUT + engF.off "receiptIdx" + (7 - k))) 8
    (fun k hk => hb _ (by have : BOUT + engF.off "receiptIdx" + 7 < 1531 := (by decide); omega))
  refine ⟨hic, hvm, hg1, hg2, hc, ht, by rw [hinc]; exact hy8, ?_⟩
  -- the output record, field by field
  have hw' : (resRec B (outB pub "stRoot" 42) (outB pub "outcomeAcc" 42) (outB pub "outRcpt0" 42)
      (valG pub "gout" 8) (valG pub "cout" 8) (valG pub "tbout" 16)).wasm = none := rfl
  rw [enc_eng _ hw' rfl, show (450 : Nat) = engF.width from by decide,
    bytesOf_lay pub engF BOUT engF_nodup]
  congr 1
  apply List.map_congr_left
  intro p hp
  have mf : ∀ {e : Expr}, e ∈ resCons SI SO PG CY p.1 p.2 (resRule p.1) → e ∈ Rb.table.constraints :=
    fun he => mem_field hp he
  have hcopy : resRule p.1 = .copy → fw engF p.1 = p.2 →
      bytesOf pub (BIN + callF.off p.1) p.2 = bytesOf pub (BOUT + engF.off p.1) p.2 :=
    fun hr hfw => bytesOf_congr (fun j hj => copy_r H hp hr j (hfw ▸ hj))
  have hnum : ∀ v, resRule p.1 = .num v → fw engF p.1 = p.2 →
      bytesOf pub (BOUT + engF.off p.1) p.2 = beN p.2 v := by
    intro v hr hfw
    have h1 := constF_sem H SO p.1 v (fun e he => mf (by rw [hr]; exact he))
    exact bytesOf_num pub _ p.2 v (fun k hk => by
      have := h1 k (by show k < fw engF p.1; omega)
      simpa [SO, Rb.SO, bout_eq, hfw] using this)
  have hpg : ∀ g, resRule p.1 = .pubG g → fw engF p.1 = p.2 → (∀ k < p.2, Rx.PL.off g + k < 1531) →
      bytesOf pub (BOUT + engF.off p.1) p.2 = beN p.2 (valG pub g p.2) := by
    intro g hr hfw hlt
    have h1 := eqLE_sem H SO p.1 (Rx.PL.off g) (fun e he => mf (by rw [hr]; exact he))
    exact bytesOf_le pub _ p.2 _ (fun k hk => hb _ (hlt k hk)) (fun k hk => by
      have := h1 k (by show k < fw engF p.1; omega)
      simpa [SO, Rb.SO, bout_eq, hfw] using this)
  simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · exact (hnum 1 rfl rfl).symm
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · show beN 8 (B.receiptIdx + 1) = _
    rw [bytesOf_le pub _ 8 (fun k => pv pub (BOUT + engF.off "receiptIdx" + (7 - k)))
      (fun k hk => hb _ (by have : BOUT + engF.off "receiptIdx" + 7 < 1531 := (by decide); omega))
      (fun k _ => rfl), hinc]
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · rw [hnum 0 rfl rfl]; rfl
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · rfl
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · exact (hpg "gout" rfl rfl (fun k hk => by have : Rx.PL.off "gout" + 8 ≤ 1531 := (by decide); omega)).symm
  · exact (hpg "gout" rfl rfl (fun k hk => by have : Rx.PL.off "gout" + 8 ≤ 1531 := (by decide); omega)).symm
  · exact (hpg "tbout" rfl rfl (fun k hk => by have : Rx.PL.off "tbout" + 16 ≤ 1531 := (by decide); omega)).symm
  · exact (hpg "cout" rfl rfl (fun k hk => by have : Rx.PL.off "cout" + 8 ≤ 1531 := (by decide); omega)).symm
  · exact (hnum 0 rfl rfl).symm
  · exact (hnum 0 rfl rfl).symm
  · exact (hnum 0 rfl rfl).symm
  · rfl
  · have h1 := hin ("outRcptN", 8) (by decide)
    have e : recVal B "outRcptN" = beN 8 1 := by simp [recVal, ho]
    show beN 8 1 = _
    rw [← e, h1]; exact hcopy rfl rfl
  · rfl
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · exact (hin _ (by decide)).trans (hcopy rfl rfl)
  · show bdigest [] = _
    have h2 := dig_sem' H SO "vmAcc" (fun e he => mf he)
    rw [emptyDig_eq]
    exact (bytesOf_dig pub (BOUT + engF.off "vmAcc") emptyDig (fun j hj => by
      have := h2 j (by simpa [emptyDig] using hj); simpa [SO, Rb.SO, bout_eq] using this)).symm
  · rw [hnum 0 rfl rfl]; rfl
end

end M5T1.RbSem
