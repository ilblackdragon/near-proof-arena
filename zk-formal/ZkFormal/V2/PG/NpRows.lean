import ZkFormal.V2.PG.NpPrep

/-!
# ZkFormal.V2.PG.NpRows (P2 copy of `Prover.NpRows` at `dp = pg g`) — the honest columns on the trace domain

* `mainV_row`: the main column polynomials take the trace values at `ω^r`;
* `evalWith_row`: on the trace domain the polynomial environment evaluates every
  expression reading only columns `< width` to the (embedded) trace value;
* `allConstraints_row`: the AIR's constraints (and booleanity) vanish there (`Holds`).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-! ## Facts from `headerOk` -/

section
variable (A : Air) (tr : Trace Fp)

structure TabOk (t : Nat) : Prop where
  lt : t < A.tables.length
  log1 : 1 ≤ tr.log t
  log22 : tr.log t ≤ 22
  wf : Air.Table.wf A (2 ^ dp.logBlowup) (tb A t) = true
  deg : (tb A t).degree dp.auxGroup ≤ 2 ^ dp.logBlowup

theorem tabOk (hok : headerOk A dp (hdr A tr) = true) {t : Nat} (ht : t < A.tables.length) :
    TabOk A tr t := by
  obtain ⟨hlen, hall, hwf, hdeg⟩ := headerOk_facts hok
  have hl := hall t ht (by rw [hdr_length]; exact ht)
  have e : (hdr A tr)[t]'(by rw [hdr_length]; exact ht) = tr.log t := by simp [hdr, trHdr]
  rw [e] at hl
  have hmem : A.tables[t] ∈ A.tables := List.getElem_mem ht
  refine ⟨ht, hl.1, ?_, ?_, ?_⟩
  · have : tr.log t + 4 ≤ 26 := hl.2.2
    omega
  · rw [tb_eq A ht]; exact (wf_facts hwf).1 _ hmem
  · rw [tb_eq A ht]; exact hdeg _ hmem

theorem colBound_of_wf {t : Nat} (h : Air.Table.wf A (2 ^ dp.logBlowup) (tb A t) = true) :
    ∀ e ∈ (tb A t).exprs, e.colBound ≤ (tb A t).width := by
  simp only [Table.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun e he => (h.1.1.1.1 e he).1

theorem colBound_allConstraints {t : Nat} (h : Air.Table.wf A (2 ^ dp.logBlowup) (tb A t) = true) :
    ∀ e ∈ (tb A t).allConstraints, e.colBound ≤ (tb A t).width := by
  have hc := colBound_of_wf A h
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hc e (List.mem_append_left _ he)
  · simp only [Table.bitConstraints, List.mem_flatMap, List.mem_map] at he
    obtain ⟨i, hi, b, hb, rfl⟩ := he
    have := hc b (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_append_left _ hb⟩))
    simp only [Expr.colBound]; omega

end

/-! ## Main columns on the trace domain -/

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem mainC_spec (t c : Nat) (hlog : tr.log t ≤ 27) :
    ∀ r, r < 2 ^ lg tr t → ev (2 ^ lg tr t) (mainC tr t c) (Fp.twoAdicGen (lg tr t) ^ r) = tr.cell t r c := by
  unfold mainC
  exact pick_spec <| exists_interp (pts := fun r => Fp.twoAdicGen (lg tr t) ^ r)
    (fun _ _ hi hj h => Fp.twoAdicGen_pow_inj hlog hi hj h) _

theorem omg_pow (log r : Nat) : omg log ^ r = Fp8.ofBase (Fp.twoAdicGen log ^ r) := by
  unfold omg; rw [ofBase_pow]

theorem mainV_row (t : Nat) (hlog : tr.log t ≤ 27) {r : Nat} (hr : r < 2 ^ lg tr t) :
    mainV A tr t (omg (lg tr t) ^ r) =
      (List.range (tb A t).width).map fun c => Fp8.ofBase (tr.cell t r c) := by
  unfold mainV
  apply List.map_congr_left
  intro c _
  rw [omg_pow, ← ofBase_ev, mainC_spec tr t c hlog r hr]

theorem omg_mul_pow (t : Nat) (hlog : tr.log t ≤ 27) (r : Nat) :
    omg (lg tr t) * omg (lg tr t) ^ r = omg (lg tr t) ^ ((r + 1) % 2 ^ lg tr t) := by
  rw [← npOmg_pow_mod hlog, Semiring.pow_succ]; grind

/-- On the trace domain, expressions reading columns `< width` evaluate to the trace values. -/
theorem evalWith_row (t : Nat) (hlog : tr.log t ≤ 27) {r : Nat} (hr : r < 2 ^ lg tr t) :
    ∀ e : Expr, e.colBound ≤ (tb A t).width →
      e.evalWith (pEnv A cb tr t (omg (lg tr t) ^ r)) = Fp8.ofBase (e.eval tr t r (pubOf Fp cb))
  | .const c, _ => rfl
  | .pub i, _ => rfl
  | .col c nx, hc => by
    simp only [Expr.colBound] at hc
    show (mainV A tr t (if nx then omg (lg tr t) * omg (lg tr t) ^ r else omg (lg tr t) ^ r)).getD c 0 =
      Fp8.ofBase (tr.cell t (if nx then (r + 1) % 2 ^ tr.log t else r) c)
    cases nx
    · simp only [Bool.false_eq_true, if_false]
      rw [mainV_row A tr t hlog hr, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega)]
      rfl
    · simp only [if_true]
      rw [omg_mul_pow tr t hlog, mainV_row A tr t hlog (Nat.mod_lt _ (Nat.two_pow_pos _)),
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
  | .isFirst, _ => by
    show selSum (2 ^ lg tr t) (omg (lg tr t) ^ r) = Fp8.ofBase (if r = 0 then 1 else 0)
    rw [npSelSum_omg hlog hr]; split <;> rfl
  | .isLast, _ => by
    show selSum (2 ^ lg tr t) (omg (lg tr t) * omg (lg tr t) ^ r) =
      Fp8.ofBase (if r + 1 = 2 ^ tr.log t then 1 else 0)
    rw [npSelSum_omg_next hlog hr]; split <;> rfl
  | .isTransition, _ => by
    show 1 - selSum (2 ^ lg tr t) (omg (lg tr t) * omg (lg tr t) ^ r) =
      Fp8.ofBase (if r + 1 = 2 ^ tr.log t then 0 else 1)
    rw [npSelSum_omg_next hlog hr]
    split
    · show (1 : Fp8) - 1 = 0; grind
    · show (1 : Fp8) - 0 = 1; grind
  | .add a b, hc => by
    simp only [Expr.colBound] at hc
    show a.evalWith _ + b.evalWith _ = Fp8.ofBase (a.eval _ t r _ + b.eval _ t r _)
    rw [evalWith_row t hlog hr a (by omega), evalWith_row t hlog hr b (by omega), Fp8.ofBase_add]
  | .mul a b, hc => by
    simp only [Expr.colBound] at hc
    show a.evalWith _ * b.evalWith _ = Fp8.ofBase (a.eval _ t r _ * b.eval _ t r _)
    rw [evalWith_row t hlog hr a (by omega), evalWith_row t hlog hr b (by omega), Fp8.ofBase_mul]
  | .neg a, hc => by
    simp only [Expr.colBound] at hc
    show - a.evalWith _ = Fp8.ofBase (- a.eval _ t r _)
    rw [evalWith_row t hlog hr a hc, Fp8.ofBase_neg]

/-- The AIR constraints and booleanity vanish on the trace domain. -/
theorem allConstraints_row (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t)
    {r : Nat} (hr : r < 2 ^ lg tr t) :
    ∀ e ∈ (tb A t).allConstraints, e.evalWith (pEnv A cb tr t (omg (lg tr t) ^ r)) = 0 := by
  intro e he
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  rw [evalWith_row A cb tr t hlog hr e (colBound_allConstraints A ht.wf e he)]
  have hT := tb_eq A ht.lt
  rcases List.mem_append.mp he with he | he
  · rw [hH.constr t ht.lt r hr e (by rw [← hT]; exact he)]; rfl
  · simp only [Table.bitConstraints, List.mem_flatMap, List.mem_map] at he
    obtain ⟨i, hi, b, hb, rfl⟩ := he
    have hb01 := hH.bits t ht.lt r hr i (by rw [← hT]; exact hi) b hb
    show Fp8.ofBase (b.eval tr t r (pubOf Fp cb) * (b.eval tr t r (pubOf Fp cb) +
      - @Nat.cast Fp Semiring.natCast 1)) = 0
    rcases hb01 with h | h <;> rw [h] <;> decide +kernel

end

end ZkFormal.Prover.Np.G
