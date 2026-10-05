import ZkFormal.Near.Render.Proof.RcptGasB

/-!
# ZkFormal.Near.Render.Proof.RcptDepF — the `DEP` arithmetic of the generator

Under `DepOk d` (numeric facts of a receipt's balance data: `aft = bef + dep <
u128::MAX`, `tot = aft + locked < 2^128`, `storage < 2^64`, the stake check,
`tprev ≤ r < 512`):

* `aft`, `tot`, `q = 10^19·storage` byte by byte (`sa_*`, `stt_*`, `sq_*`), no final carry;
* `tot − q` with borrow, no final borrow when `big`;
* `Σ (255 − aft_j) ≠ 0`.

`depOk`: the receipt data of a `Good` batch satisfies `DepOk`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen

/-- Numeric facts of a receipt's balance data. -/
structure DepOk (d : RD) : Prop where
  aft_lt : d.bef + d.dep + 1 < 256 ^ 16
  tot_lt : d.bef + d.dep + d.locked < 256 ^ 16
  stor_lt : d.stor < 256 ^ 8
  big : d.big = decide (10000000000000000000 * d.stor ≤ d.bef + d.dep + d.locked)
  stake : d.big = false → d.stor ≤ 770
  tprev_le : d.tprev ≤ d.r
  r_lt : d.r < 512

theorem S_LE_val : (Rcpt.S_LE.length = 8) := rfl

theorem V_convS (v : Nat → Nat) (n : Nat) : V (conv Rcpt.S_LE v) n =
    232 * 65536 * V v (n - 2) + 137 * 16777216 * V v (n - 3) + 4 * 4294967296 * V v (n - 4) +
      35 * 1099511627776 * V v (n - 5) + 199 * 281474976710656 * V v (n - 6) +
      138 * 72057594037927936 * V v (n - 7) := by
  rw [V_conv]; simp [sumR, Rcpt.S_LE]

theorem convS_le (v : Nat → Nat) (hv : ∀ i, v i ≤ 255) (i : Nat) : conv Rcpt.S_LE v i ≤ 189975 :=
  Nat.le_trans (conv_le _ v hv i) (by simp [sumR, Rcpt.S_LE])

theorem V_const255 : ∀ n, V (fun _ => 255) n + 1 = 256 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [V, Nat.pow_succ]
    have := V_const255 n
    have : 255 * 256 ^ n + 256 ^ n = 256 ^ n * 256 := by rw [Nat.mul_comm (256 ^ n) 256]; omega
    omega

section
variable {d : RD} (h : DepOk d)
include h

theorem stor_hi {i : Nat} (hi : 8 ≤ i) : Seg.stB d i = 0 := by
  simp only [Seg.stB, leBytes_getD, show ¬ i < 8 by omega, ↓reduceIte]

theorem V_stB {k : Nat} (hk : 8 ≤ k) : V (Seg.stB d) k = d.stor := V_leBytes_of hk h.stor_lt

/-! ## `aft = bef + dep` -/

theorem V_y1 : V (Seg.y1 d) 16 = d.bef + d.dep := by
  rw [show Seg.y1 d = fun i => Seg.befB d i + Seg.depB d i from rfl, V_add]
  have e1 : V (Seg.befB d) 16 = d.bef := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  have e2 : V (Seg.depB d) 16 = d.dep := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  rw [e1, e2]

theorem sa_mod {i : Nat} (hi : i < 16) : Seg.sa d i % 256 = Seg.aftB d i := chain_byte _ hi (V_y1 h)

theorem y1_le (i : Nat) : Seg.y1 d i ≤ 510 := by
  simp only [Seg.y1, Seg.befB, Seg.depB]
  have := leBytes_getD_lt 16 d.bef i; have := leBytes_getD_lt 16 d.dep i; omega

theorem c1d_le (i : Nat) : chain (Seg.y1 d) i ≤ 1 := chain_le _ (fun j => by have := y1_le h j; omega) i
theorem sa_div (i : Nat) : Seg.sa d i / 256 = chain (Seg.y1 d) (i + 1) := by simp only [Seg.sa, chain]
theorem c1d_final : chain (Seg.y1 d) 16 = 0 := chain_zero_of _ (by rw [V_y1 h]; have := h.aft_lt; omega)

/-! ## `tot = aft + locked` -/

theorem V_y2 : V (Seg.y2 d) 16 = d.bef + d.dep + d.locked := by
  rw [show Seg.y2 d = fun i => Seg.aftB d i + Seg.lkB d i from rfl, V_add]
  have e1 : V (Seg.aftB d) 16 = d.bef + d.dep := V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)
  have e2 : V (Seg.lkB d) 16 = d.locked := V_leBytes_of (Nat.le_refl _) (by have := h.tot_lt; omega)
  rw [e1, e2]

theorem stt_mod {i : Nat} (hi : i < 16) : Seg.stt d i % 256 = Seg.totB d i := chain_byte _ hi (V_y2 h)

theorem y2_le (i : Nat) : Seg.y2 d i ≤ 510 := by
  simp only [Seg.y2, Seg.aftB, Seg.lkB]
  have := leBytes_getD_lt 16 (d.bef + d.dep) i; have := leBytes_getD_lt 16 d.locked i; omega

theorem c2d_le (i : Nat) : chain (Seg.y2 d) i ≤ 1 := chain_le _ (fun j => by have := y2_le h j; omega) i
theorem stt_div (i : Nat) : Seg.stt d i / 256 = chain (Seg.y2 d) (i + 1) := by simp only [Seg.stt, chain]
theorem c2d_final : chain (Seg.y2 d) 16 = 0 := chain_zero_of _ (by rw [V_y2 h]; exact h.tot_lt)

/-! ## `q = 10^19 · storage` -/

theorem q_lt : 10000000000000000000 * d.stor < 256 ^ 16 := by
  have := h.stor_lt
  have e8 : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  have e16 : (256 : Nat) ^ 16 = 340282366920938463463374607431768211456 := by decide
  omega

theorem V_y3 : V (Seg.y3 d) 16 = 10000000000000000000 * d.stor := by
  simp only [Seg.y3]
  rw [V_convS, V_stB h (by omega), V_stB h (by omega), V_stB h (by omega), V_stB h (by omega), V_stB h (by omega),
    V_stB h (by omega)]
  omega

theorem sq_mod {i : Nat} (hi : i < 16) : Seg.sq d i % 256 = Seg.qB d i := chain_byte _ hi (V_y3 h)

theorem y3_le (i : Nat) : Seg.y3 d i ≤ 189975 :=
  convS_le _ (fun i => Nat.le_of_lt_succ (leBytes_getD_lt 8 d.stor i)) i

theorem c3d_le (i : Nat) : chain (Seg.y3 d) i ≤ 745 := chain_le _ (fun j => by have := y3_le h j; omega) i
theorem sq_div (i : Nat) : Seg.sq d i / 256 = chain (Seg.y3 d) (i + 1) := by simp only [Seg.sq, chain]
theorem c3d_final : chain (Seg.y3 d) 16 = 0 := chain_zero_of _ (by rw [V_y3 h]; exact q_lt h)

/-! ## `tot − q` -/

theorem totB_lt (i : Nat) : Seg.totB d i < 256 := leBytes_getD_lt _ _ _
theorem qB_lt (i : Nat) : Seg.qB d i < 256 := leBytes_getD_lt _ _ _
theorem dbr_le (i : Nat) : Seg.dbr d i ≤ 1 := bchain_le _ _ _ i (by decide)
theorem ddv_lt (i : Nat) : Seg.ddv d i < 256 := bdig_lt _ _ _ (totB_lt h) (qB_lt h) (by decide) i
theorem ddv_step (i : Nat) : Seg.totB d i + 256 * Seg.dbr d (i + 1) = Seg.qB d i + Seg.dbr d i + Seg.ddv d i :=
  (bdig_step _ _ _ (totB_lt h) (qB_lt h) (by decide) i).1
theorem dbr_zero : Seg.dbr d 0 = 0 := rfl

theorem dbr_final (hb : d.big = true) : Seg.dbr d 16 = 0 := by
  have := bchain_final (Seg.totB d) (Seg.qB d) 0 (totB_lt h) (qB_lt h) (by decide) 16
  have e1 : V (Seg.totB d) 16 = d.bef + d.dep + d.locked := V_leBytes_of (Nat.le_refl _) h.tot_lt
  have e2 : V (Seg.qB d) 16 = 10000000000000000000 * d.stor := V_leBytes_of (Nat.le_refl _) (q_lt h)
  rw [e1, e2] at this
  have hb' := h.big; rw [hb] at hb'
  simp only [true_eq_decide_iff] at hb'
  simp only [Seg.dbr, this]; rw [if_neg (by omega)]

/-! ## `aft ≠ u128::MAX` -/

theorem runA_succ (i : Nat) : Seg.runA d (i + 1) = Seg.runA d i + (255 - Seg.aftB d (i + 1)) := runSum_succ _ _
theorem runA_zero : Seg.runA d 0 = 255 - Seg.aftB d 0 := runSum_zero _

theorem runA_ne : Seg.runA d 15 ≠ 0 := by
  intro h0
  have hz := runSum_eq0 _ 15 h0
  have h255 : ∀ j, j < 16 → Seg.aftB d j = 255 := by
    intro j hj; have := hz j (by omega); have := leBytes_getD_lt 16 (d.bef + d.dep) j
    simp only [Seg.aftB] at *; omega
  have hV := V_congr (x := Seg.aftB d) (y := fun _ => 255) 16 h255
  rw [show Seg.aftB d = fun i => (leBytes 16 (d.bef + d.dep)).getD i 0 from rfl,
    V_leBytes_of (Nat.le_refl _) (by have := h.aft_lt; omega)] at hV
  have := V_const255 16
  have := h.aft_lt
  omega

theorem runA_lt (i : Nat) (hi : i < 16) : Seg.runA d i < 4096 := by
  have := runSum_le (fun j => 255 - Seg.aftB d j) 255 (fun j => by omega) i
  have : (i + 1) * 255 ≤ 16 * 255 := Nat.mul_le_mul_right _ (by omega)
  simp only [Seg.runA]; omega

/-! ## Storage without `big` -/

theorem stor_small (hb : d.big = false) : Seg.stB d 0 + 256 * Seg.stB d 1 = d.stor := by
  have := h.stake hb
  have h2 := V_leBytes 8 d.stor 2
  simp only [V, Nat.min_eq_left (show 2 ≤ 8 by decide)] at h2
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  simp only [Seg.stB]; omega

theorem stB_small (hb : d.big = false) {i : Nat} (hi : 2 ≤ i) : Seg.stB d i = 0 := by
  have := h.stake hb
  simp only [Seg.stB, leBytes_getD]
  split
  · have : 256 ^ 2 ≤ 256 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.div_eq_of_lt (by omega)]
  · rfl

end

/-! ## The receipt data of a `Good` batch -/

theorem u128Max_eq : Params.u128Max + 1 = 256 ^ 16 := by decide

theorem acc0_stor (e : Ext) (k : Nat) : (e.acc0 k).storageUsage < 256 ^ 8 := by
  unfold Ext.acc0 Account.decode
  by_cases hl : (e.vals0 k).length = 72
  · by_cases h1 : leNat (List.take 16 (e.vals0 k)) = Params.u128Max
    · simp [hl, h1]
    · simp only [hl, h1, ↓reduceIte, Option.getD_some]
      have := leNat_lt' ((e.vals0 k).drop 64)
      simp only [List.length_drop, hl] at this
      exact this
  · simp [hl]
where
  leNat_lt' : ∀ (l : Bytes), leNat l < 256 ^ l.length
    | [] => by simp [leNat]
    | b :: bs => by
      have := leNat_lt' bs; have := b.toNat_lt
      simp only [leNat, List.length_cons, Nat.pow_succ]
      omega

theorem tprevOf_le (e : Ext) (r : Nat) : tprevOf e r ≤ r := by
  unfold tprevOf
  cases h : ((List.range r).filter fun r' => e.slot r' = e.slot r).getLast? with
  | none => simp
  | some x =>
    have hm := List.mem_of_getLast? h
    simp only [List.mem_filter, List.mem_range] at hm
    simp only [Option.map_some, Option.getD_some]; omega

theorem depOk {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e) : DepOk (Df c e r) := by
  have ok := hg.rcpt_ok r hr
  have a1 := ok.amt_lt; have a2 := ok.tot_lt; have a3 := ok.stake
  rw [two128_eq] at a2
  have hu := u128Max_eq
  have hN := hg.n_le; have hl := hg.len
  simp only [Params.maxBatch, NN] at hN hr
  rw [Df_eq hr]
  refine ⟨by simp only [rdOf, mkInfo_e]; omega, by simp only [rdOf, mkInfo_e]; omega, acc0_stor e _, rfl, ?_,
    tprevOf_le e r, by simp only [rdOf]; omega⟩
  intro hb
  simp only [rdOf, mkInfo_e, decide_eq_false_iff_not] at hb ⊢
  simp only [Params.storageAmountPerByte, Params.zeroBalanceStorageLimit] at a3
  have hb' := of_decide_eq_false hb
  omega

end RcptP

end ZkFormal.Near.Render
