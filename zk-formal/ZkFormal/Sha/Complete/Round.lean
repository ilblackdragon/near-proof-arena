import ZkFormal.Sha.Complete.Digest

/-! # Completeness: `cRound` (four rounds per round row) -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table
open ZkFormal.Sha.Spec

theorem K_w32 : W32 ArenaCore.SHA256.K := by
  intro x hx
  simp only [ArenaCore.SHA256.K, List.mem_cons, List.mem_nil_iff, or_false] at hx
  repeat (rcases hx with rfl | hx; · decide)

theorem Kt_lt (t : Nat) : Kt t < 2 ^ 32 := getD_lt K_w32 t

/-- The window of a round row: eight `a`s and `e`s, slots `0..3` on the
current row and `4..7` on the next row. -/
def Window (Z : ZEnv) (B : Blk) (j : Nat) : Prop :=
  ∀ u, u < 8 → Holds32 Z (winA u) (B.A (4 * j + u)) ∧ Holds32 Z (winE u) (B.Ee (4 * j + u))

/-- A `gRound`-gated row pair: the next row is `Rj` of a block and the window holds. -/
theorem round_ctx (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat → Int) (x : Int)
    (h : ∀ M b j, MOk M → b < nb M → j < 16 → nx = .round j (blkOf M b) →
      Window (renv cur nx f lst p) (blkOf M b) j → x = 0) :
    zev (renv cur nx f lst p) gRound * x = 0 := by
  rw [zev_gRound]
  -- next-row half of the window, for any next round row
  have hnext : ∀ (j : Nat) (B : Blk) (cur' : Row), ∀ u, 4 ≤ u → u < 8 →
      Holds32 (renv cur' (.round j B) f lst p) (winA u) (B.A (4 * j + u)) ∧
      Holds32 (renv cur' (.round j B) f lst p) (winE u) (B.Ee (4 * j + u)) := by
    intro j B cur' u hu1 hu2
    constructor
    · intro b hb
      simp only [winA, if_neg (show ¬ u < 4 by omega)]
      exact zev_bit_n _ (by
        rw [renv_nxt, rowCell_round, rc_A j B (u - 4) b (by omega) hb,
          show 4 * j + 4 + (u - 4) = 4 * j + u by omega])
    · intro b hb
      simp only [winE, if_neg (show ¬ u < 4 by omega)]
      exact zev_bit_n _ (by
        rw [renv_nxt, rowCell_round, rc_E j B (u - 4) b (by omega) hb,
          show 4 * j + 4 + (u - 4) = 4 * j + u by omega])
  cases hs with
  | start M hM =>
    rw [h M 0 0 hM (nb_pos M) (by decide) rfl ?_, Int.mul_zero]
    intro u hu
    by_cases hu4 : u < 4
    · constructor
      · intro b hb
        simp only [winA, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_start, sc_A _ u b hu4 hb, Nat.mul_zero, Nat.zero_add,
            A_init _ u hu4, hin_zero]; rfl)
      · intro b hb
        simp only [winE, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_start, sc_E _ u b hu4 hb, Nat.mul_zero, Nat.zero_add,
            E_init _ u hu4, hin_zero]; rfl)
    · exact hnext 0 _ _ u (by omega) hu
  | round M b j hM hb hj =>
    rw [h M b (j + 1) hM hb (by omega) rfl ?_, Int.mul_zero]
    intro u hu
    by_cases hu4 : u < 4
    · constructor
      · intro b' hb'
        simp only [winA, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_round, rc_A j _ u b' hu4 hb', show 4 * j + 4 + u = 4 * (j + 1) + u by omega])
      · intro b' hb'
        simp only [winE, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_round, rc_E j _ u b' hu4 hb', show 4 * j + 4 + u = 4 * (j + 1) + u by omega])
    · exact hnext _ _ _ u (by omega) hu
  | dnext M b hM hb =>
    rw [h M (b + 1) 0 hM hb (by decide) rfl ?_, Int.mul_zero]
    intro u hu
    by_cases hu4 : u < 4
    · constructor
      · intro b' hb'
        simp only [winA, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_digest, dc_A _ u b' hu4 hb', Nat.mul_zero, Nat.zero_add,
            A_init _ u hu4, hin_succ_getD M b (by omega) _ (by omega)])
      · intro b' hb'
        simp only [winE, if_pos hu4]
        exact zev_bit_c _ (by
          rw [renv_cur, rowCell_digest, dc_E _ u b' hu4 hb', Nat.mul_zero, Nat.zero_add,
            E_init _ u hu4, hin_succ_getD M b (by omega) _ (by omega)])
    · exact hnext 0 _ _ u (by omega) hu
  | r15 M b hM hb => simp [gateV]
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, Int.zero_mul]
  | pad _ hX => rw [gateV_ps _ hX, Int.zero_mul]

theorem sum_ite_mul (c : Nat → Int) (j' : Nat) :
    ∀ n, j' < n → ((List.range n).map fun j => ((if j = j' then 1 else 0 : Nat) : Int) * c j).sum = c j'
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hn : n = j'
    · subst hn
      have : ((List.range n).map fun j => ((if j = n then 1 else 0 : Nat) : Int) * c j).sum = 0 := by
        have e : ((List.range n).map fun j => ((if j = n then 1 else 0 : Nat) : Int) * c j) =
            (List.range n).map fun _ => ((0 : Nat) : Int) := by
          apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
          rw [if_neg (by omega)]; simp
        rw [e, sum_zero_map]
      simp [this]
    · rw [sum_ite_mul c j' n (by omega)]
      simp [hn]

theorem zev_kLimb (M : Msg) (b j : Nat) (hj : j < 16) (cur : Row) (f lst : Int) (p : Nat → Int)
    (i l : Nat) (hl : l < 2) :
    zev (renv cur (.round j (blkOf M b)) f lst p) (kLimb i l) = (limbN (Kt (4 * j + i)) l : Int) := by
  unfold kLimb
  rw [zev_sum, List.map_map]
  have e : ((List.range 16).map ((zev (renv cur (.round j (blkOf M b)) f lst p)) ∘ fun j' =>
      Expr.mul (E.n (colR j'))
        (E.k ((ArenaCore.SHA256.K.getD (4 * j' + i) 0 / 2 ^ (16 * l)) % 2 ^ 16)))) =
      (List.range 16).map fun j' => ((if j' = j then 1 else 0 : Nat) : Int) *
        (((ArenaCore.SHA256.K.getD (4 * j' + i) 0 / 2 ^ (16 * l)) % 2 ^ 16 : Nat) : Int) := by
    apply List.map_congr_left
    intro j' hj'
    rw [List.mem_range] at hj'
    simp only [Function.comp, zev_mul, zev_n, renv_nxt, zev_k, cell_R _ j' hj', kR]
  rw [e, sum_ite_mul _ j 16 hj, limbN_eq _ l (Kt_lt _) hl]
  rfl

/-- `a + b` limb relation for a sum of words: the round constraints' arithmetic. -/
theorem addC_limbs (xs : List Nat) (l : Nat) (hl : l < 2)
    (cin : Int) (hcin : cin = if l = 0 then 0 else (carry xs 0 : Int)) :
    ((xs.map fun x => (limbN x l : Int)).sum + cin -
      ((limbN (xs.sum % 2 ^ 32) l : Int) + 65536 * (carry xs l : Int))) = 0 := by
  have hsp := carry_spec xs
  simp only at hsp
  have e : ∀ (g : Nat → Nat) (ys : List Nat), (ys.map fun x => (g x : Int)).sum = ((ys.map g).sum : Int) := by
    intro g ys; induction ys with
    | nil => rfl
    | cons y ys ih => simp [ih]
  rw [e (fun x => limbN x l)]
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · simp only [if_true] at hcin; subst hcin
    have : (xs.map fun x => limbN x 0) = xs.map lo16 := rfl
    rw [this, limbN_zero]; omega
  · simp only [Nat.one_ne_zero, if_false] at hcin; subst hcin
    have : (xs.map fun x => limbN x 1) = xs.map hi16 := rfl
    rw [this, limbN_one]; omega

section
variable (M : Msg) (b : Nat)

theorem termsA_lt (hM : MOk M) (hb : b < nb M) (t : Nat) : ∀ x ∈ (blkOf M b).termsA t, x < 2 ^ 32 := by
  intro x hx
  simp only [Blk.termsA, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E_lt M b _
  · exact bsig1_lt _
  · exact ch_lt _ _ _ (E_lt M b _) (E_lt M b _)
  · exact Kt_lt _
  · exact W_lt M b hM hb _
  · exact bsig0_lt _
  · exact maj_lt _ _ _ (A_lt M b _) (A_lt M b _)

theorem termsE_lt (hM : MOk M) (hb : b < nb M) (t : Nat) : ∀ x ∈ (blkOf M b).termsE t, x < 2 ^ 32 := by
  intro x hx
  simp only [Blk.termsE, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact A_lt M b _
  · exact E_lt M b _
  · exact bsig1_lt _
  · exact ch_lt _ _ _ (E_lt M b _) (E_lt M b _)
  · exact Kt_lt _
  · exact W_lt M b hM hb _

theorem A_succ4 (t : Nat) : (blkOf M b).A (t + 4) = ((blkOf M b).termsA t).sum % 2 ^ 32 := by
  unfold Blk.A Blk.termsA Blk.A Blk.Ee Blk.W
  rw [As_succ4]
  simp only [List.sum_cons, List.sum_nil]
  omega

theorem E_succ4 (t : Nat) : (blkOf M b).Ee (t + 4) = ((blkOf M b).termsE t).sum % 2 ^ 32 := by
  unfold Blk.Ee Blk.termsE Blk.A Blk.Ee Blk.W
  rw [Es_succ4]
  simp only [List.sum_cons, List.sum_nil]
  omega
end

theorem window_at (Z : ZEnv) (B : Blk) (j : Nat) (hW : Window Z B j) (i k : Nat) (hk : i + k < 8) :
    Holds32 Z (winA (i + k)) (B.A (4 * j + i + k)) ∧ Holds32 Z (winE (i + k)) (B.Ee (4 * j + i + k)) := by
  have := hW (i + k) hk
  rw [← Nat.add_assoc] at this
  exact this

theorem complete_cRound : CompleteFamStmt cRound := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  rw [henv_eq]
  have hs := step_at msgs hok t r hr
  generalize rowAt msgs r = cur at hs ⊢
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hs ⊢
  generalize (if r = 0 then 1 else 0 : Int) = f
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p
  simp only [cRound, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at he
  obtain ⟨i, hi, l, hl, he⟩ := he
  rcases he with rfl | rfl
  · unfold roundA; rw [zev_addC]
    apply round_ctx cur nx hs
    intro M b j hM hb hj hn hW
    subst hn
    have w0 := window_at _ _ j hW i 0 (by omega)
    have w1 := window_at _ _ j hW i 1 (by omega)
    have w2 := window_at _ _ j hW i 2 (by omega)
    have w3 := window_at _ _ j hW i 3 (by omega)
    simp only [Nat.add_zero] at w0
    have hres : Holds32 (renv cur (.round j (blkOf M b)) f lst p) (fun b => E.n (colA i b))
        ((blkOf M b).A (4 * j + i + 4)) := fun b' hb' => zev_bit_n _ (by
      rw [renv_nxt, rowCell_round, rc_A j _ i b' hi hb', show 4 * j + 4 + i = 4 * j + i + 4 by omega])
    have hcar : ∀ l', l' < 2 → zev (renv cur (.round j (blkOf M b)) f lst p) (carryN (colCA i) l') =
        (carry ((blkOf M b).termsA (4 * j + i)) l' : Int) := fun l' hl' =>
      zev_carryN _ _ _ _ (carry_lt _ (termsA_lt M b hM hb _) (by simp [Blk.termsA]) l') (fun k hk => by
        rw [renv_nxt, rowCell_round, rc_CA j _ i l' k hi hl' hk])
    simp only [List.map_cons, List.map_nil]
    rw [limb_word _ _ _ l (E_lt M b _) hl w0.2,
      limb_bsig1 _ _ _ l (E_lt M b _) hl w3.2,
      limb_ch _ _ _ _ _ _ _ l (E_lt M b _) (E_lt M b _) hl w3.2 w2.2 w1.2,
      zev_kLimb M b j hj cur f lst p i l hl,
      limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_nW f lst p cur _ j _ rfl i hi),
      limb_bsig0 _ _ _ l (A_lt M b _) hl w3.1,
      limb_maj _ _ _ _ _ _ _ l (A_lt M b _) (A_lt M b _) hl w3.1 w2.1 w1.1,
      limb_word _ _ _ l (A_lt M b _) hl hres, hcar l hl, A_succ4]
    have key := addC_limbs ((blkOf M b).termsA (4 * j + i)) l hl
      (zev (renv cur (.round j (blkOf M b)) f lst p) (if l = 0 then E.k 0 else carryN (colCA i) 0))
      (by split
          · rfl
          · rw [hcar 0 (by decide)])
    simp only [Blk.termsA, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at key ⊢
    omega
  · unfold roundE; rw [zev_addC]
    apply round_ctx cur nx hs
    intro M b j hM hb hj hn hW
    subst hn
    have w0 := window_at _ _ j hW i 0 (by omega)
    have w1 := window_at _ _ j hW i 1 (by omega)
    have w2 := window_at _ _ j hW i 2 (by omega)
    have w3 := window_at _ _ j hW i 3 (by omega)
    simp only [Nat.add_zero] at w0
    have hres : Holds32 (renv cur (.round j (blkOf M b)) f lst p) (fun b => E.n (colE i b))
        ((blkOf M b).Ee (4 * j + i + 4)) := fun b' hb' => zev_bit_n _ (by
      rw [renv_nxt, rowCell_round, rc_E j _ i b' hi hb', show 4 * j + 4 + i = 4 * j + i + 4 by omega])
    have hcar : ∀ l', l' < 2 → zev (renv cur (.round j (blkOf M b)) f lst p) (carryN (colCE i) l') =
        (carry ((blkOf M b).termsE (4 * j + i)) l' : Int) := fun l' hl' =>
      zev_carryN _ _ _ _ (carry_lt _ (termsE_lt M b hM hb _) (by simp [Blk.termsE]) l') (fun k hk => by
        rw [renv_nxt, rowCell_round, rc_CE j _ i l' k hi hl' hk])
    simp only [List.map_cons, List.map_nil]
    rw [limb_word _ _ _ l (A_lt M b _) hl w0.1,
      limb_word _ _ _ l (E_lt M b _) hl w0.2,
      limb_bsig1 _ _ _ l (E_lt M b _) hl w3.2,
      limb_ch _ _ _ _ _ _ _ l (E_lt M b _) (E_lt M b _) hl w3.2 w2.2 w1.2,
      zev_kLimb M b j hj cur f lst p i l hl,
      limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_nW f lst p cur _ j _ rfl i hi),
      limb_word _ _ _ l (E_lt M b _) hl hres, hcar l hl, E_succ4]
    have key := addC_limbs ((blkOf M b).termsE (4 * j + i)) l hl
      (zev (renv cur (.round j (blkOf M b)) f lst p) (if l = 0 then E.k 0 else carryN (colCE i) 0))
      (by split
          · rfl
          · rw [hcar 0 (by decide)])
    simp only [Blk.termsE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at key ⊢
    omega

end ZkFormal.Sha.Complete
