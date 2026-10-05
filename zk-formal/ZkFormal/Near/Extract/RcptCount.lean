import ZkFormal.Near.Extract.RcptWfEasy

/-!
# ZkFormal.Near.Extract.RcptCount — the batch's last row: receipt count, refund count

On the last receipt's last row `lastR = 1`, so `r + 1 = n`, `rcnt + hr = nref`
(public, little endian) and the tokens register holds the public total.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem leE4 (tr : Trace Fp) (t q : Nat) (pub : List Fp) (off : Nat) : (leE (pubs off 4)).eval tr t q pub =
    pub.getD off 0 + (256 : Nat) * pub.getD (off + 1) 0 + (65536 : Nat) * pub.getD (off + 2) 0 +
      (16777216 : Nat) * pub.getD (off + 3) 0 := by
  simp [leE, pubs, List.range_succ]
  grind

theorem leN'4 (pub : List Fp) (off : Nat) : leN' (pubBytes pub off 4) = (pubNat pub off % 256) +
    256 * (pubNat pub (off + 1) % 256) + 65536 * (pubNat pub (off + 2) % 256) + 16777216 * (pubNat pub (off + 3) % 256) := by
  simp [leN', pubBytes, List.range_succ, NearSpec.leNat]
  omega

theorem pub_eq_cast (pub : List Fp) (i : Nat) : pub.getD i 0 = ((pubNat pub i : Nat) : Fp) := by
  simp [pubNat, natCast_eq, fpN]

theorem pubNat_lt (pub : List Fp) (i : Nat) : pubNat pub i < P := Fp.toNat_lt _

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- Constraints on the public inputs alone (row 0). -/
theorem pub_consts :
    pubNat pub (PV_N + 2) = 0 ∧ pubNat pub (PV_N + 3) = 0 ∧ pubNat pub (PV_N + 1) ≤ 1 ∧
    pubNat pub (PV_N + 1) * pubNat pub PV_N = 0 ∧ pubNat pub (PV_NREF + 2) = 0 ∧ pubNat pub (PV_NREF + 3) = 0 := by
  have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
  have c1 := con hL h0 (e := .pub (PV_N + 2)) (mem_cl (by simp [cClaim]))
  have c2 := con hL h0 (e := .pub (PV_N + 3)) (mem_cl (by simp [cClaim]))
  have c3 := con hL h0 (e := Dsl.bool (.pub (PV_N + 1))) (mem_cl (by simp [cClaim]))
  have c4 := con hL h0 (e := .mul (.pub (PV_N + 1)) (.pub PV_N)) (mem_cl (by simp [cClaim]))
  have c5 := con hL h0 (e := .pub (PV_NREF + 2)) (mem_cl (by simp [cClaim]))
  have c6 := con hL h0 (e := .pub (PV_NREF + 3)) (mem_cl (by simp [cClaim]))
  simp only [eval_pub, eval_bool, eval_mul] at c1 c2 c3 c4 c5 c6
  have z : ∀ i, pub.getD i 0 = 0 → pubNat pub i = 0 := fun i h => by unfold pubNat; rw [h]; rfl
  refine ⟨z _ c1, z _ c2, cv_bool (t := 0) (r := 0) (x := 0) (tr := ⟨fun _ => 0, fun _ _ _ => pub.getD (PV_N + 1) 0⟩)
    (bool_cases c3), ?_, z _ c5, z _ c6⟩
  rw [pub_eq_cast pub (PV_N + 1), pub_eq_cast pub PV_N, ← natCast_mul] at c4
  have hb := cv_bool (t := 0) (r := 0) (x := 0) (tr := ⟨fun _ => 0, fun _ _ _ => pub.getD (PV_N + 1) 0⟩)
    (bool_cases c3)
  have : pubNat pub (PV_N + 1) * pubNat pub PV_N < P := by
    have := pubNat_lt pub PV_N
    calc _ ≤ 1 * pubNat pub PV_N := Nat.mul_le_mul_right _ (by simpa [cv, pubNat] using hb)
      _ < P := by omega
  exact ofNat_inj this (by unfold P; omega) c4

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- The refund counter. -/
theorem rcnt_of {rcs : List RS} (S : Shape tr rcs) : ∀ i (hi : i < rcs.length),
    tr.cell T_RCPT rcs[i].s rcnt = ((((rcs.take i).filter (·.h)).length : Nat) : Fp) := by
  intro i
  induction i with
  | zero => intro hi; rw [show rcs[0].s = 12 by rw [s_get S 0 hi]; rfl, S.rcnt0]; simp; rfl
  | succ i ih =>
    intro hi
    rw [(S.chain i hi).2.2, ih (by omega), (S.lay _ (List.getElem_mem (by omega))).hr]
    rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.filter_append, List.length_append]
    rw [natCast_add]
    cases h : rcs[i].h <;> simp [h] <;> rfl

/-- **The batch's last row.** -/
theorem last_facts {rcs : List RS} (S : Shape tr rcs) :
    ((rcs.length : Nat) : Fp) = (nPubE).eval tr T_RCPT 0 pub ∧
    ((((rcs.filter (·.h)).length : Nat) : Nat) : Fp) = (nrefPubE).eval tr T_RCPT 0 pub ∧
    (rcs.getD (rcs.length - 1) default).s + (rcs.getD (rcs.length - 1) default).tot - 1 < tr.height T_RCPT ∧
    tr.cell T_RCPT ((rcs.getD (rcs.length - 1) default).s + (rcs.getD (rcs.length - 1) default).tot - 1) lastR = 1 ∧
    ∀ j, j < 16 → tr.cell T_RCPT ((rcs.getD (rcs.length - 1) default).s +
      (rcs.getD (rcs.length - 1) default).tot - 1) (tok j) = pub.getD (PV_TOK + j) 0 := by
  have hn : 0 < rcs.length := by have := S.ne; cases rcs <;> simp_all
  have hi : rcs.length - 1 < rcs.length := by omega
  have hg := rcs_get hL (rcs := rcs) (rcs.length - 1) hi
  have lay := S.lay rcs[rcs.length - 1] (List.getElem_mem hi)
  have hT := total_pos rcs[rcs.length - 1].h rcs[rcs.length - 1].Lp rcs[rcs.length - 1].Lv rcs[rcs.length - 1].Ls
    rcs[rcs.length - 1].kt
  have hfin := lay.fin
  have hact := act_after S hL (rcs.length - 1) hi
  rw [if_neg (by omega)] at hact
  rw [hg]
  have hq : rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1 + 1 < tr.height T_RCPT := by
    unfold RS.tot at *; omega
  have hrl : tr.cell T_RCPT (rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1) rl = 1 := lay.endRl
  have hl : tr.cell T_RCPT (rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1) lastR = 1 := by
    rw [lastR_eq hL hq, hrl, show rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1 + 1 =
      rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot by unfold RS.tot at *; omega, hact]; grind
  have hq' : rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1 < tr.height T_RCPT := by omega
  -- constants on the last row
  obtain ⟨f, hf, h1, h2⟩ := plan_cover rcs[rcs.length - 1].h rcs[rcs.length - 1].Lp rcs[rcs.length - 1].Lv
    rcs[rcs.length - 1].Ls rcs[rcs.length - 1].kt (rcs[rcs.length - 1].tot - 1) (by unfold RS.tot at *; omega)
  have K := (lay.flds f hf).consts (rcs[rcs.length - 1].tot - 1 - f.2.1) (by omega)
  rw [show rcs[rcs.length - 1].s + f.2.1 + (rcs[rcs.length - 1].tot - 1 - f.2.1) =
    rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1 by unfold RS.tot at *; omega] at K
  have c1 := con hL hq' (e := .mul (c lastR) (sub (.add (c Rcpt.r) (k 1)) nPubE)) (mem_en (by simp [cEnd]))
  have c2 := con hL hq' (e := .mul (c lastR) (sub (.add (c rcnt) (c Rcpt.hr)) nrefPubE)) (mem_en (by simp [cEnd]))
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k] at c1 c2
  rw [hl, K _ rC] at c1
  rw [hl, K _ rcntC, K _ hrC] at c2
  rw [S.r _ hi] at c1
  rw [rcnt_of hL S _ hi, lay.hr] at c2
  have ev : ∀ e : Expr, (e = nPubE ∨ e = nrefPubE) →
      e.eval tr T_RCPT (rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1) pub = e.eval tr T_RCPT 0 pub := by
    intro e he; rcases he with rfl | rfl <;> simp [nPubE, nrefPubE, leE4]
  rw [ev _ (Or.inl rfl)] at c1
  rw [ev _ (Or.inr rfl)] at c2
  refine ⟨?_, ?_, hq', hl, fun j hj => ?_⟩
  · rw [show rcs.length = rcs.length - 1 + 1 by omega, natCast_add]; grind
  · have e : (rcs.filter (·.h)).length = ((rcs.take (rcs.length - 1)).filter (·.h)).length +
        (if rcs[rcs.length - 1].h then 1 else 0) := by
      rw [show rcs.filter (·.h) = (rcs.take (rcs.length - 1) ++ rcs.drop (rcs.length - 1)).filter (·.h) by
        rw [List.take_append_drop]]
      rw [List.filter_append, List.length_append, List.drop_eq_getElem_cons hi,
        List.drop_of_length_le (by omega)]
      cases hh : rcs[rcs.length - 1].h <;> simp [hh]
    rw [e, natCast_add]
    cases hh : rcs[rcs.length - 1].h <;> simp only [hh, Bool.false_eq_true, ↓reduceIte] at c2 ⊢ <;> grind
  · have c3 := con hL hq' (e := .mul (c lastR) (sub (c (tok j)) (.pub (PV_TOK + j)))) (mem_en (by
      unfold cEnd; simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
    simp only [eval_mul, eval_c, eval_sub, eval_pub] at c3
    rw [hl] at c3; grind

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem consec_len : ∀ (segs : List (Nat × Nat)) (s0 : Nat), Consec s0 segs → (∀ p ∈ segs, 1 ≤ p.2) →
    segs.length + s0 ≤ segEnd s0 segs := by
  intro segs
  induction segs with
  | nil => intro s0 _ _; simp [segEnd]
  | cons p rest ih =>
    intro s0 hc hp
    obtain ⟨s, l⟩ := p
    obtain ⟨rfl, hc⟩ := hc
    have := ih (s + l) hc (fun q hq => hp q (by simp [hq]))
    have := hp (s, l) (by simp)
    simp only [segEnd, List.length_cons] at *; omega

theorem viewOf_filter (tr : Trace Fp) (rcs : List RS) :
    ((viewOf tr rcs).filter (·.hr)).length = (rcs.filter (·.h)).length := by
  simp [viewOf, List.filter_map, Function.comp_def, rcptOf]

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem len_lt {rcs : List RS} (S : Shape tr rcs) : rcs.length + 12 < tr.height T_RCPT := by
  have := consec_len (segsOf rcs) 12 S.consec (fun p hp => by
    simp only [segsOf, List.mem_map] at hp
    obtain ⟨y, -, rfl⟩ := hp
    have := total_pos y.h y.Lp y.Lv y.Ls y.kt; simp [RS.tot]; omega)
  have := S.fin
  simp [segsOf] at *; omega

theorem count_ok {rcs : List RS} (S : Shape tr rcs) :
    (∀ x, x < 4 → pubNat pub (PV_N + x) < 256) →
      (viewOf tr rcs).length = nPubLE pub ∧ 1 ≤ (viewOf tr rcs).length ∧ (viewOf tr rcs).length ≤ 256 := by
  intro hb
  have hn : 0 < rcs.length := by have := S.ne; cases rcs <;> simp_all
  have hlen := len_lt hL S
  have hH := height_le hL
  obtain ⟨z2, z3, z1, z10, -, -⟩ := pub_consts hL
  have e := (last_facts hL S).1
  simp only [nPubE, leE4] at e
  rw [pub_eq_cast pub PV_N, pub_eq_cast pub (PV_N + 1), pub_eq_cast pub (PV_N + 2), pub_eq_cast pub (PV_N + 3),
    z2, z3] at e
  have e' : ((rcs.length : Nat) : Fp) = ((pubNat pub PV_N + 256 * pubNat pub (PV_N + 1) : Nat) : Fp) := by
    rw [e, natCast_add, natCast_mul]; grind
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega)
  simp only [Nat.add_zero] at b0
  have := ofNat_inj (by unfold P; omega) (by unfold P; omega) e'
  rw [viewOf_len]
  refine ⟨?_, by omega, ?_⟩
  · rw [nPubLE, leN'4, z2, z3, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1]; omega
  · rcases Nat.lt_or_ge (pubNat pub (PV_N + 1)) 1 with h | h
    · omega
    · have : pubNat pub PV_N = 0 := by
        rcases Nat.eq_zero_or_pos (pubNat pub PV_N) with h' | h'
        · exact h'
        · exfalso; have := Nat.mul_le_mul h h'; omega
      omega

theorem refunds_ok {rcs : List RS} (S : Shape tr rcs) :
    (∀ j, j < 309 → pubNat pub j < 256) →
      ((viewOf tr rcs).filter (·.hr)).length = leN' (pubBytes pub PV_NREF 4) := by
  intro hb
  have hlen := len_lt hL S
  have hH := height_le hL
  obtain ⟨-, -, -, -, z2, z3⟩ := pub_consts hL
  have e := (last_facts hL S).2.1
  simp only [nrefPubE, leE4] at e
  rw [pub_eq_cast pub PV_NREF, pub_eq_cast pub (PV_NREF + 1), pub_eq_cast pub (PV_NREF + 2),
    pub_eq_cast pub (PV_NREF + 3), z2, z3] at e
  have e' : ((((rcs.filter (·.h)).length : Nat) : Nat) : Fp) =
      ((pubNat pub PV_NREF + 256 * pubNat pub (PV_NREF + 1) : Nat) : Fp) := by
    rw [e, natCast_add, natCast_mul]; grind
  have b0 := hb PV_NREF (by decide); have b1 := hb (PV_NREF + 1) (by decide)
  have hf : (rcs.filter (·.h)).length ≤ rcs.length := List.length_filter_le _ _
  have := ofNat_inj (by unfold P; omega) (by unfold P; omega) e'
  rw [viewOf_filter, this, leN'4, z2, z3, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1]; omega

end ZkFormal.Near.RcptProof
