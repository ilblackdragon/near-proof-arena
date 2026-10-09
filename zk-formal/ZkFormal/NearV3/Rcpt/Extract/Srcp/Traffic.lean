import ZkFormal.NearV3.Rcpt.Extract.Srcp.Units
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Defs

/-!
# ZkFormal.NearV3.Rcpt.Extract.Srcp.Traffic — messages of the `srcpV3` units

`rowT`: the messages of one row; `rootTraffic`, `leafTraffic`, `pathTraffic`: the messages of a
unit (all buses but `SIZE`) as the view's `srcpRootMsgs` / `srcpLeafMsgs` / `srcpItemMsgs`.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The 32 registers of row `r`. -/
def regsF (tr : Trace Fp) (tt r : Nat) : List Fp := (List.range 32).map fun x => tr.cell tt r (reg x)
def regsN (tr : Trace Fp) (tt r : Nat) : List Nat := (List.range 32).map fun x => (tr.cell tt r (reg x)).toNat

theorem regsN_toFp (r : Nat) : (regsN tr tt r).map Fp.ofNat = regsF tr tt r := by
  simp [regsN, regsF, Fp.ofNat_toNat]

theorem multNat1 (x : Nat) (r : Nat) :
    Interaction.multNat.go tr tt r pub [c x] 0 = if tr.cell tt r x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt r x = 1 <;> simp [h]

theorem rowT (r bb : Nat) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt r pub bb sd =
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt r sg = 1 then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt r q, (32 : Nat) * tr.cell tt r wn + tr.cell tt r pw,
          tr.cell tt r b]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ tr.cell tt r gD = 1 then
        [[tr.cell tt r cId, tr.cell tt r cLen] ++ regsF tr tt r] else []) ++
      (if bb = B_RCL ∧ sd = false ∧ tr.cell tt r rt = 1 then [[tr.cell tt r j, tr.cell tt r L]] else []) ++
      (if bb = B_SRC ∧ sd = false ∧ tr.cell tt r rt = 1 then
        [[tr.cell tt r j, tr.cell tt r dup] ++ regsF tr tt r] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ tr.cell tt r gz = 1 then [[((2 : Nat) : Fp), tr.cell tt r sz]] else []) := by
  simp only [rowTraffic, SrcpV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_append,
    List.map_nil, eval_c, eval_k, eval_mid, eval_add, eval_smul, List.append_assoc, regs, List.map_map,
    Function.comp_def, regsF, List.cons_append, List.nil_append]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))) <;> (split <;> split <;> simp_all [eq_comm]) <;> first | rfl | grind

theorem c16 : ((16 : Nat) : Fp) = (16 : Fp) := rfl
theorem c32 : ((32 : Nat) : Fp) = (32 : Fp) := rfl

theorem ofNat_msgId (kind x : Nat) : Fp.ofNat (msgId kind x) = (kind : Fp) + (16 : Nat) * Fp.ofNat x := by
  unfold msgId; rw [← ofNat_add', ← ofNat_mul']; rfl

theorem toFp_digMsg (id len : Nat) (d : List Nat) :
    Msg.toFp (digMsg id len d) = [Fp.ofNat id, Fp.ofNat len] ++ d.map Fp.ofNat := by
  simp [Msg.toFp, digMsg]

/-- Byte messages of a segment as `emitAt`. -/
theorem bytesEq {ℓ qN : Nat} {qF : Fp} (hq : Fp.ofNat qN = qF) {bytes : List Nat} (hl : bytes.length = ℓ)
    (bF : Nat → Fp) (hb : ∀ o, o < ℓ → Fp.ofNat (bytes.getD o 0) = bF o) :
    (List.range ℓ).flatMap (fun o => [[(K_SRC : Fp) + (16 : Nat) * qF, ((o : Nat) : Fp), bF o]]) =
      (emitAt (msgId K_SRC qN) 0 bytes).map Msg.toFp := by
  unfold emitAt
  rw [hl, List.map_map, map_eq_flatMap]
  apply flatMap_congr'; intro o ho
  simp only [Function.comp_apply, Msg.toFp, List.map_cons, List.map_nil, ofNat_msgId, hq, Nat.zero_add,
    hb o (List.mem_range.1 ho), natCast_eq]

section
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Root unit messages. -/
theorem rootTraffic {s : Nat} (hs : s < tr.height tt) (hrt : tr.cell tt s rt = 1) (B : SrcpB)
    (hj : B.j = (tr.cell tt s j).toNat) (hL' : B.L = (tr.cell tt s L).toNat)
    (hd : B.dup = decide (tr.cell tt s dup = 1)) (hr : B.root = regsN tr tt s)
    (hqe : B.qe = (tr.cell tt s qe).toNat) (hle : B.le = (tr.cell tt s le).toNat) (bb : Nat) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt s pub bb sd = (srcpRootMsgs B bb sd).map Msg.toFp := by
  obtain ⟨h1, -, -, hwl, -, hsl, -, -, -, hgD, hcid, -, -, hgz⟩ := local_ hL hs
  have hsg : tr.cell tt s sg = 0 := by rw [hrt] at h1; grind
  have hgD1 : tr.cell tt s gD = 1 := by
    obtain ⟨-, -, hwf, -⟩ := local_ hL hs
    rcases isBool hL hs (x := wf) (by simp [bools]) with h | h
    · rw [hgD, hrt, h]; grind
    · rw [(hwf h).1] at hsg; exact absurd hsg (by decide)
  have hgz0 : tr.cell tt s gz = 0 := by
    rcases isBool hL hs (x := gz) (by simp [bools]) with h | h
    · exact h
    · have := hgz h
      rcases isBool hL hs (x := wl) (by simp [bools]) with h' | h'
      · rw [hsl, h'] at this; grind
      · rw [(hwl h').1] at hsg; exact absurd hsg (by decide)
  have hdB := isBool hL hs (x := dup) (by simp [bools])
  rw [rowT, hsg, hgD1, hrt, hgz0, (hcid hrt).1, (hcid hrt).2]
  have z1 : ¬ ((0 : Fp) = 1) := by decide
  simp only [z1, and_false, if_false, List.nil_append, and_true, List.append_nil]
  unfold srcpRootMsgs
  by_cases b1 : bb = B_DIGEST
  · subst b1; cases sd <;> simp [B_DIGEST, B_RCL, B_SRC, toFp_digMsg, ofNat_msgId, hqe, hle, hr, regsN_toFp,
      Fp.ofNat_toNat, c16]
  · by_cases b2 : bb = B_RCL
    · subst b2; cases sd <;> simp [B_DIGEST, B_RCL, B_SRC, Msg.toFp, hj, hL', Fp.ofNat_toNat]
    · by_cases b3 : bb = B_SRC
      · subst b3
        cases sd
        · simp only [show B_SRC ≠ B_DIGEST by decide, show B_SRC ≠ B_RCL by decide, false_and, if_false,
            and_self, if_true, List.nil_append, List.map_cons, List.map_nil, Msg.toFp, List.map_append,
            hj, hr, hd, regsN_toFp, Fp.ofNat_toNat, true_and]
          rcases hdB with h | h <;> simp [h] <;> rfl
        · simp [B_DIGEST, B_RCL, B_SRC]
      · simp [b1, b2, b3]

/-- Messages of a segment row (all buses but `SIZE`). -/
theorem segRowT {s ℓ : Nat} (hu : IsU tr tt s ℓ) (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    {o : Nat} (ho : o < ℓ) {bb : Nat} (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd =
      (if bb = B_BYTES ∧ sd = true then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt s q, ((o : Nat) : Fp), tr.cell tt (s + o) b]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1 then
        [[tr.cell tt (s + o) cId, tr.cell tt (s + o) cLen] ++ regsF tr tt (s + o)] else []) := by
  obtain ⟨-, -, -, -, -, -, hrows⟩ := segRows hL hu hH hrt
  obtain ⟨hsg, hrt0, -, -, hsc⟩ := hrows o ho
  obtain ⟨hshape, hrow⟩ := segShape hL hu hH hrt
  have hℓ : ℓ ≤ 64 := by rcases hshape with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨hpw, hwn, hwf, -⟩ := hrow o ho
  obtain ⟨-, -, -, -, -, -, -, -, -, hgD, -⟩ := local_ hL (r := s + o) (by omega)
  have hq := hsc q (by simp [segConst])
  have hawB := isBool hL (r := s + o) (by omega) (x := aw) (by simp [bools])
  have z1 : ¬ ((0 : Fp) = 1) := by decide
  have hpos : (32 : Nat) * tr.cell tt (s + o) wn + tr.cell tt (s + o) pw = ((o : Nat) : Fp) := by
    rw [hwn, hpw]
    by_cases h : o < 32
    · rw [if_pos h, Nat.mod_eq_of_lt h]; grind
    · rw [if_neg h, show o % 32 = o - 32 by omega, show o = 32 + (o - 32) by omega, natCast_add]
      simp only [show 32 + (o - 32) - 32 = o - 32 by omega]; grind
  have hgDe : tr.cell tt (s + o) gD = 1 ↔ o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1 := by
    rw [hgD, hrt0, hwf]
    by_cases h : o % 32 = 0
    · rw [if_pos h]
      rcases hawB with h' | h' <;> rw [h'] <;> constructor <;> intro e <;>
        first | exact ⟨h, rfl⟩ | (exfalso; grind) | (exfalso; exact z1 e.2) | grind
    · rw [if_neg h]
      constructor
      · intro e; exfalso; grind
      · intro e; exact absurd e.1 h
  rw [rowT, hsg, hrt0, hq, hpos]
  simp only [z1, hb, and_false, false_and, and_true, ite_false, List.nil_append, List.append_nil, if_false]
  congr 1
  by_cases hD : bb = B_DIGEST ∧ sd = false
  · by_cases hg : o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1
    · rw [if_pos ⟨hD.1, hD.2, hgDe.2 hg⟩, if_pos ⟨hD.1, hD.2, hg⟩]
    · rw [if_neg (fun h => hg (hgDe.1 h.2.2)), if_neg (fun h => hg h.2.2)]
  · rw [if_neg (fun h => hD ⟨h.1, h.2.1⟩), if_neg (fun h => hD ⟨h.1, h.2.1⟩)]

end

end ZkFormal.NearV3.SrcpProof
