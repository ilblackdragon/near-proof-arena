import ReexecNpai.Spec.Front
import ReexecNpai.Trie.Lemmas
import NpaiIR.Lib.NumSpec

/-!
# Helper lemmas for `Spec/Walk.lean`: bitmaps and hex-prefix encodings
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Nibbles stored one per byte. -/
def nibBytes (k : List Nat) : Bytes := k.map fun x => UInt8.ofNat x

/-- Registers 14/15 hold the constants, memory outside `[lo, hi)` is unchanged. -/
def KeepOut (lo hi : Nat) (m m' : M) : Prop :=
  m'.regs 14 = m.regs 14 ∧ m'.regs 15 = m.regs 15 ∧ ∀ a, (a < lo ∨ hi ≤ a) → m'.mem a = m.mem a

/-- VC generation for this file (the shared simp set with a goal-only discharger). -/
syntax "walk_vc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| walk_vc) => `(tactic| walk_vc [])
  | `(tactic| walk_vc [$ts,*]) => `(tactic|
      simp (disch := (first | omega | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega)))
        only [wp_seq, wp_op, wp_ite, wp_nop, twp_seq, twp_op, twp_ite, twp_nop,
        wp_fail_iff P_mem_le, twp_fail_iff P_mem_le, okInstr, not_true_eq_false, false_and, and_false,
        false_or, or_false, Nat.reduceDiv, Nat.reduceSub, ins, setReg_apply, ite_pos, ite_neg, evAbyte, evAbyte',
        evA, evS, evM, evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ,
        need, le, lt, eqc, P_memSize, Bool.true_eq_false, Bool.false_eq_true, Option.some.injEq,
        forall_eq', true_implies, imp_self, implies_true, and_true, true_and, Inp, Inputs.tape,
        Option.ite_none_right_eq_some, and_imp, exists_eq_left', exists_eq_left, and_assoc, exists_and_left,
        not_false_eq_true, Nat.zero_add, Nat.le_refl, ite10_ne_zero, ite10_eq_zero, forall_apply_eq_imp_iff₂,
        List.drop_zero, AR, KL, C_NODES, S_KEY, S_HP, $ts,*])

namespace WalkProof

theorem fsr {C : List Nat} {m : M} {r : Nat → Nat} {a v : Nat} (ha : a ∈ C)
    (h : ∀ j, j ∉ C → r j = m.regs j) : ∀ j, j ∉ C → setReg r a v j = m.regs j := by
  intro j hj
  have hne : j ≠ a := fun e => hj (e ▸ ha)
  simp only [setReg_apply, hne, ↓reduceIte]; exact h j hj

theorem evShr4 (x : Nat) (h : x < 256) : BinOp.shr.eval x 4 = x / 16 := by
  rw [eval_shr x 4 (by decide) (by unfold wordMod; omega)]

theorem evAnd15 (x : Nat) : BinOp.and.eval x 15 = x % 16 := by
  simp only [BinOp.eval]
  have : x &&& 15 = x % 16 := by
    have := Nat.and_two_pow_sub_one_eq_mod x 4
    simpa using this
  rw [this]; exact Nat.mod_eq_of_lt (by unfold wordMod; omega)

theorem nibbles_append (a b : Bytes) : nibbles (a ++ b) = nibbles a ++ nibbles b := by
  induction a with
  | nil => rfl
  | cons x r ih => simp [nibbles, ih]

theorem nibBytes_append (a b : List Nat) : nibBytes (a ++ b) = nibBytes a ++ nibBytes b := by
  simp [nibBytes]

theorem wm1 (M0 : Nat → UInt8) (a : Nat) (v : UInt8) (x : Nat) :
    writeMem M0 a 1 [v] x = if x = a then v else M0 x := by
  simp only [writeMem]
  by_cases h : x = a
  · subst h; simp
  · rw [ite_neg (by omega), ite_neg h]

theorem readMem_wm1_out (M0 : Nat → UInt8) (a : Nat) (v : UInt8) (p n : Nat) (h : a < p ∨ p + n ≤ a) :
    readMem (writeMem M0 a 1 [v]) p n = readMem M0 p n := by
  rw [readMem_ext]; intro i hi; rw [wm1, ite_neg (by omega)]

theorem nibbles_snoc (l : Bytes) (b : UInt8) :
    nibbles (0 :: (l ++ [b])) = nibbles (0 :: l) ++ [b.toNat / 16, b.toNat % 16] := by
  rw [← List.cons_append, nibbles_append]; rfl

end WalkProof


namespace WalkAux

/-! ## The revealed-children bitmap -/

theorem bitsRev_succ : ∀ (ks : List (Option (Option (List UInt8)))) (i : Nat), bitsRev ks (i + 1) = 2 * bitsRev ks i
  | [], _ => rfl
  | none :: r, i => by simp only [bitsRev]; exact bitsRev_succ r (i + 1)
  | some (some _) :: r, i => by simp only [bitsRev]; exact bitsRev_succ r (i + 1)
  | some none :: r, i => by
    simp only [bitsRev]; rw [bitsRev_succ r (i + 1), Nat.pow_succ]; omega

theorem bitsRev_cons (x : Option (Option (List UInt8))) (r : List (Option (Option (List UInt8)))) :
    bitsRev (x :: r) 0 = (if x = some none then 1 else 0) + 2 * bitsRev r 0 := by
  rcases x with _ | _ | h <;> simp [bitsRev, bitsRev_succ]

theorem bitsRev_div : ∀ (ks : List (Option (Option (List UInt8)))) (n : Nat), bitsRev ks 0 / 2 ^ n = bitsRev (ks.drop n) 0
  | ks, 0 => by simp
  | [], n + 1 => by simp [bitsRev]
  | x :: r, n + 1 => by
    rw [bitsRev_cons, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, ← Nat.div_div_eq_div_mul, List.drop_succ_cons,
      ← bitsRev_div r n]
    congr 1; split <;> omega

theorem bitsRev_bit (ks : List (Option (Option (List UInt8)))) (n : Nat) :
    bitsRev ks 0 / 2 ^ n % 2 = if ks[n]? = some (some none) then 1 else 0 := by
  rw [bitsRev_div]
  cases h : ks.drop n with
  | nil =>
    have : ks.length ≤ n := by
      have := congrArg List.length h; simp at this; omega
    simp [bitsRev, List.getElem?_eq_none this]
  | cons x r =>
    have hx : ks[n]? = some x := by
      rw [← List.head?_drop, h]; rfl
    rw [hx, bitsRev_cons]
    simp only [Option.some.injEq]
    split <;> omega

theorem bitsRev_lt : ∀ (ks : List (Option (Option (List UInt8)))), bitsRev ks 0 < 2 ^ ks.length
  | [] => by simp [bitsRev]
  | x :: r => by
    have := bitsRev_lt r
    rw [bitsRev_cons, List.length_cons, Nat.pow_succ]; split <;> omega

theorem popcN_zero : ∀ k, popcN k 0 = 0
  | 0 => rfl
  | k + 1 => by simp only [popcN, Nat.zero_mod, Nat.zero_div, popcN_zero k]

theorem popcN_bitsRev : ∀ (k : Nat) (ks : List (Option (Option (List UInt8)))), ks.length ≤ k →
    popcN k (bitsRev ks 0) = nRev ks
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | k + 1, [], _ => by
    simp only [bitsRev, nRev_nil]
    exact popcN_zero (k + 1)
  | k + 1, x :: r, h => by
    simp only [popcN]
    rw [bitsRev_cons, nRev_cons]
    have e1 : ((if x = some none then 1 else 0) + 2 * bitsRev r 0) % 2 = if x = some none then 1 else 0 := by
      split <;> omega
    have e2 : ((if x = some none then 1 else 0) + 2 * bitsRev r 0) / 2 = bitsRev r 0 := by
      split <;> omega
    rw [e1, e2, popcN_bitsRev k r (by simp at h; omega)]; omega

theorem nRev_take_drop (ks : List (Option (Option (List UInt8)))) (n : Nat) :
    nRev ks = revBelow ks n + nRev (ks.drop n) := by
  unfold revBelow nRev
  conv => lhs; rw [← List.take_append_drop n ks]
  rw [List.countP_append]

theorem revBelow_succ_of (ks : List (Option (Option (List UInt8)))) (n : Nat) (h : ks[n]? = some (some none)) :
    revBelow ks (n + 1) = revBelow ks n + 1 := by
  induction ks generalizing n with
  | nil => simp at h
  | cons x r ih =>
    cases n with
    | zero => simp at h; subst h; simp [revBelow, nRev_cons]
    | succ n =>
      simp at h
      rw [revBelow_succ, revBelow_succ x r n, ih n h]; omega

/-- The branch step's child position: popcount of the bits above `n`. -/
theorem popc_above (ks : List (Option (Option (List UInt8)))) (hl : ks.length = 16) (n : Nat)
    (h : ks[n]? = some (some none)) :
    popcN 16 (bitsRev ks 0 / 2 ^ (n + 1)) = nRev ks - 1 - revBelow ks n := by
  rw [bitsRev_div, popcN_bitsRev 16 _ (by simp; omega)]
  have := nRev_take_drop ks (n + 1)
  rw [revBelow_succ_of ks n h] at this
  omega

/-! ## Hex-prefix encodings -/

theorem packNibbles_length : ∀ (l : List Nat), (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | a :: b :: r => by
    simp only [packNibbles, List.length_cons, packNibbles_length r]; omega

theorem hexPrefix_len (k : List Nat) (b : Bool) : (hexPrefix k b).length = 1 + k.length / 2 := by
  rcases k with _ | ⟨n, rest⟩
  · simp [hexPrefix, packNibbles]
  · by_cases hp : (rest.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, hp, packNibbles_length]; omega
    · have : (rest.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, this, packNibbles_length]; omega

theorem packNibbles_getD : ∀ (l : List Nat) (i : Nat), i < l.length / 2 →
    (packNibbles l).getD i 0 = UInt8.ofNat (l.getD (2 * i) 0 * 16 + l.getD (2 * i + 1) 0)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: r, 0, _ => by simp [packNibbles]
  | a :: b :: r, i + 1, h => by
    simp only [packNibbles, List.getD_cons_succ]
    rw [packNibbles_getD r i (by simp at h; omega)]
    congr 2 <;> simp [Nat.mul_add, List.getD_cons_succ]

theorem nibs_ok (l : List Nat) (h : ∀ x ∈ l, x < 16) : nibblesOk l = true := by
  simp only [nibblesOk, List.all_eq_true, decide_eq_true_eq]; exact h

theorem packNibbles_inj : ∀ (a b : List Nat), (∀ x ∈ a, x < 16) → (∀ x ∈ b, x < 16) →
    a.length % 2 = 0 → b.length % 2 = 0 → packNibbles a = packNibbles b → a = b
  | [], [], _, _, _, _, _ => rfl
  | [], [_], _, _, _, hb, _ => by simp at hb
  | [], _ :: _ :: _, _, _, _, _, h => by simp [packNibbles] at h
  | [_], _, _, _, ha, _, _ => by simp at ha
  | _ :: _ :: _, [], _, _, _, _, h => by simp [packNibbles] at h
  | _ :: _ :: _, [_], _, _, _, hb, _ => by simp at hb
  | x :: y :: r, u :: v :: s, ha, hb, hla, hlb, h => by
    simp only [packNibbles, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx := ha x (by simp); have hy := ha y (by simp)
    have hu := hb u (by simp); have hv := hb v (by simp)
    have e := congrArg UInt8.toNat h1
    simp only [UInt8.toNat_ofNat', Nat.reducePow] at e
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
    have : x = u := by omega
    have : y = v := by omega
    subst x; subst y
    rw [packNibbles_inj r s (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))
      (by simp at hla; omega) (by simp at hlb; omega) h2]

/-- `hexPrefix` is injective on nibble lists. -/
theorem hexPrefix_inj (a b : List Nat) (lf : Bool) (ha : ∀ x ∈ a, x < 16) (hb : ∀ x ∈ b, x < 16)
    (h : hexPrefix a lf = hexPrefix b lf) : a = b := by
  have hf : ∀ (l : List Nat), (∀ x ∈ l, x < 16) →
      (hexPrefix l lf = UInt8.ofNat ((if lf then 32 else 0)) :: packNibbles l ∧ l.length % 2 = 0) ∨
      (∃ n r, l = n :: r ∧ n < 16 ∧ r.length % 2 = 0 ∧
        hexPrefix l lf = UInt8.ofNat (16 + n + (if lf then 32 else 0)) :: packNibbles r) := by
    intro l hl
    rcases l with _ | ⟨n, r⟩
    · left; simp [hexPrefix]
    · by_cases hp : (r.length + 1) % 2 = 1
      · right; refine ⟨n, r, rfl, hl n (by simp), by omega, ?_⟩
        simp only [hexPrefix, List.length_cons, hp]
      · left
        refine ⟨?_, by simp; omega⟩
        have : (r.length + 1) % 2 = 0 := by omega
        simp only [hexPrefix, List.length_cons, this]
  have key : ∀ (n : Nat), n < 16 → UInt8.ofNat (16 + n + (if lf then 32 else 0)) ≠ UInt8.ofNat (if lf then 32 else 0) := by
    intro n hn e
    have := congrArg UInt8.toNat e
    simp only [UInt8.toNat_ofNat', Nat.reducePow] at this
    cases lf <;> simp at this <;> omega
  rcases hf a ha with ⟨ea, pa⟩ | ⟨n, r, rfl, hn, pr, ea⟩ <;>
  rcases hf b hb with ⟨eb, pb⟩ | ⟨n', r', rfl, hn', pr', eb⟩ <;> rw [ea, eb] at h <;>
    simp only [List.cons.injEq] at h
  · exact packNibbles_inj a b ha hb pa pb h.2
  · exact absurd h.1.symm (key n' hn')
  · exact absurd h.1 (key n hn)
  · have e := congrArg UInt8.toNat h.1
    simp only [UInt8.toNat_ofNat', Nat.reducePow] at e
    have : n = n' := by cases lf <;> simp at e <;> omega
    subst this
    rw [packNibbles_inj r r' (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz])) pr pr' h.2]

theorem hexPrefix_getD0 (s : List Nat) (lf : Bool) :
    (hexPrefix s lf).getD 0 0 =
      UInt8.ofNat (if s.length % 2 = 1 then 16 + s.getD 0 0 + (if lf then 32 else 0) else (if lf then 32 else 0)) := by
  rcases s with _ | ⟨n, r⟩
  · simp [hexPrefix]
  · by_cases hp : (r.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, hp]; simp
    · have : (r.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, this]; simp

theorem hexPrefix_getD_succ (s : List Nat) (lf : Bool) (i : Nat) (hi : i < s.length / 2) :
    (hexPrefix s lf).getD (i + 1) 0 =
      UInt8.ofNat (s.getD (s.length % 2 + 2 * i) 0 * 16 + s.getD (s.length % 2 + 2 * i + 1) 0) := by
  rcases s with _ | ⟨n, r⟩
  · simp at hi
  · by_cases hp : (r.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, hp, List.getD_cons_succ]
      rw [packNibbles_getD r i (by simp at hi; omega)]
      simp only [List.getD_cons_succ, show 1 + 2 * i = 2 * i + 1 by omega, show 1 + 2 * i + 1 = 2 * i + 1 + 1 by omega]
    · have : (r.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, this, List.getD_cons_succ, Nat.zero_add]
      rw [packNibbles_getD (n :: r) i (by simp at hi ⊢; omega)]
      simp only [List.getD_cons_succ]

theorem writeMem_step (M0 : Nat → UInt8) (a n : Nat) (L : List UInt8) :
    writeMem (writeMem M0 a n L) (a + n) 1 [L.getD n 0] = writeMem M0 a (n + 1) L := by
  funext j; simp only [writeMem]
  by_cases h1 : a + n ≤ j ∧ j < a + n + 1
  · have : j = a + n := by omega
    subst this; simp
  · rw [ite_neg h1]
    have : (a ≤ j ∧ j < a + n) ↔ (a ≤ j ∧ j < a + (n + 1)) := by omega
    simp only [this]

theorem mem_key {M0 : Nat → UInt8} {key : List Nat} (h : readMem M0 S_KEY key.length = nibBytes key)
    (hk : ∀ y ∈ key, y < 16) {i : Nat} (hi : i < key.length) : (M0 (S_KEY + i)).toNat = key.getD i 0 := by
  have := congrArg (fun l => l.getD i 0) h
  simp only [readMem, nibBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, List.getElem?_eq_getElem hi] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have := hk _ (List.getElem_mem hi)
  simp only [Option.getD_some, UInt8.toNat_ofNat', Nat.reducePow]; omega

end WalkAux

open WalkProof WalkAux

section
variable {pub cb pb : Bytes}

def hpLoopBody : Stmt := seqs [ADDI 12 8 S_KEY, LD8 13 12, SHL 13 13 6, ADDI 12 12 1, LD8 12 12, ADD 13 13 12,
    ST8 11 13, ADDI 11 11 1, ADDI 8 8 2, SUB 4 4 15]

theorem pHP_eq : pHP = seqs [AND 4 10 15, CST 11 S_HP,
    .ite 4 (seqs [ADDI 12 1 S_KEY, LD8 12 12, ADDI 12 12 16, ADD 12 12 6, ST8 11 12]) (ST8 11 6),
    ADD 8 1 4, SHR 4 10 15, ADDI 11 11 1, CST 6 4, .loop 4 hpLoopBody, SHR 6 10 15, ADDI 6 6 1] := rfl

theorem wm1_eq (M0 : Nat → UInt8) (a : Nat) (v : UInt8) (L : List UInt8) (h : L.getD 0 0 = v) :
    writeMem M0 a 1 [v] = writeMem M0 a 1 L := by
  funext j; simp only [writeMem]
  by_cases h1 : a ≤ j ∧ j < a + 1
  · have : j = a := by omega
    subst this; simp [← h, List.getD_eq_getElem?_getD]
  · rw [ite_neg h1, ite_neg h1]

theorem frame_hp {x y y' : M} {r : Nat → Nat} (hy : ∀ j, j ∉ [4, 6, 8, 11, 12, 13] → y.regs j = x.regs j)
    (hF : Frame [4, 8, 11, 12, 13] y y') (hr : ∀ j, j ≠ 6 → r j = y'.regs j) :
    ∀ j, j ∉ [4, 6, 8, 11, 12, 13] → r j = x.regs j := by
  intro j hj
  have h6 : j ≠ 6 := by intro e; apply hj; simp [e]
  rw [hr j h6, hF j (by simp at hj ⊢; omega), hy j hj]

theorem evShl4 (a : Nat) (h : a < 16) : BinOp.shl.eval a 4 = a * 16 := by
  rw [eval_shl a 4 (by decide) (by unfold wordMod; omega)]

theorem evAnd1 (x : Nat) : BinOp.and.eval x 1 = x % 2 := by
  simp only [BinOp.eval]
  have : x &&& 1 = x % 2 := by
    have := Nat.and_two_pow_sub_one_eq_mod x 1
    simpa using this
  rw [this]; exact Nat.mod_eq_of_lt (by unfold wordMod; omega)

theorem slice_getD (key : List Nat) (o cnt q : Nat) (hq : q < cnt) (h : o + cnt ≤ key.length) :
    ((key.drop o).take cnt).getD q 0 = key.getD (o + q) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hq, ↓reduceIte, List.getElem?_drop]

theorem walkHPLoop_twp {y : M} {M0 : Nat → UInt8} {key : List Nat} {o cnt : Nat} {lf : Bool} (hk1 : y.regs 15 = 1)
    (hkey : readMem M0 S_KEY key.length = nibBytes key) (hk16 : ∀ z ∈ key, z < 16) (hkl : key.length ≤ 130)
    (ho : o + cnt ≤ key.length)
    (hmem : y.mem = writeMem M0 S_HP 1 (hexPrefix ((key.drop o).take cnt) lf))
    (h4 : y.regs 4 = cnt / 2) (h8 : y.regs 8 = o + cnt % 2) (h11 : y.regs 11 = S_HP + 1) (h6 : y.regs 6 = 4) :
    twp P (Inp pub cb pb) (.loop 4 hpLoopBody) y (fun y' c =>
      y'.mem = writeMem M0 S_HP (1 + cnt / 2) (hexPrefix ((key.drop o).take cnt) lf) ∧
      Frame [4, 8, 11, 12, 13] y y' ∧ c ≤ 12 * (cnt / 2) + 1) := by
  have hsl : ((key.drop o).take cnt).length = cnt := by simp; omega
  refine twp_loopDown (J := fun k y' => k ≤ cnt / 2 ∧ y'.regs 11 = S_HP + 1 + (cnt / 2 - k) ∧
      y'.regs 8 = o + cnt % 2 + 2 * (cnt / 2 - k) ∧ y'.regs 6 = 4 ∧
      y'.mem = writeMem M0 S_HP (1 + (cnt / 2 - k)) (hexPrefix ((key.drop o).take cnt) lf) ∧
      Frame [4, 8, 11, 12, 13] y y') (cnt / 2) 10 ⟨Nat.le_refl _, by simp [h11], by simp [h8], h6,
        by simp [hmem], Frame.refl _ _⟩ h4 ?_ ?_
  · intro j y' hj ⟨hjh, h11', h8', h6', hm', hF⟩ h4'
    have hy1 : y'.regs 15 = 1 := by rw [hF 15 (by simp)]; exact hk1
    have hq : o + cnt % 2 + 2 * (cnt / 2 - j) + 1 < key.length := by omega
    have ha := mem_key hkey hk16 (i := o + cnt % 2 + 2 * (cnt / 2 - j)) (by omega)
    have hb := mem_key hkey hk16 (i := o + cnt % 2 + 2 * (cnt / 2 - j) + 1) (by omega)
    have hm1 : y'.mem (o + cnt % 2 + 2 * (cnt / 2 - j) + 512) = M0 (512 + (o + cnt % 2 + 2 * (cnt / 2 - j))) := by
      rw [hm', Nat.add_comm _ 512]; exact writeMem_apply_out' _ _ _ _ _ (by simp only [S_HP]; omega)
    have hm2 : y'.mem (o + cnt % 2 + 2 * (cnt / 2 - j) + 512 + 1) =
        M0 (512 + (o + cnt % 2 + 2 * (cnt / 2 - j) + 1)) := by
      rw [hm', show o + cnt % 2 + 2 * (cnt / 2 - j) + 512 + 1 = 512 + (o + cnt % 2 + 2 * (cnt / 2 - j) + 1) by omega]
      exact writeMem_apply_out' _ _ _ _ _ (by simp only [S_HP]; omega)
    have hka : key.getD (o + cnt % 2 + 2 * (cnt / 2 - j)) 0 < 16 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hk16 _ (List.getElem_mem _)
    have hkb : key.getD (o + cnt % 2 + 2 * (cnt / 2 - j) + 1) 0 < 16 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hk16 _ (List.getElem_mem _)
    simp only [S_KEY] at ha hb
    simp only [hpLoopBody]
    walk_vc [h8', h11', h6', h4', hy1]
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [hm1, hm2, ha, hb, evShl4 _ hka, evA _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
      have e : (hexPrefix ((key.drop o).take cnt) lf).getD (1 + (cnt / 2 - j)) 0 =
          UInt8.ofNat (key.getD (o + cnt % 2 + 2 * (cnt / 2 - j)) 0 * 16 +
            key.getD (o + cnt % 2 + 2 * (cnt / 2 - j) + 1) 0) := by
        rw [Nat.add_comm 1, hexPrefix_getD_succ _ _ _ (by rw [hsl]; omega), hsl,
          slice_getD _ _ _ _ (by omega) ho, slice_getD _ _ _ _ (by omega) ho]
        simp only [Nat.add_assoc]
      rw [← e, hm', show 769 + (cnt / 2 - j) = 768 + (1 + (cnt / 2 - j)) by omega]
      simp only [S_HP]
      rw [writeMem_step]; congr 1; omega
    · repeat (first | exact hF | refine fsr (by simp) ?_)
  · rintro y' c ⟨-, -, -, -, hm', hF⟩ - hc
    refine ⟨by simpa using hm', hF, ?_⟩
    rw [Nat.mul_comm 12]; omega

theorem walkHP_twp {x : M} {key : List Nat} {lf : Bool} (hk1 : x.regs 15 = 1) (hk8 : x.regs 14 = 8)
    (hkey : readMem x.mem S_KEY key.length = nibBytes key) (hk16 : ∀ y ∈ key, y < 16) (hkl : key.length ≤ 130)
    (ho : x.regs 1 + x.regs 10 ≤ key.length) (hf : x.regs 6 = if lf then 32 else 0) :
    twp P (Inp pub cb pb) pHP x (fun x' c =>
      x'.mem = writeMem x.mem S_HP (1 + x.regs 10 / 2) (hexPrefix ((key.drop (x.regs 1)).take (x.regs 10)) lf) ∧
      x'.regs 6 = 1 + x.regs 10 / 2 ∧ Frame [4, 6, 8, 11, 12, 13] x x' ∧ c ≤ 20 + 12 * (x.regs 10 / 2)) := by
  have hx10 : x.regs 10 < 18446744073709551616 := by omega
  simp only [pHP_eq]
  by_cases hpar : x.regs 10 % 2 = 0
  · walk_vc [hk1, hk8, evAnd1, evShr1 _ hx10, hpar]
    refine Or.inl (twp_mono (walkHPLoop_twp (M0 := x.mem) (o := x.regs 1) (cnt := x.regs 10) (lf := lf)
      (by simp [setReg_apply, hk1]) hkey hk16 hkl ho ?_ (by simp [setReg_apply]) (by simp [setReg_apply, hpar])
      (by simp [setReg_apply, S_HP]) (by simp [setReg_apply])) ?_)
    · simp only [S_HP]
      apply wm1_eq
      rw [hexPrefix_getD0]
      have : ((key.drop (x.regs 1)).take (x.regs 10)).length = x.regs 10 := by simp; omega
      rw [this, ite_neg (by omega), hf]
      cases lf <;> rfl
    · rintro y' c ⟨hm, hF, hc⟩
      have h10 : y'.regs 10 = x.regs 10 := by rw [hF 10 (by simp)]; simp [setReg_apply]
      have h15 : y'.regs 15 = 1 := by rw [hF 15 (by simp)]; simp [setReg_apply, hk1]
      rw [h10, h15, evShr1 _ hx10, evAddi _ _ (by omega)]
      refine ⟨hm, by omega, ?_, by omega⟩
      refine frame_hp (y := { regs := _, mem := _ }) ?_ hF ?_
      · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj; simp [setReg_apply, h1, h2, h3, h4, h5, h6]
      · intro j hj; simp [setReg_apply, hj]
  · have hpar1 : x.regs 10 % 2 = 1 := by omega
    have hk0 := mem_key hkey hk16 (i := x.regs 1) (by omega)
    have hk0' : key.getD (x.regs 1) 0 < 16 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hk16 _ (List.getElem_mem _)
    simp only [S_KEY] at hk0
    rw [Nat.add_comm] at hk0
    have hfl : x.regs 6 ≤ 32 := by rw [hf]; split <;> omega
    walk_vc [hk1, hk8, evAnd1, evShr1 _ hx10, hpar1, hk0]
    refine ⟨by omega, by omega, twp_mono (walkHPLoop_twp (M0 := x.mem) (o := x.regs 1) (cnt := x.regs 10) (lf := lf)
      (by simp [setReg_apply, hk1]) hkey hk16 hkl ho ?_ (by simp [setReg_apply]) (by simp [setReg_apply, hpar1])
      (by simp [setReg_apply, S_HP]) (by simp [setReg_apply])) ?_⟩
    · simp only [S_HP]
      apply wm1_eq
      rw [hexPrefix_getD0]
      have : ((key.drop (x.regs 1)).take (x.regs 10)).length = x.regs 10 := by simp; omega
      rw [this, ite_pos hpar1, hf, slice_getD _ _ _ _ (by omega) ho, Nat.add_zero]
      congr 1; rw [← hf]; omega
    · rintro y' c ⟨hm, hF, hc⟩
      have h10 : y'.regs 10 = x.regs 10 := by rw [hF 10 (by simp)]; simp [setReg_apply]
      have h15 : y'.regs 15 = 1 := by rw [hF 15 (by simp)]; simp [setReg_apply, hk1]
      rw [h10, h15, evShr1 _ hx10, evAddi _ _ (by omega)]
      refine ⟨hm, by omega, ?_, by omega⟩
      refine frame_hp (y := { regs := _, mem := _ }) ?_ hF ?_
      · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj; simp [setReg_apply, h1, h2, h3, h4, h5, h6]
      · intro j hj; simp [setReg_apply, hj]

end

end ReexecNpai
