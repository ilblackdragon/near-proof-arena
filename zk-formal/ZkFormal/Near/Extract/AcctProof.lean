import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.AcctProof — `AcctViewStmt`

Row facts, 16-row segments (lane `i = 0 … 15`, `lo8 = [i < 8]`), the view
(`AcctV` per segment) and its traffic.  The value bytes are emitted lane by
lane; the view lists them in message order, so the BYTES traffic is equal up
to permutation (`List.Perm`, via `Nodup` and membership).
-/

namespace ZkFormal.Near.AcctProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

theorem con (hL : TableLocal Acct.table tr T_ACCT pub) {r : Nat} (hr : r < tr.height T_ACCT)
    {e : Expr} (he : e ∈ Acct.constraints) : e.eval tr T_ACCT r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height T_ACCT) : (r + 1) % tr.height T_ACCT = r + 1 :=
  Nat.mod_eq_of_lt h

variable (hL : TableLocal Acct.table tr T_ACCT pub)
include hL

theorem isBool {r : Nat} (hr : r < tr.height T_ACCT) {x : Nat} (hx : x ∈ [act, af, al, lo8, gS]) :
    tr.cell T_ACCT r x = 0 ∨ tr.cell T_ACCT r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold Acct.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem hx))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rowFacts {r : Nat} (hr : r < tr.height T_ACCT) :
    (tr.cell T_ACCT r af = 1 → tr.cell T_ACCT r act = 1 ∧ tr.cell T_ACCT r i = 0 ∧
      tr.cell T_ACCT r lo8 = 1 ∧ tr.cell T_ACCT r dsum = 255 - tr.cell T_ACCT r amt) ∧
    (tr.cell T_ACCT r al = 1 → tr.cell T_ACCT r act = 1 ∧ tr.cell T_ACCT r i = 15 ∧
      tr.cell T_ACCT r lo8 = 0 ∧ tr.cell T_ACCT r dsum * tr.cell T_ACCT r inv = 1) ∧
    (tr.cell T_ACCT r lo8 = 0 → tr.cell T_ACCT r st = 0) ∧
    tr.cell T_ACCT r gS = tr.cell T_ACCT r act * tr.cell T_ACCT r lo8 := by
  have h1 := con hL hr (e := .mul (c af) (Dsl.not (c act))) (by simp [Acct.constraints])
  have h2 := con hL hr (e := .mul (c al) (Dsl.not (c act))) (by simp [Acct.constraints])
  have h3 := con hL hr (e := .mul (c af) (c i)) (by simp [Acct.constraints])
  have h4 := con hL hr (e := .mul (c al) (sub (c i) (k 15))) (by simp [Acct.constraints])
  have h5 := con hL hr (e := .mul (c af) (Dsl.not (c lo8))) (by simp [Acct.constraints])
  have h6 := con hL hr (e := .mul (c al) (c lo8)) (by simp [Acct.constraints])
  have h7 := con hL hr (e := .mul (Dsl.not (c lo8)) (c st)) (by simp [Acct.constraints])
  have h8 := con hL hr (e := sub (c gS) (.mul (c act) (c lo8))) (by simp [Acct.constraints])
  have h9 := con hL hr (e := .mul (c af) (sub (c dsum) (sub (k 255) (c amt)))) (by simp [Acct.constraints])
  have h10 := con hL hr (e := .mul (c al) (sub (.mul (c dsum) (c inv)) (k 1))) (by simp [Acct.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by grind⟩
  · rw [h] at h1 h3 h5 h9; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h] at h2 h4 h6 h10; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h] at h7; grind

theorem within {r : Nat} (hr : r + 1 < tr.height T_ACCT)
    (ha : tr.cell T_ACCT r act = 1) (hl : tr.cell T_ACCT r al = 0) :
    tr.cell T_ACCT (r + 1) act = 1 ∧ tr.cell T_ACCT (r + 1) af = 0 ∧
    tr.cell T_ACCT (r + 1) kk = tr.cell T_ACCT r kk ∧ tr.cell T_ACCT (r + 1) tlast = tr.cell T_ACCT r tlast ∧
    tr.cell T_ACCT (r + 1) i = tr.cell T_ACCT r i + 1 ∧
    (tr.cell T_ACCT (r + 1) lo8 = 1 → tr.cell T_ACCT r lo8 = 1) ∧
    tr.cell T_ACCT (r + 1) dsum = tr.cell T_ACCT r dsum + (255 - tr.cell T_ACCT (r + 1) amt) := by
  have hr' : r < tr.height T_ACCT := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (Dsl.not (n act))) (by simp [Acct.constraints])
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (n af)) (by simp [Acct.constraints])
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (sub (n kk) (c kk))) (by simp [Acct.constraints])
  have h4 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (sub (n tlast) (c tlast)))
    (by simp [Acct.constraints])
  have h5 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (sub (n i) (.add (c i) (k 1))))
    (by simp [Acct.constraints])
  have h6 := con hL hr' (e := .mul (mul3 (c act) (Dsl.not (c al)) (n lo8)) (Dsl.not (c lo8)))
    (by simp [Acct.constraints])
  have h7 := con hL hr' (e := mul3 (c act) (Dsl.not (c al))
    (sub (n dsum) (.add (c dsum) (sub (k 255) (n amt))))) (by simp [Acct.constraints])
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr]
    at h1 h2 h3 h4 h5 h6 h7
  rw [ha, hl] at h1 h2 h3 h4 h5 h6 h7
  refine ⟨by grind, by grind, by grind, by grind, by grind, fun h => ?_, by grind⟩
  rw [h] at h6; grind

theorem switch {r : Nat} (hr : r + 1 < tr.height T_ACCT) (ha : tr.cell T_ACCT r act = 1)
    (h1 : tr.cell T_ACCT r lo8 = 1) (h0 : tr.cell T_ACCT (r + 1) lo8 = 0) :
    tr.cell T_ACCT r i = 7 := by
  have h := con hL (by omega : r < _) (e := .mul (mul3 (c act) (c lo8) (Dsl.not (n lo8))) (sub (c i) (k 7)))
    (by simp [Acct.constraints])
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_k, nxt hr] at h
  rw [ha, h1, h0] at h; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height T_ACCT) (hl : tr.cell T_ACCT r al = 1)
    (ha : tr.cell T_ACCT (r + 1) act = 1) : tr.cell T_ACCT (r + 1) af = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c al) (n act) (Dsl.not (n af))) (by simp [Acct.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height T_ACCT) (ha : tr.cell T_ACCT r act = 0) :
    tr.cell T_ACCT (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (by simp [Acct.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height T_ACCT by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height T_ACCT) : tr.cell T_ACCT 0 af = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c af))) (by simp [Acct.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height T_ACCT) (ha : tr.cell T_ACCT (tr.height T_ACCT - 1) act = 1) :
    tr.cell T_ACCT (tr.height T_ACCT - 1) al = 1 := by
  have h1 := con hL (by omega : tr.height T_ACCT - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c al)))) (by simp [Acct.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height T_ACCT - 1 + 1 = tr.height T_ACCT by omega)] at h1
  rw [ha] at h1; grind

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

def isOne (tr : Trace Fp) (x : Nat) (r : Nat) : Bool := decide (tr.cell T_ACCT r x = 1)

theorem zero_of_not_one (hL : TableLocal Acct.table tr T_ACCT pub) {r : Nat}
    (hr : r < tr.height T_ACCT) {x : Nat} (hx : x ∈ [act, af, al, lo8, gS]) (h : isOne tr x r = false) :
    tr.cell T_ACCT r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem segFacts (hL : TableLocal Acct.table tr T_ACCT pub) :
    SegFacts (tr.height T_ACCT) (isOne tr act) (isOne tr af) (isOne tr al) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).1 h).1
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.1 h).1
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) (by simp) hl)
    simp [isOne, this.1, this.2.1]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact nextSeg hL hr hl ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp) ha)
    simp [isOne, this]
  start h0 := by simp [isOne, row0 hL h0]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le (hL : TableLocal Acct.table tr T_ACCT pub) : tr.height T_ACCT ≤ 2 ^ 12 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_pos : 0 < tr.height T_ACCT := by unfold Trace.height; exact Nat.two_pow_pos _

/-- `Σ_{j' < j} (255 − amt(s + j'))` as a field element. -/
def dsumF (tr : Trace Fp) (s : Nat) : Nat → Fp
  | 0 => 0
  | j + 1 => dsumF tr s j + (255 - tr.cell T_ACCT (s + j) amt)

theorem segInfo (hL : TableLocal Acct.table tr T_ACCT pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr af) (isOne tr al) s ℓ) (hH : s + ℓ ≤ tr.height T_ACCT) :
    ℓ = 16 ∧
    (∀ j, j < 16 → tr.cell T_ACCT (s + j) act = 1 ∧ tr.cell T_ACCT (s + j) i = ((j : Nat) : Fp) ∧
      tr.cell T_ACCT (s + j) kk = tr.cell T_ACCT s kk ∧ tr.cell T_ACCT (s + j) tlast = tr.cell T_ACCT s tlast ∧
      tr.cell T_ACCT (s + j) lo8 = (if j < 8 then 1 else 0) ∧
      tr.cell T_ACCT (s + j) dsum = dsumF tr s (j + 1)) ∧
    tr.cell T_ACCT (s + 15) dsum * tr.cell T_ACCT (s + 15) inv = 1 := by
  have hP : tr.height T_ACCT < P := by have := height_le hL; unfold P; omega
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have haf : tr.cell T_ACCT s af = 1 := by simpa [isOne] using hfs
  have hal : tr.cell T_ACCT (s + ℓ - 1) al = 1 := by simpa [isOne] using hle
  have hA : ∀ j, j < ℓ → tr.cell T_ACCT (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell T_ACCT (s + j) al = 0 := fun j hj =>
    zero_of_not_one hL (by omega) (by simp) (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hs := (rowFacts hL (by omega : s < _)).1 haf
  have he := (rowFacts hL (by omega : s + ℓ - 1 < _)).2.1 hal
  have hi := counter_of (f := fun q => tr.cell T_ACCT q i) (s := s) (ℓ := ℓ) (v0 := 0)
    hs.2.1 (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have h16 : ℓ = 16 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [he.2.1, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    have := ofNat_inj (a := 15) (b := ℓ - 1) (by unfold P; omega) (by omega) e
    omega
  subst h16
  have hk := const_of (f := fun q => tr.cell T_ACCT q kk) (s := s) (ℓ := 16) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have htl := const_of (f := fun q => tr.cell T_ACCT q tlast) (s := s) (ℓ := 16) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.2.1; rwa [show s + (q - s) = q by omega] at this)
  -- lo8 is boolean, starts at 1, ends at 0, never goes 0 → 1, and drops only at lane 7
  have hlb : ∀ j, j < 16 → tr.cell T_ACCT (s + j) lo8 = 0 ∨ tr.cell T_ACCT (s + j) lo8 = 1 :=
    fun j hj => isBool hL (by omega) (by simp)
  have hmono : ∀ j, j + 1 < 16 → tr.cell T_ACCT (s + j) lo8 = 0 → tr.cell T_ACCT (s + j + 1) lo8 = 0 := by
    intro j hj h0
    rcases hlb (j + 1) hj with h | h
    · rwa [show s + (j + 1) = s + j + 1 by omega] at h
    · rw [show s + (j + 1) = s + j + 1 by omega] at h
      have := (hw j hj).2.2.2.2.2.1 h; rw [this] at h0; exact absurd h0 fp_one_ne_zero
  have hdrop : ∀ j, j + 1 < 16 → tr.cell T_ACCT (s + j) lo8 = 1 → tr.cell T_ACCT (s + j + 1) lo8 = 0 → j = 7 := by
    intro j hj h1 h0
    have := switch hL (r := s + j) (by omega) (hA j (by omega)) h1 h0
    have e := hi (s + j) (by omega) (by omega)
    rw [this, show 0 + (s + j - s) = j by omega] at e
    exact (ofNat_inj (a := 7) (b := j) (by unfold P; omega) (by unfold P; omega) e).symm
  have hlo : ∀ j, j < 16 → tr.cell T_ACCT (s + j) lo8 = (if j < 8 then 1 else 0) := by
    -- lanes 0..7 are 1 (going backwards a 1 at lane j>0 forces lane j-1 = 1; lane 0 is 1),
    -- lanes 8..15 are 0
    have up : ∀ j, j < 8 → tr.cell T_ACCT (s + j) lo8 = 1 := by
      intro j
      induction j with
      | zero => intro _; simpa using hs.2.2.1
      | succ j ih =>
        intro hj
        rcases hlb (j + 1) (by omega) with h | h
        · exfalso
          have := hdrop j (by omega) (ih (by omega)) (by rwa [show s + (j + 1) = s + j + 1 by omega] at h)
          omega
        · exact h
    have l8 : tr.cell T_ACCT (s + 8) lo8 = 0 := by
      rcases hlb 8 (by omega) with h | h
      · exact h
      · exfalso
        -- then lanes 8..15 would all be 1 (no drop after 7), contradicting lane 15 = 0
        have : ∀ j, 8 ≤ j → j < 16 → tr.cell T_ACCT (s + j) lo8 = 1 := by
          intro j hj1 hj2
          induction j with
          | zero => omega
          | succ j ih =>
            rcases Nat.lt_or_ge j 8 with h' | h'
            · have : j = 7 := by omega
              subst this; exact h
            · rcases hlb (j + 1) hj2 with h0 | h0
              · exfalso
                have := hdrop j (by omega) (ih h' (by omega))
                  (by rwa [show s + (j + 1) = s + j + 1 by omega] at h0)
                omega
              · exact h0
        have := this 15 (by omega) (by omega)
        rw [show s + 15 = s + 16 - 1 by omega, he.2.2.1] at this
        exact fp_zero_ne_one this
    have down : ∀ j, 8 ≤ j → j < 16 → tr.cell T_ACCT (s + j) lo8 = 0 := by
      intro j hj1 hj2
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_or_ge j 8 with h' | h'
        · have : j = 7 := by omega
          subst this; exact l8
        · have := hmono j (by omega) (ih h' (by omega))
          rwa [show s + j + 1 = s + (j + 1) by omega] at this
    intro j hj
    by_cases h8 : j < 8
    · rw [if_pos h8]; exact up j h8
    · rw [if_neg h8]; exact down j (by omega) hj
  have hds : ∀ j, j < 16 → tr.cell T_ACCT (s + j) dsum = dsumF tr s (j + 1) := by
    intro j
    induction j with
    | zero => intro _; simp only [dsumF, Nat.add_zero]; rw [hs.2.2.2]; grind
    | succ j ih =>
      intro hj
      have := (hw j (by omega)).2.2.2.2.2.2
      rw [show s + j + 1 = s + (j + 1) by omega] at this
      rw [this, ih (by omega)]; rfl
  refine ⟨rfl, fun j hj => ⟨hA j hj, ?_, hk (s + j) (by omega) (by omega), htl (s + j) (by omega) (by omega),
    hlo j hj, hds j hj⟩, ?_⟩
  · have := hi (s + j) (by omega) (by omega); rwa [show 0 + (s + j - s) = j by omega] at this
  · have := he.2.2.2; rwa [show s + 16 - 1 = s + 15 by omega] at this

end ZkFormal.Near.AcctProof
