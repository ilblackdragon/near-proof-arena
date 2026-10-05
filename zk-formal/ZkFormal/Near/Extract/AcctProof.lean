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

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

abbrev cN (tr : Trace Fp) (q x : Nat) : Nat := (tr.cell T_ACCT q x).toNat

theorem flatMap_segs' {α β : Type} {l : List α} {F G : α → List β}
    (h : ∀ x ∈ l, F x = G x) : l.flatMap F = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem List.map_eq_flatMap_singleton_aux {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun x => if True then [f x] else []) = l.map f := by
  induction l <;> simp_all

/-- Pre value byte `p` of the segment at `s` (lane layout of `Tables/Acct.lean`). -/
def valAt (tr : Trace Fp) (amtCol s p : Nat) : Nat :=
  if p < 16 then cN tr (s + p) amtCol
  else if p < 32 then cN tr (s + (p - 16)) lk
  else if p < 64 then (if (p - 32) % 2 = 0 then cN tr (s + (p - 32) / 2) ch0 else cN tr (s + (p - 32) / 2) ch1)
  else cN tr (s + (p - 64)) st

abbrev preAt (tr : Trace Fp) (s p : Nat) : Nat := valAt tr amt s p

def acctOfSeg (tr : Trace Fp) (s : Nat) : AcctV :=
  { k := cN tr s kk, tlast := cN tr s tlast, pre := (List.range 72).map (preAt tr s),
    post := (List.range 16).map fun j => cN tr (s + j) post }

/-- Nat messages of lane `j` on BYTES (pre, then post). -/
def laneBytes (tr : Trace Fp) (s j : Nat) (id : Nat) (amtCol : Nat) : List Msg :=
  [[id, j, cN tr (s + j) amtCol], [id, 16 + j, cN tr (s + j) lk], [id, 32 + 2 * j, cN tr (s + j) ch0],
   [id, 33 + 2 * j, cN tr (s + j) ch1]] ++ (if j < 8 then [[id, 64 + j, cN tr (s + j) st]] else [])

theorem emit_perm (s id amtCol : Nat) :
    ((List.range 16).flatMap fun j => laneBytes tr s j id amtCol).Perm
      (emitAt id 0 ((List.range 72).map (valAt tr amtCol s))) := by
  -- the four parts of the value
  let a := fun j => ([id, j, cN tr (s + j) amtCol] : Msg)
  let l := fun j => ([id, 16 + j, cN tr (s + j) lk] : Msg)
  let cc := fun j => ([[id, 32 + 2 * j, cN tr (s + j) ch0], [id, 33 + 2 * j, cN tr (s + j) ch1]] : List Msg)
  let so := fun j => (if j < 8 then [[id, 64 + j, cN tr (s + j) st]] else [] : List Msg)
  have hl : ∀ j, laneBytes tr s j id amtCol = [a j] ++ ([l j] ++ (cc j ++ so j)) := fun j => rfl
  have p1 : ((List.range 16).flatMap fun j => laneBytes tr s j id amtCol).Perm
      ((List.range 16).map a ++ ((List.range 16).map l ++ ((List.range 16).flatMap cc ++
        (List.range 16).flatMap so))) := by
    simp only [hl]
    refine (flatMap_append_perm _ _ _).trans ?_
    rw [← map_eq_flatMap]
    apply List.Perm.append_left
    refine (flatMap_append_perm _ _ _).trans ?_
    rw [← map_eq_flatMap]
    apply List.Perm.append_left
    exact flatMap_append_perm _ _ _
  refine p1.trans (List.Perm.of_eq ?_)
  have hg : ∀ p, p < 72 → ((List.range 72).map (valAt tr amtCol s)).getD p 0 = valAt tr amtCol s p := by
    intro p hp; simp [List.getD_eq_getElem?_getD, List.getElem?_range hp]
  have hlen : ((List.range 72).map (valAt tr amtCol s)).length = 72 := by simp
  generalize ((List.range 72).map (valAt tr amtCol s)) = pre at hg hlen
  have hr : List.range 72 = List.range' 0 16 ++ (List.range' 16 16 ++ (List.range' 32 (2 * 16) ++
      List.range' 64 8)) := by decide
  unfold emitAt
  rw [hlen, hr]
  simp only [List.map_append]
  have e1 : (List.range' 0 16).map (fun p => ([id, 0 + p, pre.getD p 0] : Msg)) = (List.range 16).map a := by
    rw [List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp, a, Nat.zero_add]
    rw [hg j (by omega)]; simp [valAt, show j < 16 from hj]
  have e2 : (List.range' 16 16).map (fun p => ([id, 0 + p, pre.getD p 0] : Msg)) = (List.range 16).map l := by
    rw [List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp, l, Nat.zero_add]
    rw [hg (16 + j) (by omega)]
    simp [valAt, show ¬ (16 + j < 16) by omega, show 16 + j < 32 by omega]
  have e3 : (List.range' 32 (2 * 16)).map (fun p => ([id, 0 + p, pre.getD p 0] : Msg)) =
      (List.range 16).flatMap cc := by
    rw [range'_flatMap_pairs, List.map_flatMap]
    apply flatMap_segs' ; intro j hj; rw [List.mem_range] at hj
    simp only [List.map_cons, List.map_nil, cc, Nat.zero_add]
    rw [hg (32 + 2 * j) (by omega), hg (32 + 2 * j + 1) (by omega),
      show 32 + 2 * j + 1 = 33 + 2 * j by omega]
    simp [valAt, show ¬ (32 + 2 * j < 16) by omega, show ¬ (32 + 2 * j < 32) by omega,
      show 32 + 2 * j < 64 by omega, show ¬ (33 + 2 * j < 16) by omega,
      show ¬ (33 + 2 * j < 32) by omega, show 33 + 2 * j < 64 by omega,
      show (32 + 2 * j - 32) % 2 = 0 by omega, show (33 + 2 * j - 32) % 2 = 1 by omega,
      show (32 + 2 * j - 32) / 2 = j by omega, show (33 + 2 * j - 32) / 2 = j by omega]
  have e4 : (List.range' 64 8).map (fun p => ([id, 0 + p, pre.getD p 0] : Msg)) =
      (List.range 16).flatMap so := by
    have h16 : List.range 16 = List.range' 0 8 ++ List.range' 8 8 := by decide
    rw [h16, List.flatMap_append, flatMap_range'_nil so 8 8 (fun j hj => by simp [so]),
      List.append_nil, flatMap_range'_single so (fun j => [id, 64 + j, cN tr (s + j) st]) 0 8
        (fun j hj => by simp [so, hj]), List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp, Nat.zero_add]
    rw [hg (64 + j) (by omega)]
    simp [valAt, show ¬ (64 + j < 16) by omega, show ¬ (64 + j < 32) by omega, show ¬ (64 + j < 64) by omega]
  rw [e1, e2, e3, e4]

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

theorem post_list (s : Nat) :
    (acctOfSeg tr s).post ++ (acctOfSeg tr s).pre.drop 16 = (List.range 72).map (valAt tr post s) := by
  apply List.ext_getElem
  · simp [acctOfSeg]
  · intro p h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases hp : p < 16
    · rw [List.getElem_append_left (by simp [acctOfSeg]; omega)]
      simp [acctOfSeg, valAt, hp]
    · rw [List.getElem_append_right (by simp [acctOfSeg]; omega)]
      simp [acctOfSeg, valAt, hp, show 16 + (p - 16) = p by omega]

theorem multNat1 (e : Expr) (q : Nat) :
    Interaction.multNat.go tr T_ACCT q pub [e] 0 = if e.eval tr T_ACCT q pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr T_ACCT q pub = 1 <;> simp [h]

/-- Nat messages a row sends on BYTES. -/
def rowBytesN (tr : Trace Fp) (q : Nat) (lane : Nat) (lo : Bool) : List Msg :=
  let k := cN tr q kk
  let one (id pos x : Nat) : Msg := [id, pos, cN tr q x]
  [one (msgId K_VPRE k) lane amt, one (msgId K_VPRE k) (16 + lane) lk, one (msgId K_VPRE k) (32 + 2 * lane) ch0,
    one (msgId K_VPRE k) (33 + 2 * lane) ch1] ++
  (if lo then [one (msgId K_VPRE k) (64 + lane) st] else []) ++
  [one (msgId K_VPOST k) lane post, one (msgId K_VPOST k) (16 + lane) lk, one (msgId K_VPOST k) (32 + 2 * lane) ch0,
    one (msgId K_VPOST k) (33 + 2 * lane) ch1] ++
  (if lo then [one (msgId K_VPOST k) (64 + lane) st] else [])

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

theorem fpN (a : Fp) : Fp.ofNat a.toNat = a := Fp.ofNat_toNat a

theorem castAdd (x : Nat) (a : Fp) (h : a = ((x : Nat) : Fp)) (y : Nat) :
    (y : Fp) + a = ((y + x : Nat) : Fp) := by rw [h, natCast_add]

theorem rowT_bytes (q j : Nat) (hj : j < 16) (ha : tr.cell T_ACCT q act = 1) (hi : tr.cell T_ACCT q i = ((j : Nat) : Fp))
    (hg : tr.cell T_ACCT q gS = if j < 8 then 1 else 0) :
    rowTraffic Acct.interactions tr T_ACCT q pub B_BYTES true = (rowBytesN tr q j (decide (j < 8))).map Msg.toFp := by
  simp only [rowTraffic, Acct.interactions, Acct.vbytes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Dsl.send, Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, eval_c, eval_add, eval_k,
    eval_smul, eval_mid, ha, hg]
  rw [natCast_eq] at hi
  have hjP : j % P = j := Nat.mod_eq_of_lt (by unfold P; omega)
  by_cases h8 : j < 8 <;>
  simp [h8, rowBytesN, Msg.toFp, msgId, B_BYTES, B_MEM, B_VSLOT, natCast_eq, fpN, hi, Fp.toNat_ofNat, hjP]

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

def memN (tr : Trace Fp) (q j : Nat) (t amtCol : Nat) : Msg :=
  [cN tr q kk, t, j, cN tr q amtCol, cN tr q lk, cN tr q st]

theorem rowT_other (q j : Nat) (hj : j < 16) (ha : tr.cell T_ACCT q act = 1)
    (hi : tr.cell T_ACCT q i = ((j : Nat) : Fp)) (b : Nat) (sd : Bool) (hb : ¬ (b = B_BYTES ∧ sd = true)) :
    rowTraffic Acct.interactions tr T_ACCT q pub b sd =
      (if b = B_MEM ∧ sd = true then [(memN tr q j 0 amt).map Fp.ofNat] else []) ++
      (if b = B_MEM ∧ sd = false then [(memN tr q j (cN tr q tlast) post).map Fp.ofNat] else []) ++
      (if b = B_VSLOT ∧ sd = true ∧ tr.cell T_ACCT q af = 1 then [[tr.cell T_ACCT q kk]] else []) := by
  rw [natCast_eq] at hi
  have hjP : j % P = j := Nat.mod_eq_of_lt (by unfold P; omega)
  simp only [rowTraffic, Acct.interactions, Acct.vbytes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Dsl.send, Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, eval_c, eval_k, ha]
  by_cases h1 : b = B_BYTES
  · subst h1
    have : sd = false := by cases sd <;> simp_all
    subst this
    simp [B_BYTES, B_MEM, B_VSLOT]
  · by_cases h2 : b = B_MEM
    · subst h2; cases sd <;> simp [B_BYTES, B_MEM, B_VSLOT, memN, fpN, hi, Fp.toNat_ofNat, hjP] <;> rfl
    · by_cases h3 : b = B_VSLOT
      · subst h3; cases sd <;> simp [B_BYTES, B_MEM, B_VSLOT]
        split <;> simp_all [eq_comm]
      · simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near
theorem perm_flatMap_congr {α β : Type} (l : List α) (F G : α → List β) (h : ∀ x ∈ l, (F x).Perm (G x)) :
    (l.flatMap F).Perm (l.flatMap G) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
end ZkFormal.Near

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

theorem acctSends_flat (as : List AcctV) (b : Nat) : acctSends as b = as.flatMap fun a => acctSends [a] b := by
  unfold acctSends; split
  · simp
  · split
    · simp
    · split
      · simp [map_eq_flatMap]
      · simp

theorem acctRecvs_flat (as : List AcctV) (b : Nat) : acctRecvs as b = as.flatMap fun a => acctRecvs [a] b := by
  unfold acctRecvs; split <;> simp

/-- One segment's traffic, up to permutation. -/
theorem segTraffic (hL : TableLocal Acct.table tr T_ACCT pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr af) (isOne tr al) s ℓ) (hH : s + ℓ ≤ tr.height T_ACCT)
    (b : Nat) (sd : Bool) :
    ((List.range' s ℓ).flatMap fun q => rowTraffic Acct.interactions tr T_ACCT q pub b sd).Perm
      ((if sd then acctSends [acctOfSeg tr s] b else acctRecvs [acctOfSeg tr s] b).map Msg.toFp) := by
  obtain ⟨h16, hrow, -⟩ := segInfo hL hseg hH
  subst h16
  have hfs : tr.cell T_ACCT s af = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hgS : ∀ j, j < 16 → tr.cell T_ACCT (s + j) gS = if j < 8 then 1 else 0 := fun j hj => by
    rw [(rowFacts hL (by omega : s + j < _)).2.2.2, (hrow j hj).1, (hrow j hj).2.2.2.2.1]; split <;> grind
  have hst : ∀ j, j < 16 → ¬ j < 8 → tr.cell T_ACCT (s + j) st = 0 := fun j hj h8 =>
    (rowFacts hL (by omega : s + j < _)).2.2.1 (by rw [(hrow j hj).2.2.2.2.1, if_neg h8])
  have hk : ∀ j, j < 16 → cN tr (s + j) kk = cN tr s kk := fun j hj => by
    show (tr.cell T_ACCT (s + j) kk).toNat = _; rw [(hrow j hj).2.2.1]
  have htl : ∀ j, j < 16 → cN tr (s + j) tlast = cN tr s tlast := fun j hj => by
    show (tr.cell T_ACCT (s + j) tlast).toNat = _; rw [(hrow j hj).2.2.2.1]
  have hl0 : ∀ j, 0 < j → j < 16 → tr.cell T_ACCT (s + j) af = 0 := fun j h0 hj =>
    zero_of_not_one hL (by omega) (by simp) (hseg.2.2.2.2.1 (s + j) (by omega) (by omega))
  rw [List.range'_eq_map_range, List.flatMap_map]
  by_cases hB : b = B_BYTES ∧ sd = true
  · obtain ⟨rfl, rfl⟩ := hB
    rw [flatMap_segs' (G := fun j => (rowBytesN tr (s + j) j (decide (j < 8))).map Msg.toFp)
      (fun j hj => rowT_bytes (s + j) j (List.mem_range.mp hj) (hrow j (List.mem_range.mp hj)).1
        (hrow j (List.mem_range.mp hj)).2.1 (hgS j (List.mem_range.mp hj))), ← List.map_flatMap]
    simp only [if_true, acctSends, if_pos rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply List.Perm.map
    -- each row = pre lane ++ post lane
    have hrowsplit : ∀ j ∈ List.range 16, rowBytesN tr (s + j) j (decide (j < 8)) =
        laneBytes tr s j (msgId K_VPRE (cN tr s kk)) amt ++ laneBytes tr s j (msgId K_VPOST (cN tr s kk)) post := by
      intro j hj; rw [List.mem_range] at hj
      simp only [rowBytesN, laneBytes, hk j hj]
      by_cases h8 : j < 8 <;> simp [h8]
    rw [flatMap_segs' hrowsplit]
    refine (flatMap_append_perm _ _ _).trans (List.Perm.append (emit_perm s _ amt) ?_)
    rw [post_list]; exact emit_perm s _ post
  · apply List.Perm.of_eq
    rw [flatMap_segs' (G := fun j =>
      (if b = B_MEM ∧ sd = true then [(memN tr (s + j) j 0 amt).map Fp.ofNat] else []) ++
      (if b = B_MEM ∧ sd = false then [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] else []) ++
      (if b = B_VSLOT ∧ sd = true ∧ tr.cell T_ACCT (s + j) af = 1 then [[tr.cell T_ACCT (s + j) kk]] else []))
      (fun j hj => rowT_other (s + j) j (List.mem_range.mp hj) (hrow j (List.mem_range.mp hj)).1
        (hrow j (List.mem_range.mp hj)).2.1 b sd hB)]
    have hpre : ∀ p, p < 72 → (acctOfSeg tr s).pre.getD p 0 = preAt tr s p := fun p hp => by
      simp [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_range hp]
    have hpost : ∀ j, j < 16 → (acctOfSeg tr s).post.getD j 0 = cN tr (s + j) post := fun j hj => by
      simp [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_range hj]
    have hlane : ∀ (amtCol : Nat) (col : List Nat), (∀ j, j < 16 → col.getD j 0 = cN tr (s + j) amtCol) →
        ∀ j, j < 16 → acctLane (acctOfSeg tr s) col j = [cN tr (s + j) amtCol, cN tr (s + j) lk, cN tr (s + j) st] := by
      intro amtCol col hcol j hj
      simp only [acctLane, hcol j hj, hpre (16 + j) (by omega), preAt, valAt]
      by_cases h8 : j < 8
      · rw [if_pos h8, hpre (64 + j) (by omega)]
        simp [valAt, show ¬ (16 + j < 16) by omega, show 16 + j < 32 by omega, show ¬ (64 + j < 16) by omega,
          show ¬ (64 + j < 32) by omega, show ¬ (64 + j < 64) by omega]
      · rw [if_neg h8, show cN tr (s + j) st = 0 by simp [cN, hst j hj h8, Fp.toNat_zero]]
        simp [show ¬ (16 + j < 16) by omega, show 16 + j < 32 by omega]
    by_cases hM : b = B_MEM
    · subst hM
      cases sd
      · have hf : (fun j =>
            (if B_MEM = B_MEM ∧ false = true then [(memN tr (s + j) j 0 amt).map Fp.ofNat] else []) ++
            (if B_MEM = B_MEM ∧ false = false then
              [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] else []) ++
            (if B_MEM = B_VSLOT ∧ false = true ∧ tr.cell T_ACCT (s + j) af = 1 then
              [[tr.cell T_ACCT (s + j) kk]] else [])) =
            fun j => [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] := by
          funext j; simp
        rw [hf, ← map_eq_flatMap]
        simp only [Bool.false_eq_true, if_false, acctRecvs, if_pos rfl, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.map_map]
        simp only [ite_true, List.map_map]
        apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
        simp only [Function.comp, Msg.toFp, memN, hk j hj, htl j hj]
        rw [hlane post (acctOfSeg tr s).post hpost j hj]; simp [acctOfSeg]
      · have hf : (fun j =>
            (if B_MEM = B_MEM ∧ true = true then [(memN tr (s + j) j 0 amt).map Fp.ofNat] else []) ++
            (if B_MEM = B_MEM ∧ true = false then
              [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] else []) ++
            (if B_MEM = B_VSLOT ∧ true = true ∧ tr.cell T_ACCT (s + j) af = 1 then
              [[tr.cell T_ACCT (s + j) kk]] else [])) =
            fun j => [(memN tr (s + j) j 0 amt).map Fp.ofNat] := by
          funext j; simp [B_MEM, B_VSLOT]
        rw [hf, ← map_eq_flatMap]
        simp only [if_true, acctSends, show ¬ (B_MEM = B_BYTES) by decide, if_false, if_pos rfl,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
        try simp only [ite_true, List.map_map]
        apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
        simp only [Function.comp, Msg.toFp, memN, hk j hj]
        rw [hlane amt (acctOfSeg tr s).pre (fun j hj => by rw [hpre j (by omega)]; simp [valAt, hj]) j hj]
        simp [acctOfSeg]
    · by_cases hV : b = B_VSLOT ∧ sd = true
      · obtain ⟨rfl, rfl⟩ := hV
        have hf : (fun j =>
            (if B_VSLOT = B_MEM ∧ true = true then [(memN tr (s + j) j 0 amt).map Fp.ofNat] else []) ++
            (if B_VSLOT = B_MEM ∧ true = false then
              [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] else []) ++
            (if B_VSLOT = B_VSLOT ∧ true = true ∧ tr.cell T_ACCT (s + j) af = 1 then
              [[tr.cell T_ACCT (s + j) kk]] else [])) =
            fun j => if tr.cell T_ACCT (s + j) af = 1 then [[tr.cell T_ACCT (s + j) kk]] else [] := by
          funext j; simp [B_MEM, B_VSLOT]
        rw [hf]
        have h16 : List.range 16 = [0] ++ List.range' 1 15 := by decide
        rw [h16, List.flatMap_append, List.flatMap_singleton, Nat.add_zero, if_pos hfs,
          flatMap_range'_nil _ 1 15 (fun j hj => by
            rw [if_neg (by rw [hl0 (1 + j) (by omega) (by omega)]; exact fp_zero_ne_one)])]
        simp [acctSends, B_VSLOT, B_MEM, B_BYTES, Msg.toFp, acctOfSeg, fpN]
      · have hf : (fun j =>
            (if b = B_MEM ∧ sd = true then [(memN tr (s + j) j 0 amt).map Fp.ofNat] else []) ++
            (if b = B_MEM ∧ sd = false then
              [(memN tr (s + j) j (cN tr (s + j) tlast) post).map Fp.ofNat] else []) ++
            (if b = B_VSLOT ∧ sd = true ∧ tr.cell T_ACCT (s + j) af = 1 then
              [[tr.cell T_ACCT (s + j) kk]] else [])) = fun _ => [] := by
          funext j
          rw [if_neg (fun h => hM h.1), if_neg (fun h => hM h.1), if_neg (fun h => hV ⟨h.1, h.2.1⟩)]; rfl
        rw [hf, flatMap_nil_fun]
        cases sd
        · simp [acctRecvs, hM]
        · have : b ≠ B_BYTES := fun h => hB ⟨h, rfl⟩
          have : b ≠ B_VSLOT := fun h => hV ⟨h, rfl⟩
          simp [acctSends, hM, *]

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near.AcctProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp}

theorem dsumF_zero (s : Nat) (h : ∀ j, j < 16 → tr.cell T_ACCT (s + j) amt = 255) :
    ∀ j, j ≤ 16 → dsumF tr s j = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih => intro hj; simp only [dsumF]; rw [ih (by omega), h j (by omega)]; grind

theorem notMax (hL : TableLocal Acct.table tr T_ACCT pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr af) (isOne tr al) s ℓ) (hH : s + ℓ ≤ tr.height T_ACCT) :
    (∀ j, j < 16 → (acctOfSeg tr s).pre.getD j 0 < 256) →
      ∃ j, j < 16 ∧ (acctOfSeg tr s).pre.getD j 0 ≠ 255 := by
  intro _
  obtain ⟨h16, hrow, hinv⟩ := segInfo hL hseg hH
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ j, j < 16 → tr.cell T_ACCT (s + j) amt = 255 := by
    intro j hj
    have : (acctOfSeg tr s).pre.getD j 0 = 255 := Classical.byContradiction fun h => hne ⟨j, hj, h⟩
    simp only [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : j < 72),
      Option.map_some, Option.getD_some, valAt, if_pos hj] at this
    have h' : (tr.cell T_ACCT (s + j) amt).toNat = 255 := this
    rw [← Fp.ofNat_toNat (tr.cell T_ACCT (s + j) amt), h']; rfl
  have := (hrow 15 (by omega)).2.2.2.2.2
  rw [this, dsumF_zero s hall 16 (by omega)] at hinv
  grind

end ZkFormal.Near.AcctProof

namespace ZkFormal.Near
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Acct AcctProof

/-- **The acct table's view.** -/
theorem acct_view : AcctViewStmt := by
  intro tr pub hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) height_pos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height T_ACCT := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height T_ACCT →
      rowTraffic Acct.interactions tr T_ACCT q pub b sd = [] := by
    intro b sd q h1 h2
    have ha := zero_of_not_one hL h2 (by simp) (hpad q h1 h2)
    have hf : tr.cell T_ACCT q af = 0 := by
      rcases isBool hL h2 (x := af) (by simp) with h | h
      · exact h
      · have := ((rowFacts hL h2).1 h).1; rw [ha] at this; exact absurd this fp_zero_ne_one
    have hg : tr.cell T_ACCT q gS = 0 := by rw [(rowFacts hL h2).2.2.2, ha]; grind
    simp only [rowTraffic, Acct.interactions, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, multNat1, eval_c, ha, hf, hg]
    simp
  refine ⟨segs.map fun p => acctOfSeg tr p.1, ⟨?_, ?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro h
    rw [List.map_eq_nil_iff] at h
    subst h
    have := hpad 0 (by simp [segEnd]) height_pos
    have h0 := ((rowFacts hL height_pos).1 (row0 hL height_pos)).1
    simp [isOne, h0] at this
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨p, -, rfl⟩ := ha
    exact ⟨by simp [acctOfSeg], by simp [acctOfSeg], Fp.toNat_lt _, Fp.toNat_lt _⟩
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact notMax hL (hall p hp) (hH p hp)
  · intro a ha x hx
    simp only [List.mem_map] at ha
    obtain ⟨p, -, rfl⟩ := ha
    simp only [acctOfSeg, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
    · simp only [preAt, valAt]; split
      · exact Fp.toNat_lt _
      · split
        · exact Fp.toNat_lt _
        · split
          · split <;> exact Fp.toNat_lt _
          · exact Fp.toNat_lt _
    · exact Fp.toNat_lt _
  · simp only [acctTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT b true)]
    refine List.Perm.count_eq ?_ m
    rw [acctSends_flat, List.map_flatMap, List.flatMap_map]
    exact perm_flatMap_congr _ _ _ (fun p hp => by
      have := segTraffic hL (hall p hp) (hH p hp) b true; simpa using this)
  · simp only [acctTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT b false)]
    refine List.Perm.count_eq ?_ m
    rw [acctRecvs_flat, List.map_flatMap, List.flatMap_map]
    exact perm_flatMap_congr _ _ _ (fun p hp => by
      have := segTraffic hL (hall p hp) (hH p hp) b false; simpa using this)

end ZkFormal.Near
