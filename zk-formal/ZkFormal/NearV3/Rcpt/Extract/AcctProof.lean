import ZkFormal.Near.Extract.AcctProof
import ZkFormal.NearV3.Rcpt.Tables.Acct

/-!
# ZkFormal.NearV3.Rcpt.Extract.AcctProof — the `acctV3` view (`AcctV3ViewStmt`, `acctV3_view`)

The constraints of `acctV3` are v1 `acct`'s verbatim, so the row and segment facts are v1's
(`Near/Extract/AcctProof.lean`) with the table index generalised (`tt`) and the height bound
`2^17`.  The view is v1's `AcctV` per 16-row segment.  Traffic (up to permutation inside a
segment, as v1): the pre value on `VBYTES (vid, p, pre_p)` (72), the post value on
`BYTES (VPOST(vid), p, post_p)` (72), `MEM` open / close as v1, `VSLOT (vid)` once.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure AcctV3Wf (as : List AcctV) : Prop where
  v1 : AcctWf as
  rows : 16 * as.length ≤ 2 ^ AcctV3.maxLog

def acctV3Sends (as : List AcctV) (b : Nat) : List Msg :=
  if b = B_VBYTES then as.flatMap fun a => emitAt a.k 0 a.pre
  else if b = B_BYTES then as.flatMap fun a => emitAt (msgId K_VPOST a.k) 0 (a.post ++ a.pre.drop 16)
  else if b = B_MEM then
    as.flatMap fun a => (List.range 16).map fun i => [a.k, 0, i] ++ acctLane a a.pre i
  else if b = B_VSLOT then as.map fun a => [a.k]
  else []

/-- Receives: v1's (`MEM` closing reads). -/
def acctV3Traffic (as : List AcctV) : Traffic := ⟨acctV3Sends as, acctRecvs as⟩

/-- **The `acctV3` view statement.** -/
def AcctV3ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal AcctV3.table tr t pub →
    ∃ as, AcctV3Wf as ∧ TableTraffic AcctV3.interactions tr t pub (acctV3Traffic as)

/-- The `VBYTES` messages of a value in `valV3`'s receive format. -/
theorem emitAt_zero (vid : Nat) (bytes : List Nat) :
    emitAt vid 0 bytes = (List.range bytes.length).map fun p => [vid, p, bytes.getD p 0] := by
  simp [emitAt]

end ZkFormal.NearV3

namespace ZkFormal.NearV3.AcctV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal AcctV3.table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ Acct.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 :=
  Nat.mod_eq_of_lt h

variable (hL : TableLocal AcctV3.table tr tt pub)
include hL

theorem isBool {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ [act, af, al, lo8, gS]) :
    tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold Acct.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem hx))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r af = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r i = 0 ∧
      tr.cell tt r lo8 = 1 ∧ tr.cell tt r dsum = 255 - tr.cell tt r amt) ∧
    (tr.cell tt r al = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r i = 15 ∧
      tr.cell tt r lo8 = 0 ∧ tr.cell tt r dsum * tr.cell tt r inv = 1) ∧
    (tr.cell tt r lo8 = 0 → tr.cell tt r st = 0) ∧
    tr.cell tt r gS = tr.cell tt r act * tr.cell tt r lo8 := by
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

theorem within {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt r act = 1) (hl : tr.cell tt r al = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) af = 0 ∧
    tr.cell tt (r + 1) kk = tr.cell tt r kk ∧ tr.cell tt (r + 1) tlast = tr.cell tt r tlast ∧
    tr.cell tt (r + 1) i = tr.cell tt r i + 1 ∧
    (tr.cell tt (r + 1) lo8 = 1 → tr.cell tt r lo8 = 1) ∧
    tr.cell tt (r + 1) dsum = tr.cell tt r dsum + (255 - tr.cell tt (r + 1) amt) := by
  have hr' : r < tr.height tt := by omega
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

theorem switch {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (h1 : tr.cell tt r lo8 = 1) (h0 : tr.cell tt (r + 1) lo8 = 0) :
    tr.cell tt r i = 7 := by
  have h := con hL (by omega : r < _) (e := .mul (mul3 (c act) (c lo8) (Dsl.not (n lo8))) (sub (c i) (k 7)))
    (by simp [Acct.constraints])
  simp only [eval_mul3, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_k, nxt hr] at h
  rw [ha, h1, h0] at h; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r al = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) af = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c al) (n act) (Dsl.not (n af))) (by simp [Acct.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (by simp [Acct.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 af = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c af))) (by simp [Acct.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) al = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c al)))) (by simp [Acct.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def isOne (tr : Trace Fp) (tt : Nat) (x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem zero_of_not_one (hL : TableLocal AcctV3.table tr tt pub) {r : Nat}
    (hr : r < tr.height tt) {x : Nat} (hx : x ∈ [act, af, al, lo8, gS]) (h : isOne tr tt x r = false) :
    tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem segFacts (hL : TableLocal AcctV3.table tr tt pub) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) where
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

theorem height_le (hL : TableLocal AcctV3.table tr tt pub) : tr.height tt ≤ 2 ^ 17 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_pos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _

/-- `Σ_{j' < j} (255 − amt(s + j'))` as a field element. -/
def dsumF (tr : Trace Fp) (tt : Nat) (s : Nat) : Nat → Fp
  | 0 => 0
  | j + 1 => dsumF tr tt s j + (255 - tr.cell tt (s + j) amt)

theorem segInfo (hL : TableLocal AcctV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 16 ∧
    (∀ j, j < 16 → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) i = ((j : Nat) : Fp) ∧
      tr.cell tt (s + j) kk = tr.cell tt s kk ∧ tr.cell tt (s + j) tlast = tr.cell tt s tlast ∧
      tr.cell tt (s + j) lo8 = (if j < 8 then 1 else 0) ∧
      tr.cell tt (s + j) dsum = dsumF tr tt s (j + 1)) ∧
    tr.cell tt (s + 15) dsum * tr.cell tt (s + 15) inv = 1 := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have haf : tr.cell tt s af = 1 := by simpa [isOne] using hfs
  have hal : tr.cell tt (s + ℓ - 1) al = 1 := by simpa [isOne] using hle
  have hA : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell tt (s + j) al = 0 := fun j hj =>
    zero_of_not_one hL (by omega) (by simp) (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hs := (rowFacts hL (by omega : s < _)).1 haf
  have he := (rowFacts hL (by omega : s + ℓ - 1 < _)).2.1 hal
  have hi := counter_of (f := fun q => tr.cell tt q i) (s := s) (ℓ := ℓ) (v0 := 0)
    hs.2.1 (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have h16 : ℓ = 16 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [he.2.1, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    have := ofNat_inj (a := 15) (b := ℓ - 1) (by unfold P; omega) (by omega) e
    omega
  subst h16
  have hk := const_of (f := fun q => tr.cell tt q kk) (s := s) (ℓ := 16) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have htl := const_of (f := fun q => tr.cell tt q tlast) (s := s) (ℓ := 16) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.2.1; rwa [show s + (q - s) = q by omega] at this)
  -- lo8 is boolean, starts at 1, ends at 0, never goes 0 → 1, and drops only at lane 7
  have hlb : ∀ j, j < 16 → tr.cell tt (s + j) lo8 = 0 ∨ tr.cell tt (s + j) lo8 = 1 :=
    fun j hj => isBool hL (by omega) (by simp)
  have hmono : ∀ j, j + 1 < 16 → tr.cell tt (s + j) lo8 = 0 → tr.cell tt (s + j + 1) lo8 = 0 := by
    intro j hj h0
    rcases hlb (j + 1) hj with h | h
    · rwa [show s + (j + 1) = s + j + 1 by omega] at h
    · rw [show s + (j + 1) = s + j + 1 by omega] at h
      have := (hw j hj).2.2.2.2.2.1 h; rw [this] at h0; exact absurd h0 fp_one_ne_zero
  have hdrop : ∀ j, j + 1 < 16 → tr.cell tt (s + j) lo8 = 1 → tr.cell tt (s + j + 1) lo8 = 0 → j = 7 := by
    intro j hj h1 h0
    have := switch hL (r := s + j) (by omega) (hA j (by omega)) h1 h0
    have e := hi (s + j) (by omega) (by omega)
    rw [this, show 0 + (s + j - s) = j by omega] at e
    exact (ofNat_inj (a := 7) (b := j) (by unfold P; omega) (by unfold P; omega) e).symm
  have hlo : ∀ j, j < 16 → tr.cell tt (s + j) lo8 = (if j < 8 then 1 else 0) := by
    -- lanes 0..7 are 1 (going backwards a 1 at lane j>0 forces lane j-1 = 1; lane 0 is 1),
    -- lanes 8..15 are 0
    have up : ∀ j, j < 8 → tr.cell tt (s + j) lo8 = 1 := by
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
    have l8 : tr.cell tt (s + 8) lo8 = 0 := by
      rcases hlb 8 (by omega) with h | h
      · exact h
      · exfalso
        -- then lanes 8..15 would all be 1 (no drop after 7), contradicting lane 15 = 0
        have : ∀ j, 8 ≤ j → j < 16 → tr.cell tt (s + j) lo8 = 1 := by
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
    have down : ∀ j, 8 ≤ j → j < 16 → tr.cell tt (s + j) lo8 = 0 := by
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
  have hds : ∀ j, j < 16 → tr.cell tt (s + j) dsum = dsumF tr tt s (j + 1) := by
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

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

abbrev cN (tr : Trace Fp) (tt : Nat) (q x : Nat) : Nat := (tr.cell tt q x).toNat

theorem flatMap_segs' {α β : Type} {l : List α} {F G : α → List β}
    (h : ∀ x ∈ l, F x = G x) : l.flatMap F = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem List.map_eq_flatMap_singleton_aux {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun x => if True then [f x] else []) = l.map f := by
  induction l <;> simp_all

/-- Pre value byte `p` of the segment at `s` (lane layout of `Tables/Acct.lean`). -/
def valAt (tr : Trace Fp) (tt : Nat) (amtCol s p : Nat) : Nat :=
  if p < 16 then cN tr tt (s + p) amtCol
  else if p < 32 then cN tr tt (s + (p - 16)) lk
  else if p < 64 then (if (p - 32) % 2 = 0 then cN tr tt (s + (p - 32) / 2) ch0 else cN tr tt (s + (p - 32) / 2) ch1)
  else cN tr tt (s + (p - 64)) st

abbrev preAt (tr : Trace Fp) (tt : Nat) (s p : Nat) : Nat := valAt tr tt amt s p

def acctOfSeg (tr : Trace Fp) (tt : Nat) (s : Nat) : AcctV :=
  { k := cN tr tt s kk, tlast := cN tr tt s tlast, pre := (List.range 72).map (preAt tr tt s),
    post := (List.range 16).map fun j => cN tr tt (s + j) post }

/-- Nat messages of lane `j` on BYTES (pre, then post). -/
def laneBytes (tr : Trace Fp) (tt : Nat) (s j : Nat) (id : Nat) (amtCol : Nat) : List Msg :=
  [[id, j, cN tr tt (s + j) amtCol], [id, 16 + j, cN tr tt (s + j) lk], [id, 32 + 2 * j, cN tr tt (s + j) ch0],
   [id, 33 + 2 * j, cN tr tt (s + j) ch1]] ++ (if j < 8 then [[id, 64 + j, cN tr tt (s + j) st]] else [])

theorem emit_perm (s id amtCol : Nat) :
    ((List.range 16).flatMap fun j => laneBytes tr tt s j id amtCol).Perm
      (emitAt id 0 ((List.range 72).map (valAt tr tt amtCol s))) := by
  -- the four parts of the value
  let a := fun j => ([id, j, cN tr tt (s + j) amtCol] : Msg)
  let l := fun j => ([id, 16 + j, cN tr tt (s + j) lk] : Msg)
  let cc := fun j => ([[id, 32 + 2 * j, cN tr tt (s + j) ch0], [id, 33 + 2 * j, cN tr tt (s + j) ch1]] : List Msg)
  let so := fun j => (if j < 8 then [[id, 64 + j, cN tr tt (s + j) st]] else [] : List Msg)
  have hl : ∀ j, laneBytes tr tt s j id amtCol = [a j] ++ ([l j] ++ (cc j ++ so j)) := fun j => rfl
  have p1 : ((List.range 16).flatMap fun j => laneBytes tr tt s j id amtCol).Perm
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
  have hg : ∀ p, p < 72 → ((List.range 72).map (valAt tr tt amtCol s)).getD p 0 = valAt tr tt amtCol s p := by
    intro p hp; simp [List.getD_eq_getElem?_getD, List.getElem?_range hp]
  have hlen : ((List.range 72).map (valAt tr tt amtCol s)).length = 72 := by simp
  generalize ((List.range 72).map (valAt tr tt amtCol s)) = pre at hg hlen
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
      List.append_nil, flatMap_range'_single so (fun j => [id, 64 + j, cN tr tt (s + j) st]) 0 8
        (fun j hj => by simp [so, hj]), List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp, Nat.zero_add]
    rw [hg (64 + j) (by omega)]
    simp [valAt, show ¬ (64 + j < 16) by omega, show ¬ (64 + j < 32) by omega, show ¬ (64 + j < 64) by omega]
  rw [e1, e2, e3, e4]

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem post_list (s : Nat) :
    (acctOfSeg tr tt s).post ++ (acctOfSeg tr tt s).pre.drop 16 = (List.range 72).map (valAt tr tt post s) := by
  apply List.ext_getElem
  · simp [acctOfSeg]
  · intro p h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases hp : p < 16
    · rw [List.getElem_append_left (by simp [acctOfSeg]; omega)]
      simp [acctOfSeg, valAt, hp]
    · rw [List.getElem_append_right (by simp [acctOfSeg]; omega)]
      simp [acctOfSeg, valAt, hp, show 16 + (p - 16) = p by omega]

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multNat1 (e : Expr) (q : Nat) :
    Interaction.multNat.go tr tt q pub [e] 0 = if e.eval tr tt q pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr tt q pub = 1 <;> simp [h]

/-- Nat messages a row sends for one value (`VBYTES` with `id = vid`, `BYTES` with `id = VPOST(vid)`). -/
def rowN (tr : Trace Fp) (tt q : Nat) (id : Nat) (lane : Nat) (amtCol : Nat) (lo : Bool) : List Msg :=
  let one (pos x : Nat) : Msg := [id, pos, cN tr tt q x]
  [one lane amtCol, one (16 + lane) lk, one (32 + 2 * lane) ch0, one (33 + 2 * lane) ch1] ++
  (if lo then [one (64 + lane) st] else [])

theorem fpN (a : Fp) : Fp.ofNat a.toNat = a := Fp.ofNat_toNat a

theorem rowT_v (q j : Nat) (hj : j < 16) (ha : tr.cell tt q act = 1) (hi : tr.cell tt q i = ((j : Nat) : Fp))
    (hg : tr.cell tt q gS = if j < 8 then 1 else 0) :
    rowTraffic AcctV3.interactions tr tt q pub B_VBYTES true =
      (rowN tr tt q (cN tr tt q kk) j amt (decide (j < 8))).map Msg.toFp := by
  simp only [rowTraffic, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, eval_c, eval_add,
    eval_k, eval_smul, eval_mid, ha, hg]
  rw [natCast_eq] at hi
  have hjP : j % P = j := Nat.mod_eq_of_lt (by unfold P; omega)
  by_cases h8 : j < 8 <;>
  simp [h8, rowN, Msg.toFp, msgId, B_BYTES, B_VBYTES, B_MEM, B_VSLOT, natCast_eq, fpN, hi, Fp.toNat_ofNat, hjP]

theorem rowT_b (q j : Nat) (hj : j < 16) (ha : tr.cell tt q act = 1) (hi : tr.cell tt q i = ((j : Nat) : Fp))
    (hg : tr.cell tt q gS = if j < 8 then 1 else 0) :
    rowTraffic AcctV3.interactions tr tt q pub B_BYTES true =
      (rowN tr tt q (msgId K_VPOST (cN tr tt q kk)) j post (decide (j < 8))).map Msg.toFp := by
  simp only [rowTraffic, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, eval_c, eval_add,
    eval_k, eval_smul, eval_mid, ha, hg]
  rw [natCast_eq] at hi
  have hjP : j % P = j := Nat.mod_eq_of_lt (by unfold P; omega)
  by_cases h8 : j < 8 <;>
  simp [h8, rowN, Msg.toFp, msgId, B_BYTES, B_VBYTES, B_MEM, B_VSLOT, natCast_eq, fpN, hi, Fp.toNat_ofNat, hjP]

def memN (tr : Trace Fp) (tt q j : Nat) (t amtCol : Nat) : Msg :=
  [cN tr tt q kk, t, j, cN tr tt q amtCol, cN tr tt q lk, cN tr tt q st]

theorem rowT_other (q j : Nat) (hj : j < 16) (ha : tr.cell tt q act = 1)
    (hi : tr.cell tt q i = ((j : Nat) : Fp)) (b : Nat) (sd : Bool)
    (hb : ¬ (b = B_BYTES ∧ sd = true)) (hv : ¬ (b = B_VBYTES ∧ sd = true)) :
    rowTraffic AcctV3.interactions tr tt q pub b sd =
      (if b = B_MEM ∧ sd = true then [(memN tr tt q j 0 amt).map Fp.ofNat] else []) ++
      (if b = B_MEM ∧ sd = false then [(memN tr tt q j (cN tr tt q tlast) post).map Fp.ofNat] else []) ++
      (if b = B_VSLOT ∧ sd = true ∧ tr.cell tt q af = 1 then [[tr.cell tt q kk]] else []) := by
  rw [natCast_eq] at hi
  have hjP : j % P = j := Nat.mod_eq_of_lt (by unfold P; omega)
  simp only [rowTraffic, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, eval_c, eval_k, ha]
  by_cases h1 : b = B_BYTES
  · subst h1
    have : sd = false := by cases sd <;> simp_all
    subst this
    simp [B_BYTES, B_VBYTES, B_MEM, B_VSLOT]
  · by_cases h0 : b = B_VBYTES
    · subst h0
      have : sd = false := by cases sd <;> simp_all
      subst this
      simp [B_BYTES, B_VBYTES, B_MEM, B_VSLOT]
    · by_cases h2 : b = B_MEM
      · subst h2; cases sd <;> simp [B_BYTES, B_VBYTES, B_MEM, B_VSLOT, memN, fpN, hi, Fp.toNat_ofNat, hjP] <;> rfl
      · by_cases h3 : b = B_VSLOT
        · subst h3; cases sd <;> simp [B_BYTES, B_VBYTES, B_MEM, B_VSLOT]
          split <;> simp_all [eq_comm]
        · simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, h0, h1, h2, h3]

theorem acctV3Sends_flat (as : List AcctV) (b : Nat) :
    acctV3Sends as b = as.flatMap fun a => acctV3Sends [a] b := by
  unfold acctV3Sends; repeat' split
  all_goals simp [map_eq_flatMap]

theorem acctRecvs_flat (as : List AcctV) (b : Nat) : acctRecvs as b = as.flatMap fun a => acctRecvs [a] b := by
  unfold acctRecvs; split <;> simp

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- One segment's traffic, up to permutation. -/
theorem segTraffic (hL : TableLocal AcctV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) (sd : Bool) :
    ((List.range' s ℓ).flatMap fun q => rowTraffic AcctV3.interactions tr tt q pub b sd).Perm
      ((if sd then acctV3Sends [acctOfSeg tr tt s] b else acctRecvs [acctOfSeg tr tt s] b).map Msg.toFp) := by
  obtain ⟨h16, hrow, -⟩ := segInfo hL hseg hH
  subst h16
  have hfs : tr.cell tt s af = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hgS : ∀ j, j < 16 → tr.cell tt (s + j) gS = if j < 8 then 1 else 0 := fun j hj => by
    rw [(rowFacts hL (by omega : s + j < _)).2.2.2, (hrow j hj).1, (hrow j hj).2.2.2.2.1]; split <;> grind
  have hst : ∀ j, j < 16 → ¬ j < 8 → tr.cell tt (s + j) st = 0 := fun j hj h8 =>
    (rowFacts hL (by omega : s + j < _)).2.2.1 (by rw [(hrow j hj).2.2.2.2.1, if_neg h8])
  have hk : ∀ j, j < 16 → cN tr tt (s + j) kk = cN tr tt s kk := fun j hj => by
    show (tr.cell tt (s + j) kk).toNat = _; rw [(hrow j hj).2.2.1]
  have htl : ∀ j, j < 16 → cN tr tt (s + j) tlast = cN tr tt s tlast := fun j hj => by
    show (tr.cell tt (s + j) tlast).toNat = _; rw [(hrow j hj).2.2.2.1]
  have hl0 : ∀ j, 0 < j → j < 16 → tr.cell tt (s + j) af = 0 := fun j h0 hj =>
    zero_of_not_one hL (by omega) (by simp) (hseg.2.2.2.2.1 (s + j) (by omega) (by omega))
  have hlaneN : ∀ id amtCol j, j < 16 → rowN tr tt (s + j) id j amtCol (decide (j < 8)) =
      laneBytes tr tt s j id amtCol := by
    intro id amtCol j hj
    simp only [rowN, laneBytes]
    by_cases h8 : j < 8 <;> simp [h8]
  rw [List.range'_eq_map_range, List.flatMap_map]
  by_cases hV : b = B_VBYTES ∧ sd = true
  · obtain ⟨rfl, rfl⟩ := hV
    rw [flatMap_segs' (G := fun j => (laneBytes tr tt s j (cN tr tt s kk) amt).map Msg.toFp)
      (fun j hj => by
        rw [rowT_v (s + j) j (List.mem_range.mp hj) (hrow j (List.mem_range.mp hj)).1
          (hrow j (List.mem_range.mp hj)).2.1 (hgS j (List.mem_range.mp hj)), hk j (List.mem_range.mp hj),
          hlaneN _ _ j (List.mem_range.mp hj)]), ← List.map_flatMap]
    simp only [if_true, acctV3Sends, if_pos rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Perm.map _ (emit_perm s _ amt)
  · by_cases hB : b = B_BYTES ∧ sd = true
    · obtain ⟨rfl, rfl⟩ := hB
      rw [flatMap_segs' (G := fun j => (laneBytes tr tt s j (msgId K_VPOST (cN tr tt s kk)) post).map Msg.toFp)
        (fun j hj => by
          rw [rowT_b (s + j) j (List.mem_range.mp hj) (hrow j (List.mem_range.mp hj)).1
            (hrow j (List.mem_range.mp hj)).2.1 (hgS j (List.mem_range.mp hj)), hk j (List.mem_range.mp hj),
            hlaneN _ _ j (List.mem_range.mp hj)]), ← List.map_flatMap]
      simp only [if_true, acctV3Sends, show B_BYTES ≠ B_VBYTES by decide, if_false, if_pos rfl,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [post_list]
      exact List.Perm.map _ (emit_perm s _ post)
    · apply List.Perm.of_eq
      rw [flatMap_segs' (G := fun j =>
        (if b = B_MEM ∧ sd = true then [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] else []) ++
        (if b = B_MEM ∧ sd = false then [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] else []) ++
        (if b = B_VSLOT ∧ sd = true ∧ tr.cell tt (s + j) af = 1 then [[tr.cell tt (s + j) kk]] else []))
        (fun j hj => rowT_other (s + j) j (List.mem_range.mp hj) (hrow j (List.mem_range.mp hj)).1
          (hrow j (List.mem_range.mp hj)).2.1 b sd hB hV)]
      have hpre : ∀ p, p < 72 → (acctOfSeg tr tt s).pre.getD p 0 = preAt tr tt s p := fun p hp => by
        simp [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_range hp]
      have hpost : ∀ j, j < 16 → (acctOfSeg tr tt s).post.getD j 0 = cN tr tt (s + j) post := fun j hj => by
        simp [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_range hj]
      have hlane : ∀ (amtCol : Nat) (col : List Nat), (∀ j, j < 16 → col.getD j 0 = cN tr tt (s + j) amtCol) →
          ∀ j, j < 16 → acctLane (acctOfSeg tr tt s) col j =
            [cN tr tt (s + j) amtCol, cN tr tt (s + j) lk, cN tr tt (s + j) st] := by
        intro amtCol col hcol j hj
        simp only [acctLane, hcol j hj, hpre (16 + j) (by omega), preAt, valAt]
        by_cases h8 : j < 8
        · rw [if_pos h8, hpre (64 + j) (by omega)]
          simp [valAt, show ¬ (16 + j < 16) by omega, show 16 + j < 32 by omega, show ¬ (64 + j < 16) by omega,
            show ¬ (64 + j < 32) by omega, show ¬ (64 + j < 64) by omega]
        · rw [if_neg h8, show cN tr tt (s + j) st = 0 by simp [cN, hst j hj h8, Fp.toNat_zero]]
          simp [show ¬ (16 + j < 16) by omega, show 16 + j < 32 by omega]
      by_cases hM : b = B_MEM
      · subst hM
        cases sd
        · have hf : (fun j =>
              (if B_MEM = B_MEM ∧ false = true then [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] else []) ++
              (if B_MEM = B_MEM ∧ false = false then
                [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] else []) ++
              (if B_MEM = B_VSLOT ∧ false = true ∧ tr.cell tt (s + j) af = 1 then
                [[tr.cell tt (s + j) kk]] else [])) =
              fun j => [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] := by
            funext j; simp
          rw [hf, ← map_eq_flatMap]
          simp only [Bool.false_eq_true, if_false, acctRecvs, if_pos rfl, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.map_map]
          simp only [ite_true, List.map_map]
          apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
          simp only [Function.comp, Msg.toFp, memN, hk j hj, htl j hj]
          rw [hlane post (acctOfSeg tr tt s).post hpost j hj]; simp [acctOfSeg]
        · have hf : (fun j =>
              (if B_MEM = B_MEM ∧ true = true then [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] else []) ++
              (if B_MEM = B_MEM ∧ true = false then
                [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] else []) ++
              (if B_MEM = B_VSLOT ∧ true = true ∧ tr.cell tt (s + j) af = 1 then
                [[tr.cell tt (s + j) kk]] else [])) =
              fun j => [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] := by
            funext j; simp [B_MEM, B_VSLOT]
          rw [hf, ← map_eq_flatMap]
          simp only [if_true, acctV3Sends, show ¬ (B_MEM = B_BYTES) by decide,
            show ¬ (B_MEM = B_VBYTES) by decide, if_false, if_pos rfl,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
          try simp only [ite_true, List.map_map]
          apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
          simp only [Function.comp, Msg.toFp, memN, hk j hj]
          rw [hlane amt (acctOfSeg tr tt s).pre (fun j hj => by rw [hpre j (by omega)]; simp [valAt, hj]) j hj]
          simp [acctOfSeg]
      · by_cases hS : b = B_VSLOT ∧ sd = true
        · obtain ⟨rfl, rfl⟩ := hS
          have hf : (fun j =>
              (if B_VSLOT = B_MEM ∧ true = true then [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] else []) ++
              (if B_VSLOT = B_MEM ∧ true = false then
                [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] else []) ++
              (if B_VSLOT = B_VSLOT ∧ true = true ∧ tr.cell tt (s + j) af = 1 then
                [[tr.cell tt (s + j) kk]] else [])) =
              fun j => if tr.cell tt (s + j) af = 1 then [[tr.cell tt (s + j) kk]] else [] := by
            funext j; simp [B_MEM, B_VSLOT]
          rw [hf]
          have h16 : List.range 16 = [0] ++ List.range' 1 15 := by decide
          rw [h16, List.flatMap_append, List.flatMap_singleton, Nat.add_zero, if_pos hfs,
            flatMap_range'_nil _ 1 15 (fun j hj => by
              rw [if_neg (by rw [hl0 (1 + j) (by omega) (by omega)]; exact fp_zero_ne_one)])]
          simp [acctV3Sends, B_VSLOT, B_MEM, B_BYTES, B_VBYTES, Msg.toFp, acctOfSeg, fpN]
        · have hf : (fun j =>
              (if b = B_MEM ∧ sd = true then [(memN tr tt (s + j) j 0 amt).map Fp.ofNat] else []) ++
              (if b = B_MEM ∧ sd = false then
                [(memN tr tt (s + j) j (cN tr tt (s + j) tlast) post).map Fp.ofNat] else []) ++
              (if b = B_VSLOT ∧ sd = true ∧ tr.cell tt (s + j) af = 1 then
                [[tr.cell tt (s + j) kk]] else [])) = fun _ => [] := by
            funext j
            rw [if_neg (fun h => hM h.1), if_neg (fun h => hM h.1), if_neg (fun h => hS ⟨h.1, h.2.1⟩)]; rfl
          rw [hf, flatMap_nil_fun]
          cases sd
          · simp [acctRecvs, hM]
          · have : b ≠ B_BYTES := fun h => hB ⟨h, rfl⟩
            have : b ≠ B_VBYTES := fun h => hV ⟨h, rfl⟩
            have : b ≠ B_VSLOT := fun h => hS ⟨h, rfl⟩
            simp [acctV3Sends, hM, *]

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3.AcctV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Near.Acct

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem dsumF_zero (s : Nat) (h : ∀ j, j < 16 → tr.cell tt (s + j) amt = 255) :
    ∀ j, j ≤ 16 → dsumF tr tt s j = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih => intro hj; simp only [dsumF]; rw [ih (by omega), h j (by omega)]; grind

theorem notMax (hL : TableLocal AcctV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    (∀ j, j < 16 → (acctOfSeg tr tt s).pre.getD j 0 < 256) →
      ∃ j, j < 16 ∧ (acctOfSeg tr tt s).pre.getD j 0 ≠ 255 := by
  intro _
  obtain ⟨h16, hrow, hinv⟩ := segInfo hL hseg hH
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ j, j < 16 → tr.cell tt (s + j) amt = 255 := by
    intro j hj
    have : (acctOfSeg tr tt s).pre.getD j 0 = 255 := Classical.byContradiction fun h => hne ⟨j, hj, h⟩
    simp only [acctOfSeg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : j < 72),
      Option.map_some, Option.getD_some, valAt, if_pos hj] at this
    have h' : (tr.cell tt (s + j) amt).toNat = 255 := this
    rw [← Fp.ofNat_toNat (tr.cell tt (s + j) amt), h']; rfl
  have := (hrow 15 (by omega)).2.2.2.2.2
  rw [this, dsumF_zero s hall 16 (by omega)] at hinv
  grind

end ZkFormal.NearV3.AcctV3Proof

namespace ZkFormal.NearV3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Acct AcctV3Proof

/-- **The `acctV3` view.** -/
theorem acctV3_view : AcctV3ViewStmt := by
  intro tr pub tt hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) height_pos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic AcctV3.interactions tr tt q pub b sd = [] := by
    intro b sd q h1 h2
    have ha := zero_of_not_one hL h2 (by simp) (hpad q h1 h2)
    have hf : tr.cell tt q af = 0 := by
      rcases isBool hL h2 (x := af) (by simp) with h | h
      · exact h
      · have := ((rowFacts hL h2).1 h).1; rw [ha] at this; exact absurd this fp_zero_ne_one
    have hg : tr.cell tt q gS = 0 := by rw [(rowFacts hL h2).2.2.2, ha]; grind
    simp only [rowTraffic, AcctV3.interactions, AcctV3.vpre, Acct.vbytes, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat, multNat1, eval_c, ha, hf, hg]
    simp
  have h16 : ∀ p ∈ segs, p.2 = 16 := fun p hp => (segInfo hL (hall p hp) (hH p hp)).1
  refine ⟨segs.map fun p => acctOfSeg tr tt p.1, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
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
  · rw [List.length_map]
    have hsum : (segs.map fun p => p.2).sum = segEnd 0 segs := by
      have := congrArg List.length (range'_segs segs 0 hc)
      simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
      rw [this]
    have : (segs.map fun p => p.2) = segs.map fun _ => 16 := List.map_congr_left h16
    rw [this] at hsum
    have e : ∀ l : List (Nat × Nat), (l.map fun _ => 16).sum = 16 * l.length := by
      intro l; induction l with
      | nil => rfl
      | cons _ l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
    rw [e] at hsum
    have := height_le hL
    simp only [AcctV3.maxLog]; omega
  · simp only [acctV3Traffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT b true)]
    refine List.Perm.count_eq ?_ m
    rw [acctV3Sends_flat, List.map_flatMap, List.flatMap_map]
    exact perm_flatMap_congr _ _ _ (fun p hp => by
      have := segTraffic hL (hall p hp) (hH p hp) b true; simpa using this)
  · simp only [acctV3Traffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT b false)]
    refine List.Perm.count_eq ?_ m
    rw [acctRecvs_flat, List.map_flatMap, List.flatMap_map]
    exact perm_flatMap_congr _ _ _ (fun p hp => by
      have := segTraffic hL (hall p hp) (hH p hp) b false; simpa using this)

end ZkFormal.NearV3
