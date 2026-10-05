import ZkFormal.Near.Render.Proof.MrkRecs
import ZkFormal.Near.Render.Proof.Base
import ZkFormal.Near.Render.Rcpt
import ZkFormal.Near.Render.Proof.RcptAttr

/-!
# ZkFormal.Near.Render.Proof.RcptBase — rows of the honest `rcpt` table

* `evR cur nx fst lst pub e`: an expression on a row given by its cells `cur`
  and the next row's `nx` (`eval_evR`); `Zr`: a syntactic test that an
  expression vanishes when some cells do (`Zr_sound`).
* The records `recsOf ds` in table order: consecutive records are related by
  `nextOf` (`recs_adj`), every record is in range (`RecOk`), the last one ends
  the last receipt (`recs_last`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

attribute [rcols] Rcpt.act Rcpt.rf Rcpt.rl Rcpt.lastR Rcpt.sCL Rcpt.sPL Rcpt.sP Rcpt.sVL Rcpt.sV Rcpt.sRID Rcpt.sT0 Rcpt.sSL Rcpt.sS Rcpt.sKT Rcpt.sPK Rcpt.sGP Rcpt.sTL Rcpt.sDEP Rcpt.sXP0 Rcpt.sXRI Rcpt.sXG Rcpt.sXST Rcpt.sXL0 Rcpt.sXLH Rcpt.sXRH Rcpt.sXRF Rcpt.sXRZ Rcpt.idx Rcpt.fs Rcpt.fe Rcpt.b Rcpt.e1Id Rcpt.e1Pos Rcpt.e1V Rcpt.e1G Rcpt.e2Id Rcpt.e2Pos Rcpt.e2V Rcpt.e2G Rcpt.e3Id Rcpt.e3Pos Rcpt.e3V Rcpt.e3G Rcpt.tA Rcpt.symA Rcpt.lastA Rcpt.gKA Rcpt.kz Rcpt.r Rcpt.o Rcpt.o2 Rcpt.Lp Rcpt.Lv Rcpt.Ls Rcpt.kt Rcpt.hr Rcpt.kslot Rcpt.tprev Rcpt.rcnt Rcpt.ge Rcpt.big Rcpt.oEnd Rcpt.o2End Rcpt.reg Rcpt.tok Rcpt.h2 Rcpt.h3 Rcpt.h5 Rcpt.h6 Rcpt.h7 Rcpt.lb Rcpt.z Rcpt.linv Rcpt.l210 Rcpt.hx6 Rcpt.acc Rcpt.vc0 Rcpt.vc1 Rcpt.h01 Rcpt.p1 Rcpt.p2 Rcpt.p3 Rcpt.i1 Rcpt.i2 Rcpt.i3 Rcpt.isys Rcpt.r1 Rcpt.lo8 Rcpt.lo4 Rcpt.xb Rcpt.c1 Rcpt.c2 Rcpt.c3 Rcpt.c4 Rcpt.dl Rcpt.burnt Rcpt.ramt Rcpt.sumD Rcpt.invA Rcpt.bef Rcpt.lk Rcpt.st Rcpt.dsum Rcpt.invB Rcpt.dI Rcpt.dL Rcpt.gDg Rcpt.width


/-! ## Rows as functions -/

/-- The environment of a row with cells `cur`, next row `nx`. -/
def rowE (cur nx : Nat → Fp) (fst lst : Bool) (pub : List Fp) : Env Fp where
  ofNat := fun n => @Nat.cast Fp Lean.Grind.Semiring.natCast n
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun x b => if b then nx x else cur x
  pub := fun i => pub.getD i 0
  isFirst := if fst then 1 else 0
  isLast := if lst then 1 else 0
  isTransition := if lst then 0 else 1

def evR (cur nx : Nat → Fp) (fst lst : Bool) (pub : List Fp) (e : Expr) : Fp :=
  e.evalWith (rowE cur nx fst lst pub)

theorem eval_evR (tr : Trace Fp) (t q : Nat) (pub : List Fp) (e : Expr) :
    e.eval tr t q pub = evR (tr.cell t q) (tr.cell t ((q + 1) % tr.height t)) (decide (q = 0))
      (decide (q + 1 = tr.height t)) pub e := by
  induction e with
  | const v => rfl
  | col x b => cases b <;> rfl
  | pub i => rfl
  | isFirst => simp only [Expr.eval, evR, Expr.evalWith, rowEnv, rowE]; split <;> simp_all
  | isLast => simp only [Expr.eval, evR, Expr.evalWith, rowEnv, rowE]; split <;> simp_all
  | isTransition => simp only [Expr.eval, evR, Expr.evalWith, rowEnv, rowE]; split <;> simp_all
  | add a d iha ihd => simp only [Expr.eval, evR, Expr.evalWith] at *; rw [iha, ihd]; rfl
  | mul a d iha ihd => simp only [Expr.eval, evR, Expr.evalWith] at *; rw [iha, ihd]; rfl
  | neg a iha => simp only [Expr.eval, evR, Expr.evalWith] at *; rw [iha]; rfl

section
variable (cur nx : Nat → Fp) (fst lst : Bool) (pub : List Fp)

@[simp] theorem evR_c (x : Nat) : evR cur nx fst lst pub (c x) = cur x := rfl
@[simp] theorem evR_n (x : Nat) : evR cur nx fst lst pub (n x) = nx x := rfl
@[simp] theorem evR_k (v : Nat) : evR cur nx fst lst pub (k v) = (v : Fp) := rfl
@[simp] theorem evR_const (v : Nat) : evR cur nx fst lst pub (.const v) = (v : Fp) := rfl
@[simp] theorem evR_add (a d : Expr) :
    evR cur nx fst lst pub (.add a d) = evR cur nx fst lst pub a + evR cur nx fst lst pub d := rfl
@[simp] theorem evR_mul (a d : Expr) :
    evR cur nx fst lst pub (.mul a d) = evR cur nx fst lst pub a * evR cur nx fst lst pub d := rfl
@[simp] theorem evR_neg (a : Expr) : evR cur nx fst lst pub (.neg a) = -evR cur nx fst lst pub a := rfl
@[simp] theorem evR_sub (a d : Expr) :
    evR cur nx fst lst pub (sub a d) = evR cur nx fst lst pub a - evR cur nx fst lst pub d := by
  simp [sub, Lean.Grind.Ring.sub_eq_add_neg]
@[simp] theorem evR_not (a : Expr) : evR cur nx fst lst pub (Dsl.not a) = 1 - evR cur nx fst lst pub a := by
  simp [Dsl.not]; rfl
@[simp] theorem evR_mul3 (a b d : Expr) :
    evR cur nx fst lst pub (mul3 a b d) =
      evR cur nx fst lst pub a * evR cur nx fst lst pub b * evR cur nx fst lst pub d := rfl
@[simp] theorem evR_bool (a : Expr) :
    evR cur nx fst lst pub (Dsl.bool a) = evR cur nx fst lst pub a * (evR cur nx fst lst pub a - 1) := by
  simp [Dsl.bool]; rfl
@[simp] theorem evR_smul (v : Nat) (a : Expr) :
    evR cur nx fst lst pub (smul v a) = (v : Fp) * evR cur nx fst lst pub a := rfl
@[simp] theorem evR_pub (i : Nat) : evR cur nx fst lst pub (.pub i) = pub.getD i 0 := rfl
@[simp] theorem evR_isFirst : evR cur nx fst lst pub .isFirst = if fst then 1 else 0 := rfl
@[simp] theorem evR_isLast : evR cur nx fst lst pub .isLast = if lst then 1 else 0 := rfl
@[simp] theorem evR_isTransition : evR cur nx fst lst pub .isTransition = if lst then 0 else 1 := rfl
@[simp] theorem evR_sum_nil : evR cur nx fst lst pub (sum []) = 0 := rfl
@[simp] theorem evR_sum_cons (e : Expr) (es : List Expr) :
    evR cur nx fst lst pub (sum (e :: es)) = evR cur nx fst lst pub e + evR cur nx fst lst pub (sum es) := rfl
@[simp] theorem evR_mid (kind : Nat) (idx : Expr) :
    evR cur nx fst lst pub (mid kind idx) = (kind : Fp) + (16 : Nat) * evR cur nx fst lst pub idx := rfl

end

/-! ## Vanishing by zero cells -/

/-- The expression vanishes when the current cells `z`, the next cells `zn`
vanish (and `isFirst`, if `f0`). -/
def Zr (z zn : Nat → Bool) (f0 : Bool) : Expr → Bool
  | .const v => v == 0
  | .col x false => z x
  | .col x true => zn x
  | .pub _ => false
  | .isFirst => f0
  | .isLast | .isTransition => false
  | .add a d => Zr z zn f0 a && Zr z zn f0 d
  | .mul a d => Zr z zn f0 a || Zr z zn f0 d
  | .neg a => Zr z zn f0 a

theorem Zr_sound {z zn : Nat → Bool} {f0 : Bool} {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp}
    (hz : ∀ x, z x = true → cur x = 0) (hzn : ∀ x, zn x = true → nx x = 0) (hf : f0 = true → fst = false) :
    ∀ e, Zr z zn f0 e = true → evR cur nx fst lst pub e = 0
  | .const v, h => by simp only [Zr, beq_iff_eq] at h; subst h; rfl
  | .col x false, h => hz x h
  | .col x true, h => hzn x h
  | .pub _, h => by simp [Zr] at h
  | .isFirst, h => by simp only [Zr] at h; simp [hf h]
  | .isLast, h => by simp [Zr] at h
  | .isTransition, h => by simp [Zr] at h
  | .add a d, h => by
    simp only [Zr, Bool.and_eq_true] at h
    simp only [evR_add, Zr_sound hz hzn hf a h.1, Zr_sound hz hzn hf d h.2]; grind
  | .mul a d, h => by
    simp only [Zr, Bool.or_eq_true] at h
    rcases h with h | h <;> simp only [evR_mul, Zr_sound hz hzn hf _ h] <;> grind
  | .neg a, h => by simp only [Zr] at h; simp only [evR_neg, Zr_sound hz hzn hf a h]; grind

theorem Zr_mono_n {z zn zn' : Nat → Bool} {f0 : Bool} (h : ∀ x, zn x = true → zn' x = true) :
    ∀ {e}, Zr z zn f0 e = true → Zr z zn' f0 e = true
  | .const _, h' => h'
  | .col x false, h' => h'
  | .col x true, h' => h x h'
  | .pub _, h' => h'
  | .isFirst, h' => h'
  | .isLast, h' => h'
  | .isTransition, h' => h'
  | .add a d, h' => by
    simp only [Zr, Bool.and_eq_true] at h' ⊢; exact ⟨Zr_mono_n h h'.1, Zr_mono_n h h'.2⟩
  | .mul a d, h' => by
    simp only [Zr, Bool.or_eq_true] at h' ⊢
    rcases h' with h' | h'
    · exact .inl (Zr_mono_n h h')
    · exact .inr (Zr_mono_n h h')
  | .neg a, h' => by simp only [Zr] at h' ⊢; exact Zr_mono_n h h'

/-! ## Records -/

open RcptGen

/-- The field after `s`. -/
def nextF (h : Bool) (s : Nat) : Nat :=
  if s = 5 then 6 else if s = 6 then 7 else if s = 7 then 8 else if s = 8 then 9
  else if s = 9 then 10 else if s = 10 then 11 else if s = 11 then 12 else if s = 12 then 13
  else if s = 13 then 14 else if s = 14 then 15 else if s = 15 then 16 else if s = 16 then 17
  else if s = 17 then 18 else if s = 18 then (if h then 19 else 20) else if s = 19 then 20
  else if s = 20 then 21 else if s = 21 then 22 else if s = 22 then 23
  else if s = 23 then 24 else if s = 24 then 25 else if s = 25 then 26 else 0

/-- The record after `ρ` (receipt data `D r`). -/
def nextOf (D : Nat → RD) : RRec → RRec
  | .cl i => if i < 11 then .cl (i + 1) else .seg 0 5 0
  | .seg r s i =>
    if i + 1 < fLen (D r) s then .seg r s (i + 1)
    else if isRl (D r) s i then .seg (r + 1) 5 0
    else .seg r (nextF (D r).hr s) 0

/-- Last field of a receipt. -/
def lastF (h : Bool) : Nat := if h then 26 else 23

/-- Account-id strings are nonempty. -/
def DOk (d : RD) : Prop := 1 ≤ d.pred.length ∧ 1 ≤ d.recv.length ∧ 1 ≤ d.signer.length

/-- A record in range. -/
def RecOk (N : Nat) (D : Nat → RD) : RRec → Prop
  | .cl i => i < 12
  | .seg r s i => r < N ∧ s ∈ fields (D r).hr ∧ i < fLen (D r) s

theorem fLen_pos {d : RD} (hd : DOk d) {s : Nat} (hs : s ∈ fields d.hr) : 1 ≤ fLen d s := by
  obtain ⟨h1, h2, h3⟩ := hd
  cases hh : d.hr <;> simp only [fields, hh] at hs <;>
  simp at hs <;>
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [fLen, rcols] <;> omega

/-- Consecutive fields. -/
def FAdj (h : Bool) (s s' : Nat) : Prop := s' = nextF h s ∧ s ≠ 26 ∧ (s = 23 → h = true)

theorem fields_adj (h : Bool) : Adj2 (FAdj h) (fields h) := by
  cases h <;> simp [Adj2, FAdj, fields, nextF, rcols]

theorem fields_head (h : Bool) : (fields h).head? = some 5 := by cases h <;> rfl
theorem fields_last (h : Bool) : (fields h).getLast? = some (lastF h) := by cases h <;> rfl

/-- The rows of field `s` of receipt `r`. -/
def chunk (d : RD) (s : Nat) : List RRec := (List.range (fLen d s)).map (RRec.seg d.r s)

theorem segRecs_eq (d : RD) : segRecs d = (fields d.hr).flatMap (chunk d) := rfl

theorem chunk_ne {d : RD} (hd : DOk d) {s : Nat} (hs : s ∈ fields d.hr) : chunk d s ≠ [] := by
  have := fLen_pos hd hs
  simp [chunk]; omega

theorem chunk_head {d : RD} (hd : DOk d) {s : Nat} (hs : s ∈ fields d.hr) :
    (chunk d s).head? = some (.seg d.r s 0) := by
  have := fLen_pos hd hs
  simp only [chunk]
  rw [show fLen d s = (fLen d s - 1) + 1 by omega, List.range_succ_eq_map]
  simp

theorem chunk_last {d : RD} (hd : DOk d) {s : Nat} (hs : s ∈ fields d.hr) :
    (chunk d s).getLast? = some (.seg d.r s (fLen d s - 1)) := by
  have := fLen_pos hd hs
  simp only [chunk]
  rw [show fLen d s = (fLen d s - 1) + 1 by omega, List.range_succ]
  simp

section
variable {D : Nat → RD} {r : Nat} (hdr : (D r).r = r) (hd : DOk (D r))
include hdr hd

theorem chunk_adj {s : Nat} : Adj2 (fun a b => b = nextOf D a) (chunk (D r) s) := by
  apply Adj2.of_get
  intro q hq
  simp only [chunk, List.length_map, List.length_range] at hq
  simp only [chunk, List.getElem_map, List.getElem_range, nextOf, hdr, if_pos hq]

theorem segRecs_adj : Adj2 (fun a b => b = nextOf D a) (segRecs (D r)) := by
  rw [segRecs_eq]
  apply Adj2.flatMap (chunk (D r)) (fun s _ => chunk_adj hdr hd) _ (fun s hs => chunk_ne hd hs)
  -- consecutive fields
  have FA := fields_adj (D r).hr
  have gen : ∀ (l : List Nat), (∀ s ∈ l, s ∈ fields (D r).hr) → Adj2 (FAdj (D r).hr) l →
      Adj2 (fun x y => ∀ a b, (chunk (D r) x).getLast? = some a → (chunk (D r) y).head? = some b →
        b = nextOf D a) l := by
    intro l
    induction l with
    | nil => intros; trivial
    | cons x l ih =>
      intro hm ha
      cases l with
      | nil => trivial
      | cons y l =>
        obtain ⟨⟨h1, h2, h3⟩, ha⟩ := ha
        refine ⟨fun a b hA hB => ?_, ih (fun s hs => hm s (by simp [hs])) ha⟩
        rw [chunk_last hd (hm x (by simp))] at hA
        rw [chunk_head hd (hm y (by simp))] at hB
        cases hA; cases hB
        have hp := fLen_pos hd (hm x (by simp))
        have hrl : isRl (D r) x (fLen (D r) x - 1) = false := by
          simp only [isRl, Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false]
          right; refine ⟨h2, ?_⟩
          by_cases hx : x = 23
          · right; exact h3 hx
          · left; exact hx
        simp only [nextOf, hdr, show ¬ (fLen (D r) x - 1 + 1 < fLen (D r) x) by omega, if_false, hrl,
          Bool.false_eq_true, h1]
  exact gen _ (fun s hs => hs) FA

theorem segRecs_ne : segRecs (D r) ≠ [] := by
  rw [segRecs_eq]
  intro h
  rw [List.flatMap_eq_nil_iff] at h
  exact chunk_ne hd (show 5 ∈ fields (D r).hr by cases (D r).hr <;> simp [fields]) (h 5 (by
    cases (D r).hr <;> simp [fields]))

theorem segRecs_head : (segRecs (D r)).head? = some (.seg r 5 0) := by
  rw [segRecs_eq]
  have hs : 5 ∈ fields (D r).hr := by cases (D r).hr <;> simp [fields]
  have : fields (D r).hr = 5 :: (fields (D r).hr).tail := by cases (D r).hr <;> rfl
  rw [this, List.flatMap_cons]
  have hc := chunk_head hd hs
  rw [hdr] at hc
  cases hch : chunk (D r) 5 with
  | nil => exact absurd hch (chunk_ne hd hs)
  | cons a l => rw [hch] at hc; simpa using hc

theorem segRecs_last : (segRecs (D r)).getLast? =
    some (.seg r (lastF (D r).hr) (fLen (D r) (lastF (D r).hr) - 1)) := by
  rw [segRecs_eq]
  have hs : lastF (D r).hr ∈ fields (D r).hr := by cases (D r).hr <;> simp [fields, lastF]
  have : fields (D r).hr = (fields (D r).hr).dropLast ++ [lastF (D r).hr] := by cases (D r).hr <;> rfl
  rw [this, List.flatMap_append, List.flatMap_singleton, List.getLast?_append, chunk_last hd hs, hdr]
  simp

end

theorem lastF_rl {d : RD} (hd : DOk d) : isRl d (lastF d.hr) (fLen d (lastF d.hr) - 1) = true := by
  have := fLen_pos hd (show lastF d.hr ∈ fields d.hr by cases d.hr <;> simp [fields, lastF])
  cases h : d.hr <;> simp [isRl, lastF, h] at this ⊢ <;> omega

theorem segRecs_mem {d : RD} {ρ : RRec} (h : ρ ∈ segRecs d) :
    ∃ s i, ρ = .seg d.r s i ∧ s ∈ fields d.hr ∧ i < fLen d s := by
  simp only [segRecs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨s, hs, i, hi, rfl⟩ := h
  exact ⟨s, i, rfl, hs, hi⟩

/-! ## All records -/

section
variable {N : Nat} {D : Nat → RD} (hD : ∀ r, r < N → (D r).r = r ∧ DOk (D r)) (hN : 1 ≤ N)

/-- The records of receipts `0 … N − 1`. -/
def recs (N : Nat) (D : Nat → RD) : List RRec := recsOf ((List.range N).map D)

theorem recs_eq : recs N D = (List.range 12).map RRec.cl ++ (List.range N).flatMap (fun r => segRecs (D r)) := by
  simp [recs, recsOf, List.flatMap_map]

include hD in
theorem recs_ok : ∀ ρ ∈ recs N D, RecOk N D ρ := by
  intro ρ h
  rw [recs_eq] at h
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at h
  rcases h with ⟨i, hi, rfl⟩ | ⟨r, hr, hm⟩
  · exact hi
  · obtain ⟨s, i, rfl, hs, hi⟩ := segRecs_mem hm
    rw [(hD r hr).1]
    exact ⟨hr, hs, hi⟩

include hD in
theorem segs_adj : ∀ M, M ≤ N → Adj2 (fun a b => b = nextOf D a) ((List.range M).flatMap fun r => segRecs (D r)) ∧
    (0 < M → ((List.range M).flatMap fun r => segRecs (D r)).head? = some (.seg 0 5 0)) ∧
    (0 < M → ((List.range M).flatMap fun r => segRecs (D r)).getLast? =
      some (.seg (M - 1) (lastF (D (M - 1)).hr) (fLen (D (M - 1)) (lastF (D (M - 1)).hr) - 1)))
  | 0, _ => ⟨trivial, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | M + 1, hM => by
    obtain ⟨A, Hd, L⟩ := segs_adj M (by omega)
    obtain ⟨h1, h2⟩ := hD M (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · refine Adj2.append A (segRecs_adj h1 h2) ?_
      intro a b ha hb
      rcases Nat.eq_zero_or_pos M with rfl | hpos
      · simp at ha
      · rw [L hpos] at ha; rw [segRecs_head h1 h2] at hb
        cases ha; cases hb
        obtain ⟨h1', h2'⟩ := hD (M - 1) (by omega)
        have hp := fLen_pos h2' (show lastF (D (M - 1)).hr ∈ fields (D (M - 1)).hr by
          cases (D (M - 1)).hr <;> simp [fields, lastF])
        simp only [nextOf, show ¬ (fLen (D (M - 1)) (lastF (D (M - 1)).hr) - 1 + 1 <
          fLen (D (M - 1)) (lastF (D (M - 1)).hr)) by omega, if_false, lastF_rl h2', if_true,
          show M - 1 + 1 = M by omega]
    · rcases Nat.eq_zero_or_pos M with rfl | hpos
      · simpa using segRecs_head h1 h2
      · rw [List.head?_append, Hd hpos]; rfl
    · rw [List.getLast?_append, segRecs_last h1 h2]; simp

include hD hN in
theorem recs_adj : Adj2 (fun a b => b = nextOf D a) (recs N D) := by
  rw [recs_eq]
  obtain ⟨A, Hd, -⟩ := segs_adj hD N (Nat.le_refl _)
  refine Adj2.append ?_ A ?_
  · apply Adj2.map
    apply Adj2.of_get
    intro q hq
    simp only [List.length_range] at hq
    simp [nextOf, show q < 11 by omega]
  · intro a b ha hb
    rw [Hd hN] at hb
    simp [List.range_succ] at ha
    cases ha; cases hb
    simp [nextOf]

include hD hN in
theorem recs_last : (recs N D).getLast? =
    some (.seg (N - 1) (lastF (D (N - 1)).hr) (fLen (D (N - 1)) (lastF (D (N - 1)).hr) - 1)) := by
  rw [recs_eq, List.getLast?_append, (segs_adj hD N (Nat.le_refl _)).2.2 hN]; rfl

theorem recs_get_cl (i : Nat) (hi : i < 12) : (recs N D)[i]? = some (.cl i) := by
  rw [recs_eq, List.getElem?_append_left (by simp; omega)]
  simp [hi]

end

end RcptP

end ZkFormal.Near.Render
