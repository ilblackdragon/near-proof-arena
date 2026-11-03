import StateM5a.VerBus

/-!
# StateM5a.VerDec — decoding a `VER` record from its parts

A record on `VER` is published in parts (`BR`: 17, `SN`: 3), each `(tag, part, refFlag, ref₁₆,
payload)`.  A reader's parts may come from different publishers under one digest, so the decoded
record must be a function of per-part decoded values that the record determines back:

* **`PartDec`** (generic, for `BR` and `SN` alike): `g p payload : X` per part, `F` assembling a
  record from them, `proj R p` reading part `p`'s value back, with `proj (F (g ∘ P)) p = g p (P p)`.
  **`dec_of_parts`**: if every part `p` of `P` decodes like part `p` of some `Q p`, and every
  `Q p` decodes to `R`, then `P` decodes to `R`.
* **`brDec`**: the `BR` instance (slot `i` from `(f, f·isn, f·bytes)`, value and memory from part
  16); **`brDec_rec`**: decoding the payloads of `Br.rec … fl isn cb hv vl vh mem` gives the branch
  with slots `kidsFrom`, value from `(hv, vl limbs, vh)` and memory `le4 mem` — so `brOld`/`brNew`
  are the decodings of the row's old / new `VER` payloads (`brOld_dec`, `brNew_dec`).
-/

namespace StateM5a.VerDec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.VerBus

set_option maxRecDepth 100000

/-! ## Generic part decoding -/

structure PartDec where
  k : Nat
  hk : 0 < k
  X : Type
  g : Nat → List Fp → X
  F : (Nat → X) → Rec
  proj : Rec → Nat → X
  hF : ∀ a b, (∀ p, p < k → a p = b p) → F a = F b
  hproj : ∀ (P : Nat → List Fp) p, p < k → proj (F fun q => g q (P q)) p = g p (P p)

def PartDec.dec (D : PartDec) (P : Nat → List Fp) : Rec := D.F fun q => D.g q (P q)

/-- **A record assembled from parts of records equal to `R` is `R`.** -/
theorem dec_of_parts (D : PartDec) {P : Nat → List Fp} {R : Rec} (Q : Nat → Nat → List Fp)
    (hQ : ∀ p, p < D.k → D.dec (Q p) = R) (hP : ∀ p, p < D.k → D.g p (P p) = D.g p (Q p p)) :
    D.dec P = R := by
  have e1 : D.dec P = D.F (fun q => D.proj R q) := by
    unfold PartDec.dec
    apply D.hF; intro p hp
    rw [hP p hp, ← D.hproj (Q p) p hp]
    show D.proj (D.dec (Q p)) p = _
    rw [hQ p hp]
  have e2 : R = D.F (fun q => D.proj R q) := by
    conv => lhs; rw [← hQ 0 D.hk]
    unfold PartDec.dec
    apply D.hF; intro p hp
    rw [← D.hproj (Q 0) p hp]
    show D.proj (D.dec (Q 0)) p = _
    rw [hQ 0 D.hk]
  rw [e1, ← e2]

/-! ## `BR` -/

/-- Record slots from an optional-ref function. -/
def kidsO (o : Nat → Option Ref) : Nat → Nat → RKids
  | _, 0 => .nil
  | i, k + 1 => match o i with
    | some c => .some c (kidsO o (i + 1) k)
    | none => .none (kidsO o (i + 1) k)

theorem kidsO_at (o : Nat → Option Ref) : ∀ k i n, n < k → (kidsO o i k).at n = o (i + n)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, 0, _ => by
    simp only [Nat.add_zero]; unfold kidsO
    cases o i <;> rfl
  | k + 1, i, n + 1, h => by
    have := kidsO_at o k (i + 1) n (by omega)
    rw [show i + (n + 1) = i + 1 + n by omega]
    unfold kidsO
    cases o i <;> exact this

theorem kidsO_congr (o o' : Nat → Option Ref) : ∀ k i, (∀ j, j < k → o (i + j) = o' (i + j)) →
    kidsO o i k = kidsO o' i k
  | 0, _, _ => rfl
  | k + 1, i, h => by
    have ih := kidsO_congr o o' k (i + 1) (fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega]; exact h (j + 1) (by omega))
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [kidsO, h0, ih]

theorem kidsFrom_eq (fl : Nat → Nat) (rf : Nat → Ref) : ∀ k i,
    kidsFrom fl rf i k = kidsO (fun j => if fl j = 1 then some (rf j) else none) i k
  | 0, _ => rfl
  | k + 1, i => by
    simp only [RowBr.kidsFrom, kidsO, kidsFrom_eq fl rf k (i + 1)]
    split <;> simp_all

/-- 32 payload bytes as 16 big-endian limbs. -/
def pk (bs : List Fp) : List Fp := (List.range 16).map fun j => 256 * bs.getD (2 * j) 0 + bs.getD (2 * j + 1) 0

def slotDec (P : List Fp) : Option Ref :=
  if (P.getD 0 0).toNat = 1 then some (refOf (P.getD 1 0) (pk (P.drop 2))) else none

def valDec (P : List Fp) : Option Slot :=
  if (P.getD 0 0).toNat = 1 then
    some (.ref ((P.getD 1 0).toNat + 65536 * (P.getD 2 0).toNat) (bytesOf (pk (P.drop 3))))
  else none

def memDec (P : List Fp) : Nat := le4 ((P.drop 35).take 4)

def brProj : Rec → Nat → Option Ref × Option Slot × Nat
  | .branch v cs m, p => if p < 16 then (cs.at p, none, 0) else (none, v, m)
  | _, _ => (none, none, 0)

/-- **The `BR` part decoder.** -/
def brDec : PartDec where
  k := 17
  hk := by decide
  X := Option Ref × Option Slot × Nat
  g p P := if p < 16 then (slotDec P, none, 0) else (none, valDec P, memDec P)
  F a := .branch (a 16).2.1 (kidsO (fun i => (a i).1) 0 16) (a 16).2.2
  proj := brProj
  hF a b h := by
    show Rec.branch _ _ _ = Rec.branch _ _ _
    rw [h 16 (by decide), kidsO_congr (fun i => (a i).1) (fun i => (b i).1) 16 0
      (fun j hj => by rw [h (0 + j) (by omega)])]
  hproj P p hp := by
    simp only [brProj]
    by_cases h : p < 16
    · simp only [h, ↓reduceIte, kidsO_at _ 16 0 p h, Nat.zero_add]
    · have : p = 16 := by omega
      subst this; simp

/-! ## The payloads of a `BR` record -/

/-- Payload of part `p` of `Br.rec … fl isn cb hv vl vh mem` (after the 19 header fields). -/
def brPay (fl isn : Nat → Expr) (cb : Nat → Nat → Expr) (hv : Expr) (vl vh : Nat → Expr) (mem : List Expr)
    (p : Nat) : List Expr :=
  if p < 16 then [fl p, fl p * isn p] ++ (List.range 32).map fun b => fl p * cb p b
  else [hv, limb16 vl 0, limb16 vl 1] ++ (List.range 32).map vh ++ mem

theorem brRec_get (rf : Expr) (ref : List Expr) (fl isn : Nat → Expr) (cb : Nat → Nat → Expr) (hv : Expr)
    (vl vh : Nat → Expr) (mem : List Expr) (p : Nat) (hp : p < 17) :
    (Br.rec rf ref fl isn cb hv vl vh mem)[p]? =
      some ([K VT_BR, K p, rf] ++ ref ++ brPay fl isn cb hv vl vh mem p) := by
  unfold Br.rec brPay
  by_cases h : p < 16
  · rw [List.getElem?_append_left (by simp; omega)]
    simp [h]
  · have : p = 16 := by omega
    subst this
    rw [List.getElem?_append_right (by simp)]
    simp

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem pk_pack2 (cb : Nat → Expr) (fl : Expr) (hf : fl.eval tr 2 r pub = 1) :
    pk (((List.range 32).map fun b => fl * cb b).map (E tr 2 r pub)) = (pack2 cb).map (E tr 2 r pub) := by
  simp only [pk, pack2, List.map_map]
  apply List.map_congr_left; intro j hj
  have hj' := List.mem_range.1 hj
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 2 * j < 32 by omega), List.getElem?_range (show 2 * j + 1 < 32 by omega),
    Option.map_some, Option.getD_some, E, eval_add, eval_mul, eval_K, hf]
  grind

theorem pk_raw (vh : Nat → Expr) :
    pk ((List.range 32).map (fun b => vh b) |>.map (E tr 2 r pub)) = (pack2 vh).map (E tr 2 r pub) := by
  simp only [pk, pack2, List.map_map]
  apply List.map_congr_left; intro j hj
  have hj' := List.mem_range.1 hj
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 2 * j < 32 by omega), List.getElem?_range (show 2 * j + 1 < 32 by omega),
    Option.map_some, Option.getD_some, E, eval_add, eval_mul, eval_K]
  grind

theorem pk_append (A B : List Fp) (hA : A.length = 32) : pk (A ++ B) = pk A := by
  unfold pk
  apply List.map_congr_left; intro j hj
  have hj' := List.mem_range.1 hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 2 * j < A.length by omega),
    List.getElem?_append_left (show 2 * j + 1 < A.length by omega)]

/-- **Decoding the payloads of a `BR` record.** -/
theorem brDec_rec (fl isn : Nat → Expr) (cb : Nat → Nat → Expr) (hv : Expr) (vl vh : Nat → Expr) (mem : List Expr)
    (hmem : mem.length = 4) :
    brDec.dec (fun p => (brPay fl isn cb hv vl vh mem p).map (E tr 2 r pub)) =
      .branch (if ev tr 2 r pub hv = 1 then
          some (.ref ((E tr 2 r pub (limb16 vl 0)).toNat + 65536 * (E tr 2 r pub (limb16 vl 1)).toNat)
            (bytesOf ((pack2 vh).map (E tr 2 r pub))))
        else none)
        (kidsFrom (fun i => ev tr 2 r pub (fl i))
          (fun i => refOf (E tr 2 r pub (isn i)) ((pack2 (cb i)).map (E tr 2 r pub))) 0 16)
        (le4 (mem.map (E tr 2 r pub))) := by
  have sdec : ∀ i, i < 16 → slotDec ((brPay fl isn cb hv vl vh mem i).map (E tr 2 r pub)) =
      if ev tr 2 r pub (fl i) = 1 then some (refOf (E tr 2 r pub (isn i)) ((pack2 (cb i)).map (E tr 2 r pub)))
      else none := by
    intro i hi
    unfold slotDec brPay
    simp only [hi, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
    by_cases h : ev tr 2 r pub (fl i) = 1
    · have h' : (E tr 2 r pub (fl i)).toNat = 1 := h
      have hf : (fl i).eval tr 2 r pub = 1 := fp_of_ev1 h
      rw [if_pos h', if_pos h, pk_pack2 (cb i) (fl i) hf]
      have e : E tr 2 r pub (fl i * isn i) = E tr 2 r pub (isn i) := by
        simp only [E, eval_mul, hf]; grind
      rw [e]
    · have h' : ¬ (E tr 2 r pub (fl i)).toNat = 1 := h
      rw [if_neg h', if_neg h]
  have vdec : valDec ((brPay fl isn cb hv vl vh mem 16).map (E tr 2 r pub)) =
      if ev tr 2 r pub hv = 1 then
          some (.ref ((E tr 2 r pub (limb16 vl 0)).toNat + 65536 * (E tr 2 r pub (limb16 vl 1)).toNat)
            (bytesOf ((pack2 vh).map (E tr 2 r pub))))
        else none := by
    unfold valDec brPay
    simp only [show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
      List.drop_zero]
    rw [pk_append _ _ (by simp), pk_raw]
    rfl
  have mdec : memDec ((brPay fl isn cb hv vl vh mem 16).map (E tr 2 r pub)) = le4 (mem.map (E tr 2 r pub)) := by
    unfold memDec brPay
    simp only [show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    rw [show (35 : Nat) = 3 + 32 from rfl, ← List.drop_drop]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append]
    rw [List.take_of_length_le (by simp [hmem])]
  show Rec.branch (brDec.g 16 _).2.1 (kidsO (fun i => (brDec.g i _).1) 0 16) (brDec.g 16 _).2.2 = _
  simp only [brDec, show ¬ (16 < 16) from by decide, ↓reduceIte]
  rw [vdec, mdec, kidsFrom_eq]
  congr 1
  apply kidsO_congr; intro j hj
  simp only [Nat.zero_add, hj, ↓reduceIte]
  exact sdec j hj

/-- The old payloads of a `BR` row (the same for its `VER` publication and its reading). -/
def brOldPay (tr : Trace Fp) (pub : List Fp) (r : Nat) (p : Nat) : List Fp :=
  (brPay (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch (Br.c "hasv") (fun t => Br.c "vl" t)
    (fun t => Br.c "vh" t) Br.M p).map (E tr 2 r pub)

def brNewPay (tr : Trace Fp) (pub : List Fp) (r : Nat) (p : Nat) : List Fp :=
  (brPay (fun i => Br.c "nf" i) Br.nisn Br.newch (Br.c "nhv") (fun t => Br.c "nvl" t)
    (fun t => Br.c "nvh" t) Br.NM p).map (E tr 2 r pub)

theorem brOld_dec : brOld tr pub r = brDec.dec (brOldPay tr pub r) := by
  unfold brOldPay; rw [brDec_rec _ _ _ _ _ _ _ (by simp [Br.M, memLimbs])]; rfl

theorem brNew_dec : brNew tr pub r = brDec.dec (brNewPay tr pub r) := by
  unfold brNewPay; rw [brDec_rec _ _ _ _ _ _ _ (by simp [Br.NM, memLimbs])]; rfl

end

end StateM5a.VerDec
