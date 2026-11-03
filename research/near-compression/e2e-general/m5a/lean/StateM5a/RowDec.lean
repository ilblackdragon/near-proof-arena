import StateM5a.DecodeShape

/-!
# StateM5a.RowDec — a concrete decoder of the walk messages, and the `BR` / `SN` walk messages

`DecodeWalk.Dec` is any field decoder; this file fixes the one the per-row proofs use (`cDc`).
Every field is read **as the field element the bus carries** (no range fact is needed to decode;
range facts are needed only where a decoded value is compared with bytes hashed by SHA-256):

* a ref is `(flag, 16 limbs)`: flag `1` → version id `limb₀` (as a natural), otherwise the digest
  whose bytes are the limbs split big-endian (`bytesOf`: `l ↦ [l / 256, l mod 256]`);
* `DOWN` payload `(kid, mode, vlen, vh₁₆)`: naturals and `bytesOf vh`;
* `UP` result `(rk, ref, nm₄, om₄, kid2, st2, alen, avh₁₆, fpres)`: memory limbs little-endian in
  base `2^16` (`le4`).

The message lists of `BR` / `SN` on `DOWN` / `UP` (read off the exported tables, `filt`) are
`br_di` … `sn_uo`.
-/

namespace StateM5a.RowDec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec

/-! ## The decoder -/

def limbBytes (l : Fp) : Bytes := [UInt8.ofNat (l.toNat / 256), UInt8.ofNat (l.toNat % 256)]

/-- Bytes of 16-bit big-endian limbs. -/
def bytesOf (ls : List Fp) : Bytes := ls.flatMap limbBytes

/-- A ref from its flag and limbs. -/
def refOf (fl : Fp) (ls : List Fp) : Ref :=
  if fl.toNat = 1 then .vid (ls.getD 0 0).toNat else .dig (bytesOf ls)

/-- Four 16-bit limbs, little-endian. -/
def le4 (ls : List Fp) : Nat :=
  (ls.getD 0 0).toNat + 65536 * (ls.getD 1 0).toNat + 4294967296 * (ls.getD 2 0).toNat +
    281474976710656 * (ls.getD 3 0).toNat

def payOf (m : List Fp) : Pay :=
  ⟨(m.getD 0 0).toNat, (m.getD 1 0).toNat, (m.getD 2 0).toNat, bytesOf ((m.drop 3).take 16)⟩

def resOf (m : List Fp) : Res :=
  ⟨(m.getD 0 0).toNat, refOf (m.getD 1 0) ((m.drop 2).take 16), le4 ((m.drop 18).take 4),
    le4 ((m.drop 22).take 4), (m.getD 26 0).toNat, (m.getD 27 0).toNat, (m.getD 28 0).toNat,
    bytesOf ((m.drop 29).take 16), (m.getD 45 0).toNat⟩

/-- **The concrete decoder.** -/
def cDc : Dec Ref Pay Res where
  dp m := (refOf (m.getD 0 0) ((m.drop 1).take 16), payOf (m.drop 17))
  dr := resOf

/-! ## The `BR` / `SN` walk messages -/

set_option maxRecDepth 100000

/-- `DOWN` payload expressions (shared by `BR` / `SN`, receive and send). -/
def payE (c : String → Nat → Expr) (mode : Expr) : List Expr :=
  [c "kid" 0, mode, c "dvlen" 0] ++ (List.range 16).map fun i => c "dvh" i

theorem br_di : brW.di = [Br.c "w", Br.c "d", Br.c "oref"] ++ pack2 (fun b => Br.c "ho" b) ++
    payE (fun s j => Br.c s j) Br.mode := by
  simp [brW, payE]; filt

theorem br_dd : brW.dd = [Br.c "w", Br.c "d" + 1, Br.isnSel] ++ pack2 Br.chSel ++
    payE (fun s j => Br.c s j) Br.mode := by
  simp [brW, payE]; filt

theorem br_ui : brW.ui = [Br.c "w", Br.c "d" + 1, Br.c "rk",
      (Br.c "oUD" + Br.c "oDH") * Br.c "nhf" + Br.c "oDS" * Br.isnSel] ++
    ((pack2 (fun b => Br.c "nh" b)).zip (pack2 Br.chSel)).map
      (fun (p, q) => (Br.c "oUD" + Br.c "oDH") * p + Br.c "oDS" * q) ++
    ((List.range 4).map fun k => (Br.c "oUD" + Br.c "oDH") * Br.c "nm" k) ++
    ((List.range 4).map fun k => Br.c "om" k) ++
    [Br.c "oDL" * Br.c "kid2", Br.c "oDL" * Br.c "st2", (Br.c "oFD" + Br.c "oDL") * Br.c "lvlen"] ++
    ((List.range 16).map fun i => (Br.c "oFD" + Br.c "oDL") * Br.c "lvh" i) ++
    [Br.c "oFD" * Br.c "fpres"] := by
  simp [brW]; filt

theorem br_uo : brW.uo = [Br.c "w", Br.c "d",
      Br.c "oUD" + Br.c "oUN" + Br.c "oUV" + sm 2 (Br.gKeep + Br.c "oDV") + sm 4 (Br.c "oD1") +
        sm RK_SAME Br.gSame,
      Br.c "gnew" * Br.c "nref" + Br.gSame * Br.c "oref"] ++
    ((pack2 (fun b => Br.c "hn" b)).zip (pack2 fun b => Br.c "ho" b)).map
      (fun (p, q) => Br.c "gnew" * p + Br.gSame * q) ++
    Br.NM.map (Br.c "gnew" * ·) ++ Br.M.map ((Br.c "mU" + Br.c "mD") * ·) ++
    [Br.c "oD1" * Br.c "kid2", Br.c "oD1" * Br.c "d",
      (Br.c "oFD" + Br.c "oD1") * Br.c "lvlen" + Br.c "oFV" * Br.vlen] ++
    ((List.range 16).zip (pack2 fun b => Br.c "vh" b)).map
      (fun (i, p) => (Br.c "oFD" + Br.c "oD1") * Br.c "lvh" i + Br.c "oFV" * p) ++
    [Br.c "oFD" * Br.c "fpres" + Br.c "oFV" * Br.c "hasv"] := by
  simp [brW]; filt


/-! ## Decoding a message of the walk shape -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- Field value of an expression on the row. -/
abbrev E (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) : Fp := e.eval tr t r pub

theorem eval_add (a b : Expr) : (a + b).eval tr t r pub = a.eval tr t r pub + b.eval tr t r pub := rfl
theorem eval_sub (a b : Expr) : (a - b).eval tr t r pub = a.eval tr t r pub + -b.eval tr t r pub := rfl
theorem eval_mul (a b : Expr) : (a * b).eval tr t r pub = a.eval tr t r pub * b.eval tr t r pub := rfl
theorem eval_sm (v : Nat) (a : Expr) : (sm v a).eval tr t r pub = (@Nat.cast Fp Lean.Grind.Semiring.natCast v) * a.eval tr t r pub := rfl
theorem eval_K (v : Nat) : (K v).eval tr t r pub = @Nat.cast Fp Lean.Grind.Semiring.natCast v := rfl
theorem eval_lit (v : Nat) : (no_index (OfNat.ofNat v : Expr)).eval tr t r pub = @Nat.cast Fp Lean.Grind.Semiring.natCast v := rfl
theorem ev_eq_of_eval {a b : Expr} (h : a.eval tr t r pub = b.eval tr t r pub) :
    ev tr t r pub a = ev tr t r pub b := by unfold ev; rw [h]
theorem eval_of_ev {a : Expr} {n : Nat} (h : ev tr t r pub a = n) (hn : n < 2013265921) :
    a.eval tr t r pub = Fp.ofNat n := Fp.ext (by rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (show n < ZkFormal.Algebra.P from hn)]; exact h)

/-- Simp set: field values of composite expressions. -/
macro "evs" : tactic => `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_sm, eval_K, eval_lit] at *)

theorem down_eq (w d f : Expr) (L PE : List Expr) (hL : L.length = 16) :
    cDc.down (vals tr t r pub ([w, d, f] ++ L ++ PE)) =
      ⟨ev tr t r pub w, ev tr t r pub d, refOf (E tr t r pub f) (L.map (E tr t r pub)),
        payOf (PE.map (E tr t r pub))⟩ := by
  match L, hL with
  | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15], _ => rfl

theorem up_eq (w d rk f a b c fp : Expr) (L N O A : List Expr) (hL : L.length = 16)
    (hN : N.length = 4) (hO : O.length = 4) (hA : A.length = 16) :
    cDc.dr ((vals tr t r pub ([w, d, rk, f] ++ L ++ N ++ O ++ [a, b, c] ++ A ++ [fp])).drop 2) =
      ⟨ev tr t r pub rk, refOf (E tr t r pub f) (L.map (E tr t r pub)), le4 (N.map (E tr t r pub)),
        le4 (O.map (E tr t r pub)), ev tr t r pub a, ev tr t r pub b, ev tr t r pub c,
        bytesOf (A.map (E tr t r pub)), ev tr t r pub fp⟩ := by
  match L, N, O, A, hL, hN, hO, hA with
  | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15], [n0, n1, n2, n3],
    [o0, o1, o2, o3], [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _, _, _, _ =>
    rfl

end

end StateM5a.RowDec
