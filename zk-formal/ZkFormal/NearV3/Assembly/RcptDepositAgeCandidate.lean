import ZkFormal.NearV3.Assembly.RcptDepositContradiction

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof

/-- Isolated wider version-distance candidate. Storage bits47..56 are used
only on the second DEP row; this candidate uses53..65 on the first DEP row.
Global scratch-patch preservation remains a separate obligation. -/
def depositConstraintsWith (age : Expr) : List Expr :=
  let d (j : Nat) : Expr := c (dl j)
  [ .mul dp (sub (sum [c bef, c b, c c1]) (.add aftE (smul 256 (c (xb 8))))),
    .mul (.mul dp (c fs)) (c c1), mul3 dp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 dp (c fe) (c (xb 8)),
    -- amount ≠ u128::MAX
    mul3 dp (c fs) (sub (c dsum) (sub (k 255) aftE)),
    mul3 dp (not (c fe)) (sub (n dsum) (.add (c dsum) (sub (k 255) (bitsXn 0 8)))),
    mul3 dp (c fe) (sub (.mul (c dsum) (c invB)) (k 1)),
    -- tot = aft + locked < 2^128
    .mul dp (sub (sum [aftE, c lk, c c2]) (.add (bitsX 9 8) (smul 256 (c (xb 17))))),
    .mul (.mul dp (c fs)) (c c2), mul3 dp (not (c fe)) (sub (n c2) (c (xb 17))),
    mul3 dp (c fe) (c (xb 17)),
    -- q = 10^19·storage
    .mul dp (sub (.add (conv S_LE (c st) d) (c c3)) (.add (bitsX 18 8) (smul 256 (bitsX 26 12)))),
    .mul (.mul dp (c fs)) (c c3), mul3 dp (not (c fe)) (sub (n c3) (bitsX 26 12)),
    mul3 dp (c fe) (bitsX 26 12),
    mul3 dp (not (c fe)) (sub (n (dl 0)) (c st)),
    -- tot − q with borrow; no final borrow when `big`
    .mul dp (sub (sub (bitsX 9 8) (bitsX 18 8)) (sub (.add (c c4) (bitsX 38 8)) (smul 256 (c (xb 46))))),
    .mul (.mul dp (c fs)) (c c4), mul3 dp (not (c fe)) (sub (n c4) (c (xb 46))),
    .mul (mul3 dp (c fe) (c big)) (c (xb 46)),
    -- otherwise storage ≤ 770
    .mul (c r1) (not dp), mul3 dp (c fs) (c r1), mul3 dp (not (c fe)) (sub (n r1) (c fs)),
    mul3 (not (c big)) (c r1) (sub (k 770) (sum [c (dl 0), smul 256 (c st), bitsX 47 10])),
    mul3 (not (c big)) (sub (sub dp (c fs)) (c r1)) (c st),
    -- the read is not from the future
    mul3 dp (c fs) (sub (sub (c r) (c tprev)) age) ] ++
  (List.range 7).map (fun j => mul3 dp (c fs) (d j)) ++
  (List.range 6).map (fun j => mul3 dp (not (c fe)) (sub (n (dl (j + 1))) (d j)))

def depositAgeConstraints : List Expr := depositConstraintsWith (bitsX 53 13)

theorem depositConstraintsWith_original : depositConstraintsWith (bitsX 57 9)=cDep := rfl

theorem depositConstraintsWith_length (age : Expr) : (depositConstraintsWith age).length=39 := rfl

/-- Native maximum4481 receipts fits13-bit distance without assuming r<512. -/
theorem native_deposit_age_bound (r previous : Nat) (hr : r<4481) : r-previous<2^13 := by omega

/-- Exact first-row candidate equation lifts to natural version ordering
under explicit canonical bounds; no statement about arbitrary field aliases. -/
theorem candidate_deposit_age_nat (r previous distance : Nat)
    (hr : r<4481) (hp : previous<4481) (hd : distance<2^13)
    (he : (r:Fp)-(previous:Fp)-(distance:Fp)=0) :
    previous≤r ∧ r-previous=distance := by
  have hh : (r:Fp)=((previous+distance:Nat):Fp) := by
    rw [natCast_add]; grind only
  have := ofNat_inj (by unfold ZkFormal.Algebra.P; omega)
    (by unfold ZkFormal.Algebra.P; omega) hh
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
