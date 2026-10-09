import ZkFormal.NearV3.Assembly.RoutingLexComplete
import ZkFormal.NearV3.Assembly.RoutingSelectedColumns

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

structure RouteFrame where
  value : UInt8
  lower : UInt8
  upper : UInt8
  equalLower : Bool
  equalUpper : Bool
  missingUpper : Bool
  first : Bool
  atEnd : Bool
  pos : Nat

def frameOf (acct : Bytes) (iv : Option Bytes×Option Bytes) (pos : Nat) : RouteFrame :=
  ⟨acct.getD pos 0,(iv.1.getD []).getD pos 0,(iv.2.getD []).getD pos 0,
    samePrefix acct (iv.1.getD []) pos,
    !iv.2.isNone && samePrefix acct (iv.2.getD []) pos,
    iv.2.isNone,decide (pos=0),decide (pos=acct.length),pos⟩

/-- Ordinary byte-order obligations, independent of AIR constraints. -/
structure RouteFrame.Ordered (f : RouteFrame) : Prop where
  lower : f.equalLower=true → f.lower.toNat≤f.value.toNat
  upper : f.equalUpper=true → f.value.toNat≤f.upper.toNat
  strictEnd : f.atEnd=true → f.equalUpper=true → f.value.toNat<f.upper.toNat
  firstLower : f.first=true → f.equalLower=true
  firstUpper : f.first=true → f.equalUpper= !f.missingUpper
  endZero : f.atEnd=true → f.value=0

/-- The native interval predicate supplies every comparison obligation of the
generated receiver/end-marker frame, including strictness at the end. -/
theorem frameOf_ordered (acct : Bytes) (iv : Option Bytes×Option Bytes) (pos : Nat)
    (hp : pos≤acct.length) (hv : inInterval acct iv=true)
    (hupper : ∀b∈iv.2.getD [],0<b.toNat) : (frameOf acct iv pos).Ordered := by
  have hbounds : lexLe (iv.1.getD []) acct=true ∧
      (iv.2.isNone=true ∨ lexLe (iv.2.getD []) acct=false) := by
    rcases iv with ⟨lo,hi⟩
    cases lo <;> cases hi <;> simp_all [inInterval,lexLe]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro he
    apply lexLe_prefix_lower pos _ acct hp hbounds.1
    intro k hk
    exact ((samePrefix_iff _ _ pos).mp he k hk).symm
  · intro he
    have he' : iv.2.isNone=false ∧ samePrefix acct (iv.2.getD []) pos=true := by
      simpa only [frameOf,Bool.and_eq_true,Bool.not_eq_true'] using he
    exact (lexLe_prefix_upper pos _ acct hupper hp (by grind)
      ((samePrefix_iff _ _ pos).mp he'.2)).1
  · intro hend he
    have he' : iv.2.isNone=false ∧ samePrefix acct (iv.2.getD []) pos=true := by
      simpa only [frameOf,Bool.and_eq_true,Bool.not_eq_true'] using he
    have hp' : pos=acct.length := by simpa [frameOf] using hend
    exact (lexLe_prefix_upper pos _ acct hupper hp (by grind)
      ((samePrefix_iff _ _ pos).mp he'.2)).2 hp'
  · intro hf
    have hp' : pos=0 := by simpa [frameOf] using hf
    simp [frameOf,hp',samePrefix]
  · intro hf
    have hp' : pos=0 := by simpa [frameOf] using hf
    simp [frameOf,hp',samePrefix]
  · intro he
    have hp' : pos=acct.length := by simpa [frameOf] using he
    simp [frameOf,hp',List.getD_eq_getElem?_getD]

def frameBit (x j : Nat) : Fp := Fp.ofNat ((x/2^j)%2)

def frameInverse (a b : UInt8) : Fp := ((a.toNat:Fp)-(b.toNat:Fp))⁻¹

/-- All eighteen cRoute polynomials use only this row and the two next-prefix
bits. This is the executable arithmetic frame for the future receipt renderer. -/
def frameCell (f : RouteFrame) (col : Nat) : Fp :=
  if col=iL then frameInverse f.value f.lower else
  if col=iH then frameInverse f.upper f.value else
  if col=sV then (if f.atEnd then 0 else 1) else
  if col=sRID then (if f.atEnd then 1 else 0) else
  if col=fs then (if f.first || f.atEnd then 1 else 0) else
  if col=idx || col=Lv || col=iB then Fp.ofNat f.pos else
  if col=b || col=vB then Fp.ofNat f.value.toNat else
  if col=loB then Fp.ofNat f.lower.toNat else
  if col=hiB then Fp.ofNat f.upper.toNat else
  if col=hnB then (if f.missingUpper then 1 else 0) else
  if col=eqL then (if f.equalLower then 1 else 0) else
  if col=eqH then (if f.equalUpper then 1 else 0) else
  if col=gBd then (if f.equalLower || f.equalUpper then 1 else 0) else
  if col=eL then (if f.value=f.lower then 1 else 0) else
  if col=eH then (if f.upper=f.value then 1 else 0) else
  if xb 20≤col ∧ col<xb 29 then frameBit (f.value.toNat+255-f.lower.toNat) (col-xb 20) else
  if xb 29≤col ∧ col<xb 38 then frameBit (f.upper.toNat+255-f.value.toNat) (col-xb 29) else 0

def frameNext (f : RouteFrame) (col : Nat) : Fp :=
  if col=eqL then (if f.equalLower && (f.value==f.lower) then 1 else 0) else
  if col=eqH then (if f.equalUpper && (f.upper==f.value) then 1 else 0) else 0

def frameTrace (f : RouteFrame) : Trace Fp :=
  ⟨fun _=>1,fun _ r=>if r=0 then frameCell f else frameNext f⟩

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
