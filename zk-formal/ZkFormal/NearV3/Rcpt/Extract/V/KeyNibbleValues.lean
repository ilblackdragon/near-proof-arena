import ZkFormal.NearV3.Rcpt.Extract.V.KeyAccessMarkers

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Character key symbols are the actual byte's canonical high and low nibbles. -/
theorem key_character_nibbles {q X : Nat} (hq : q<tr.height tt)
    (hx : X=sP ∨ X=sV ∨ X=sS) (hs : tr.cell tt q X=1) :
    hiE.eval tr tt q pub=((cv tr tt q b/16 : Nat):Fp) ∧
    loE.eval tr tt q pub=((cv tr tt q b%16 : Nat):Fp) := by
  obtain ⟨hv,hl,_,hh,hlo⟩ := char_val hL hq hx hs
  have hd : cv tr tt q b/16=hiV tr tt q := by omega
  have hm : cv tr tt q b%16=loV tr tt q := by omega
  rw [hd,hm]
  exact ⟨hh,hlo⟩

/-- Public-key scratch bits authenticate both emitted nibbles of the actual byte. -/
theorem key_public_nibbles {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sPK=1) (he : tr.cell tt q ee=1) :
    hiPK.eval tr tt q pub=((cv tr tt q b/16 : Nat):Fp) ∧
    loPK.eval tr tt q pub=((cv tr tt q b%16 : Nat):Fp) := by
  obtain ⟨hh,hhl⟩ := bitsX_eval hL hq 0 4 (by omega)
  obtain ⟨hl,hll⟩ := bitsX_eval hL hq 4 4 (by omega)
  have hb := ((akey_row hL hq he).2.2.2.2.1 hs).2.2.2.2.2
  change (hiPK).eval tr tt q pub=_ at hh
  change (loPK).eval tr tt q pub=_ at hl
  let hi := bitsVal (fun j => cv tr tt q (xb j)) 0 4
  let lo := bitsVal (fun j => cv tr tt q (xb j)) 4 4
  have hiLt : hi<16 := hhl
  have loLt : lo<16 := hll
  have hv : cv tr tt q b=16*hi+lo := by
    have hv : tr.cell tt q b=((16*hi+lo:Nat):Fp) := by
      rw [hb,hh,hl,natCast_add,natCast_mul]
      change 16*(hi: Fp)+(lo:Fp)=((16:Nat):Fp)*(hi:Fp)+(lo:Fp)
      rw [show ((16:Nat):Fp)=(16:Fp) by decide]
    rw [cv,hv,toNat_natCast,Nat.mod_eq_of_lt (by unfold P; omega)]
  have hd : cv tr tt q b/16=hi := by omega
  have hm : cv tr tt q b%16=lo := by omega
  rw [hd,hm]
  exact ⟨hh,hl⟩

end ZkFormal.NearV3.RcptV3Proof
