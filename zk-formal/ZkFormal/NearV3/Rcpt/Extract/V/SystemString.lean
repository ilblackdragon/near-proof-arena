import ZkFormal.NearV3.Rcpt.Extract.V.SystemFlag
import ZkFormal.NearV3.Rcpt.Extract.V.SmallSquares

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- A system-flagged six-byte predecessor is exactly the native system string.
The natural sum of squared byte distances is below the field modulus. -/
theorem system_string_of_flag (hL : TableLocal RcptV3.table tr tt pub) {s r0 : Nat}
    (F : RFld tr tt s r0 6 sP) (hH : r0+6<tr.height tt)
    (hLc : ∀ k,k<6 → tr.cell tt (r0+k) RcptV3.Lp=(6:Fp))
    (hsys : tr.cell tt (r0+5) RcptV3.sys=1) :
    toBytes (colAt tr tt r0 6 b)=AccountId.system := by
  let sy : Nat→Nat := fun k => [115,121,115,116,101,109].getD k 0
  let dist : Nat→Nat := fun k => sqDistance (cv tr tt (r0+k) b) (sy k)
  have hfs : tr.cell tt r0 fs=1 := by simpa using F.fld.fs 0 (by omega)
  have hst : tr.cell tt r0 sP=1 := by simpa using F.fld.st 0 (by omega)
  have hreg : ∀ k,k<6 → tr.cell tt (r0+k) (reg 0)=((sy k:Nat):Fp) := by
    intro k hk
    rw [fld_reg hL (by omega) F.fld (by simp [states]) (by decide) k hk 0 (by omega),Nat.zero_add,
      reg_load hL (by omega) (X:=sP) (l:=ks [115,121,115,116,101,109]) (by simp [loads]) hst hfs k (by simp [ks]; omega),
      ks_get [115,121,115,116,101,109] k (by simp; omega) r0]
  have hsq : ∀ k,k<6 →
      (tr.cell tt (r0+k) b-tr.cell tt (r0+k) (reg 0)) *
      (tr.cell tt (r0+k) b-tr.cell tt (r0+k) (reg 0)) = ((dist k:Nat):Fp) := by
    intro k hk
    rw [hreg k hk,cell_eq_cast tr tt (r0+k) b]
    exact (sqDistance_cast _ _).symm
  have ha : ∀ k,k<6 → tr.cell tt (r0+k) acc=((smallSum dist (k+1):Nat):Fp) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have cc := con hL (r:=r0) (by omega)
        (e:=mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0)))))) (mem_ch (by simp [cChars]))
      simp only [sq,eval_mul3,eval_mul,eval_c,eval_sub] at cc
      rw [hst,hfs] at cc
      have hh := hsq 0 (by omega)
      simp only [Nat.add_zero] at hh
      rw [hh] at cc
      simp only [smallSum,Nat.zero_add,Nat.add_zero]
      grind
    | succ k ih =>
      intro hk
      have cc := con hL (r:=r0+k) (by omega)
        (e:=mul3 (c sP) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))))
        (mem_ch (by simp [cChars]))
      simp only [sq,eval_mul3,eval_mul,eval_c,eval_not,eval_sub,eval_add,eval_n,
        nxt (show r0+k+1<tr.height tt by omega)] at cc
      rw [F.fld.st k (by omega),F.fld.fe k (by omega),if_neg (by omega),ih (by omega),
        show r0+k+1=r0+(k+1) by omega,hsq (k+1) hk] at cc
      rw [smallSum,natCast_add]
      grind
  have cp := con hL (r:=r0+5) (by omega)
    (e:=mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c RcptV3.Lp) (k 6))))))
    (mem_ch (by simp [cChars]))
  have cz := con hL (r:=r0+5) (by omega)
    (e:=.mul (mul3 (c sP) (c fe) (c RcptV3.sys)) (c p1)) (mem_ch (by simp [cChars]))
  simp only [sq,eval_mul3,eval_mul,eval_c,eval_sub,eval_add,eval_k] at cp cz
  rw [F.fld.st 5 (by omega),F.fld.fe 5 (by omega),if_pos rfl,hLc 5 (by omega),ha 5 (by omega)] at cp
  rw [F.fld.st 5 (by omega),F.fld.fe 5 (by omega),if_pos rfl,hsys] at cz
  have hz : ((smallSum dist 6:Nat):Fp)=0 := by grind
  have hd : ∀ k,k<6 → dist k<32768 := by
    intro k hk
    apply sqDistance_lt
    · exact (row_char hL (q:=r0+k) (by omega) (by simp) (F.fld.st k hk)).1
    · have hh : ∀ k,k<6 → [115,121,115,116,101,109].getD k 0<128 := by decide
      exact hh k hk
  have hb := smallSum_lt dist 6 hd
  have hn : smallSum dist 6=0 := ofNat_inj (by unfold P; omega) (by decide) hz
  have he : ∀ k,k<6 → cv tr tt (r0+k) b=sy k := by
    intro k hk
    exact sqDistance_zero (smallSum_zero dist 6 hn k hk)
  apply List.ext_getElem
  · simp [toBytes,colAt_len,AccountId.system]
  · intro k hk hk'
    have hk6 : k<6 := by simpa [toBytes,colAt_len] using hk
    have hv : (toBytes (colAt tr tt r0 6 b))[k]=UInt8.ofNat (cv tr tt (r0+k) b) := by simp [toBytes,colAt]
    have hs : ∀ k,(hk:k<6) → AccountId.system[k]'(by simp [AccountId.system]; omega)=UInt8.ofNat (sy k) := by decide
    exact hv.trans ((congrArg UInt8.ofNat (he k hk6)).trans (hs k hk6).symm)

end ZkFormal.NearV3.RcptV3Proof
