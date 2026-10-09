import ZkFormal.NearV3.Assembly.RcptCandidateGasDelayLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

def gasSingleProduct (x out carry bits : Expr) (carryNext : Expr) (d : Nat→Expr) : List Expr :=
  [ .mul gp (sub (.add out (smul 256 bits)) (.add (conv (G_LE.take 5) x d) carry)),
    .mul (.mul gp (c fs)) carry,
    mul3 gp (not (c fe)) (sub carryNext bits),
    mul3 gp (c fe) bits,
    mul3 gp (c fe) (ovf x d) ]

theorem gasSingleProduct_local (tr : Trace Fp) (tt row : Nat) (pub : List Fp)
    (x out carry bits carryNext : Expr) (d : Nat→Expr) (v i : Nat) (hi : i<16)
    (hv : Params.G*v<256^16)
    (hg : tr.cell tt row sGP=1)
    (hfs : tr.cell tt row fs=if i=0 then 1 else 0)
    (hfe : tr.cell tt row fe=if i+1=16 then 1 else 0)
    (hx : x.eval tr tt row pub=Fp.ofNat (gasByte v i))
    (ho : out.eval tr tt row pub=Fp.ofNat (gasByte (Params.G*v) i))
    (hc : carry.eval tr tt row pub=Fp.ofNat (gasMulCarry v i))
    (hb : bits.eval tr tt row pub=Fp.ofNat (gasMulCarry v (i+1)))
    (hn : i+1<16→carryNext.eval tr tt row pub=Fp.ofNat (gasMulCarry v (i+1)))
    (hd : ∀j<4,(d j).eval tr tt row pub=Fp.ofNat (byteDelay (gasByte v) j i)) :
    ∀e∈gasSingleProduct x out carry bits carryNext d,e.eval tr tt row pub=0 := by
  have hconv : (conv (G_LE.take 5) x d).eval tr tt row pub=Fp.ofNat (gasMulDigits v i) := by
    have he := congrArg Fp.ofNat (convG_row (gasByte v) i)
    simp only [ofNat_add_e,ofNat_mul_e] at he
    change (sum [smul 196 x,smul 164 (d 0),smul 183 (d 1),smul 246 (d 2),smul 51 (d 3)]).eval tr tt row pub=_
    simp only [eval_sum_cons,eval_sum_nil,eval_smul,hx,hd 0 (by decide),hd 1 (by decide),hd 2 (by decide),hd 3 (by decide),byteDelay]
    change _=Fp.ofNat (ZkFormal.Near.Render.RcptGen.conv (Rcpt.G_LE.take 5) (gasByte v) i)
    simp only [natCast_eq]
    grind only
  intro e he
  simp only [gasSingleProduct,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl
  · have he := congrArg Fp.ofNat (gasMul_step v hv i hi)
    simp only [ofNat_add_e,ofNat_mul_e] at he
    simp only [gp,eval_mul,eval_sub,eval_add,eval_smul,eval_c,hg,ho,hb,hconv,hc,natCast_eq]
    grind only
  · simp only [gp,eval_mul,eval_c,hg,hfs,hc]
    by_cases hz : i=0
    · subst i;simp only [ite_true,gasMulCarry_zero,show Fp.ofNat 0=(0:Fp) from rfl];grind only
    · rw [if_neg hz];grind only
  · simp only [gp,eval_mul3,eval_not,eval_sub,eval_c,hg,hfe,hb]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hn (by omega)];grind only
  · simp only [gp,eval_mul3,eval_c,hg,hfe,hb]
    by_cases he : i+1=16
    · rw [if_pos he,he,gasMulCarry_final v hv];change 1*1*0=0;grind only
    · rw [if_neg he];grind only
  · simp only [gp,eval_mul3,eval_c,hg,hfe]
    by_cases he : i+1=16
    · have he' : i=15 := by omega
      subst i
      simp only [ite_true,ovf,eval_sum_cons,eval_sum_nil,eval_smul,hx,
        hd 0 (by decide),hd 1 (by decide),hd 2 (by decide),byteDelay,
        Nat.reduceLT,ite_true,Nat.reduceSub,gasMul_top_zero v hv 15 (by decide),
        gasMul_top_zero v hv 14 (by decide),gasMul_top_zero v hv 13 (by decide),
        gasMul_top_zero v hv 12 (by decide),show Fp.ofNat 0=(0:Fp) from rfl]
      grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
