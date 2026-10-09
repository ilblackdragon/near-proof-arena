import ZkFormal.NearV3.Assembly.RcptSystemGasZero

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasProductColumn (col : Nat) : Bool :=
  col∈[sGP,fs,fe,pc,gq,burnt,ramt,c2,c3] || decide (xb 0≤col ∧ col<xb 31) ||
    decide (dl 0≤col ∧ col<dl 8)

def gasProductFootprint : Expr→Bool
  | .const _ | .pub _=>true
  | .col col nx=>if nx then col∈[c2,c3] else gasProductColumn col
  | .add a b | .mul a b=>gasProductFootprint a && gasProductFootprint b
  | .neg a=>gasProductFootprint a
  | _=>false

theorem gasProduct_footprint : (gasProductConstraints systemSurplus).all gasProductFootprint=true := by decide

theorem gasProduct_no_emission (col : Nat) (hc : gasProductColumn col=true) : emissionColumn col=false := by
  simp only [gasProductColumn,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hc
  simp only [sGP,fs,fe,pc,gq,burnt,ramt,c2,c3,xb,dl] at hc
  simp only [emissionColumn,decide_eq_false_iff_not]
  omega

theorem gasProduct_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,gasProductColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hn : ∀col,col∈[c2,c3]→tr.cell t ((pos+1)%tr.height t) col=
      tr'.cell t' ((pos'+1)%tr'.height t') col)
    (e : Expr) (he : gasProductFootprint e=true) : e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx =>
    cases nx
    · exact hc col he
    · exact hn col (of_decide_eq_true he)
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : gasProductFootprint a=true ∧ gasProductFootprint b=true := by simpa only [gasProductFootprint,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : gasProductFootprint a=true ∧ gasProductFootprint b=true := by simpa only [gasProductFootprint,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem gasProduct_inactive (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sGP=0) :
    ∀e∈gasProductConstraints systemSurplus,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [gasProductConstraints,gasConstraintsWith] at he
  change e∈[_,_,_,_,_,_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [gp,eval_mul,eval_mul3,eval_c,hz]
  all_goals grind only

/-- Final GP row has no successor requirement; padding and wrap are harmless. -/
theorem gasProduct_last_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hf : tr.cell 0 pos fe=1) (hg : tr.cell 0 pos gq=0)
    (hz : ∀col,col∈systemGasZeroCols→tr.cell 0 pos col=0) :
    ∀e∈gasProductConstraints systemSurplus,e.eval tr 0 pos pub=0 := by
  have z0 := hz (pc) (by decide)
  have z1 := hz (burnt) (by decide)
  have z2 := hz (ramt) (by decide)
  have z3 := hz (c2) (by decide)
  have z4 := hz (c3) (by decide)
  have z5 := hz (dl 0) (by decide)
  have z6 := hz (dl 1) (by decide)
  have z7 := hz (dl 2) (by decide)
  have z8 := hz (dl 3) (by decide)
  have z9 := hz (dl 4) (by decide)
  have z10 := hz (dl 5) (by decide)
  have z11 := hz (dl 6) (by decide)
  have z12 := hz (dl 7) (by decide)
  have z13 := hz (xb 9) (by decide)
  have z14 := hz (xb 10) (by decide)
  have z15 := hz (xb 11) (by decide)
  have z16 := hz (xb 12) (by decide)
  have z17 := hz (xb 13) (by decide)
  have z18 := hz (xb 14) (by decide)
  have z19 := hz (xb 15) (by decide)
  have z20 := hz (xb 16) (by decide)
  have z21 := hz (xb 17) (by decide)
  have z22 := hz (xb 18) (by decide)
  have z23 := hz (xb 19) (by decide)
  have z24 := hz (xb 20) (by decide)
  have z25 := hz (xb 21) (by decide)
  have z26 := hz (xb 22) (by decide)
  have z27 := hz (xb 23) (by decide)
  have z28 := hz (xb 24) (by decide)
  have z29 := hz (xb 25) (by decide)
  have z30 := hz (xb 26) (by decide)
  have z31 := hz (xb 27) (by decide)
  have z32 := hz (xb 28) (by decide)
  have z33 := hz (xb 29) (by decide)
  have z34 := hz (xb 30) (by decide)

  have hs := systemSurplus_zero tr 0 pos pub hg
  have hb9 : (bitsX 9 11).eval tr 0 pos pub=0 := by
    simp [bitsX,bits,List.range_succ,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34]
    grind only
  have hb20 : (bitsX 20 11).eval tr 0 pos pub=0 := by
    simp [bitsX,bits,List.range_succ,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34]
    grind only
  intro e he
  simp only [gasProductConstraints,gasConstraintsWith] at he
  change e∈[_,_,_,_,_,_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [conv,G_LE,List.range_succ,ovf,eval_mul3,eval_mul,eval_add,eval_sub,
    eval_sum_cons,eval_sum_nil,eval_smul,eval_c,eval_n,eval_not,hs,hb9,hb20,hf,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
