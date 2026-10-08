import ZkFormal.NearV3.Assembly.RcptGasDelayFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Isolated candidate: use the existing non-system comparison gate. -/
def systemSurplus : Expr := .mul (c gq) DE

def gasConstraintsWith (surplus : Expr) : List Expr :=
  let d (i : Nat) : Expr := c (dl i)
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1), mul3 gp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 gp (c fe) (sub (c (xb 8)) (not (c ge))),
    -- effective burn price: `p` (`0` for system receipts); `gq = ge·(1 − sys)`
    .mul gp (sub (c pc) (.mul (not (c sys)) pE)),
    .mul rowE (sub (c gq) (.mul (c ge) (not (c sys)))),
    -- burnt = G·pc
    .mul gp (sub (.add (c burnt) (smul 256 (bitsX 9 11))) (.add (conv (G_LE.take 5) (c pc) d) (c c2))),
    .mul (.mul gp (c fs)) (c c2), mul3 gp (not (c fe)) (sub (n c2) (bitsX 9 11)),
    mul3 gp (c fe) (bitsX 9 11), mul3 gp (c fe) (ovf (c pc) d),
    -- refund amount = G·surplus
    .mul gp (sub (.add (c ramt) (smul 256 (bitsX 20 11)))
      (.add (conv (G_LE.take 5) surplus (fun i => d (4 + i))) (c c3))),
    .mul (.mul gp (c fs)) (c c3), mul3 gp (not (c fe)) (sub (n c3) (bitsX 20 11)),
    mul3 gp (c fe) (bitsX 20 11), mul3 gp (c fe) (ovf surplus (fun i => d (4 + i))),
    -- running tokens
    .mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0), c burnt, c c4])),
    .mul (.mul gp (c fs)) (c c4), mul3 gp (not (c fe)) (sub (n c4) (c (xb 39))),
    mul3 gp (c fe) (c (xb 39)),
    -- refund flag: (non-system) surplus bytes vanish without a refund; a refund has a
    -- nonzero surplus
    .mul (mul3 gp (not (c hr)) (c gq)) DE,
    mul3 gp (c fs) (sub (c sumD) DE),
    mul3 gp (not (c fe)) (sub (n sumD) (.add (c sumD) DEn)),
    mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c hr)) ] ++
  -- delay lines of pc and surplus
  (List.range 8).map (fun i => mul3 gp (c fs) (d i)) ++
  [ mul3 gp (not (c fe)) (sub (n (dl 0)) (c pc)), mul3 gp (not (c fe)) (sub (n (dl 4)) surplus) ] ++
  ([1, 2, 3, 5, 6, 7].map fun i => mul3 gp (not (c fe)) (sub (n (dl i)) (d (i - 1))))

/-- The parameterized transcription is exactly the original constraint family. -/
theorem gasConstraintsWith_original : gasConstraintsWith surE=cGas := rfl

/-- No columns, rows, or polynomial count are added by this candidate. -/
theorem gasConstraintsWith_length (surplus : Expr) : (gasConstraintsWith surplus).length=40 := rfl

def systemGasConstraints : List Expr := gasConstraintsWith systemSurplus

/-- Actual native surplus stream: system receipts do not create a refund. -/
def gasNativeSurplusByte (ctx : ApplyCtx) (r : Receipt) (i : Nat) : Nat :=
  if r.predecessorId == AccountId.system then 0 else gasRawSurplusByte ctx r i

theorem gasNativeSurplusByte_system (ctx : ApplyCtx) (r : Receipt) (i : Nat)
    (h : r.predecessorId=AccountId.system) : gasNativeSurplusByte ctx r i=0 := by
  simp [gasNativeSurplusByte,h]

theorem gasNativeSurplusByte_ordinary (ctx : ApplyCtx) (r : Receipt) (i : Nat)
    (h : r.predecessorId≠AccountId.system) :
    gasNativeSurplusByte ctx r i=gasRawSurplusByte ctx r i := by
  simp [gasNativeSurplusByte,h]

theorem systemSurplus_zero (tr : Trace Fp) (tt row : Nat) (pub : List Fp)
    (h : tr.cell tt row gq=0) : systemSurplus.eval tr tt row pub=0 := by
  simp only [systemSurplus,eval_mul,eval_c,h]; grind only

theorem systemSurplus_ordinary (tr : Trace Fp) (tt row : Nat) (pub : List Fp)
    (h : tr.cell tt row gq=tr.cell tt row ge) :
    systemSurplus.eval tr tt row pub=surE.eval tr tt row pub := by
  simp [systemSurplus,surE,eval_mul,eval_c,h]

/-- Every original polynomial is preserved pointwise for an ordinary receipt. -/
theorem systemGasConstraints_ordinary (tr : Trace Fp) (tt row : Nat) (pub : List Fp)
    (h : tr.cell tt row gq=tr.cell tt row ge) :
    systemGasConstraints.map (fun e=>e.eval tr tt row pub)=
      cGas.map (fun e=>e.eval tr tt row pub) := by
  have hs := systemSurplus_ordinary tr tt row pub h
  simp only [systemGasConstraints,gasConstraintsWith,cGas,List.map_append,List.map_cons,List.map_nil]
  simp [conv,G_LE,List.range_succ,ovf,eval_mul,eval_sub,eval_add,eval_mul3,eval_sum_cons,eval_sum_nil,eval_smul,hs]


end ZkFormal.NearV3.Assembly.RcptSkeleton
