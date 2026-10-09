import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorAdjacent
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecAccumulator ProcPriorCodecAccumulatorAdjacent

private theorem cast_add (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.add_def,Fp.toNat_add]
  exact Nat.add_mod _ _ _
private theorem cast_mul (a b : Nat) : Fp.ofNat (a*b)=Fp.ofNat a*Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.mul_def,Fp.toNat_mul]
  exact Nat.mul_mod _ _ _
private theorem cast_mod (a : Nat) : Fp.ofNat (a%P)=Fp.ofNat a := by
  apply Fp.ext
  simp

/-- The five original accumulator and weight equations hold on actual consecutive
executable rows, without a cell-shape or AIR-evaluation premise. -/
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s mid out : State)
    (hk : k<R.n*R.n) (hg : gg<7)
    (ha : step I R present gb fwd inst k 2 gg s=.ok (.yield mid))
    (hb : step I R present gb fwd inst k 2 (gg+1) mid=.ok (.yield out))
    (first last trans : Fp) :
    ∃a b,mid.1=s.1.push a ∧ out.1=mid.1.push b ∧
      ∀e∈(cRec.drop 25).take 5,e.evalWith
        (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!) first last trans)=0 := by
  obtain ⟨a,b,har,hbr,hap,hapost,hbig⟩ := adjacent I R present gb fwd inst k gg s mid out hk hg ha hb
  obtain ⟨a',ha'r,hpre,hnzb,hpost,hlow,hwt,he2⟩ := ProcPriorCodecAllowanceData.cells I R present gb fwd inst k gg s mid (by omega) hk ha
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  have hs : Fp.ofNat b[apost]! = Fp.ofNat a[apost]! +
      Fp.ofNat a[lowf]! * Fp.ofNat a[wt]! * Fp.ofNat a[bpost]! := by
    rw [hapost,hlow,hwt,hpost,cast_mod,cast_add,cast_mul]
    by_cases hlow : gg<3
    · simp only [hlow,ite_true,show Fp.ofNat 1=(1:Fp) from rfl]; grind
    · simp only [postByte,hlow,ite_false,show Fp.ofNat 0=(0:Fp) from rfl]; grind
  obtain ⟨b',hb'r,_,_,_,hblow,hbwt,_⟩ := ProcPriorCodecAllowanceData.cells I R present gb fwd inst k (gg+1) mid out (by omega) hk hb
  have he' : b'=b := Array.push_inj_right.mp (hb'r.symm.trans hbr)
  subst b'
  have hweight : Fp.ofNat b[wt]! = (256:Fp)*Fp.ofNat a[wt]! := by
    rw [hbwt,hwt,cast_mod,cast_mod,Nat.pow_succ,cast_mul]
    change Fp.ofNat (256^gg)*(256:Fp)=256*Fp.ofNat (256^gg)
    grind only
  have hselector : Fp.ofNat b[lowf]! = Fp.ofNat a[lowf]!*(1-Fp.ofNat a[e2]!) := by
    rw [hblow,hlow,he2]
    have hc : gg=0 ∨ gg=1 ∨ gg=2 ∨ 3≤gg := by omega
    rcases hc with rfl|rfl|rfl|hc
    · change (1:Fp)=1*(1-0); grind only
    · change (1:Fp)=1*(1-0); grind only
    · change (0:Fp)=1*(1-1); grind only
    · have h1 : ¬gg<3 := by omega
      have h2 : ¬gg+1<3 := by omega
      have h3 : gg≠2 := by omega
      simp only [h1,h2,h3,ite_false,show Fp.ofNat 0=(0:Fp) from rfl]
      grind only
  refine ⟨a,b,har,hbr,?_⟩
  simp only [cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [ite_true,ite_false,mul3,notE,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    hap,hbig,hpre,hnzb,hs,hweight,hselector,cast_mul]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 256=(256:Fp) from rfl]
  all_goals grind only
/-- High post bytes are zero and the retired prior-byte zero tests are exact. -/
theorem current (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hg : gg<8)
    (ha : step I R present gb fwd inst k 2 gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 30).take 3,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,har,hpre,hnzb,hpost,hlow,hwt,he2⟩ :=
    ProcPriorCodecAllowanceData.cells I R present gb fwd inst k gg s out hg hk ha
  have hz : (1-Fp.ofNat a[lowf]!)*Fp.ofNat a[bpost]! =0 := by
    rw [hlow,hpost]
    by_cases hh : gg<3
    · simp only [hh,ite_true,show Fp.ofNat 1=(1:Fp) from rfl]; grind only
    · simp only [hh,ite_false,postByte,show Fp.ofNat 0=(0:Fp) from rfl]; grind only
  refine ⟨a,har,?_⟩
  simp only [cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl
  all_goals simp only [ite_true,mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hpre,hnzb,
    show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLocal
