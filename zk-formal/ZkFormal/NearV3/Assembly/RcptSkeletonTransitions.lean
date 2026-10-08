import ZkFormal.NearV3.Assembly.RcptSkeletonContinuation

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def refundTrace (refund : Bool) : Trace Fp :=
  ⟨fun _=>1,fun _ _ col=>if col=hr then (if refund then 1 else 0) else 0⟩
def enabledTransition (refund : Bool) (a b : Nat) : Bool :=
  succ.any fun (s,t,g)=>s==a && t==b && decide (g.eval (refundTrace refund) 0 0 []=1)

theorem fields_transitions (refund : Bool) :
    ((fields refund).zip ((fields refund).drop 1)).all
      (fun (a,b)=>enabledTransition refund a b)=true := by
  cases refund <;> decide

theorem successor_uses_refund {a b : Nat} {g : Expr} (hg : (a,b,g)∈succ) :
    g=k 1 ∨ g=c hr ∨ g=Dsl.not (c hr) := by
  simp only [succ,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hg
  grind only

theorem successor_shape (x : Input) {a b : Nat} {g : Expr} (hg : (a,b,g)∈succ)
    (pub : List Fp) : g.eval (shapeTrace x) 0 0 pub=g.eval (refundTrace x.refund) 0 0 [] := by
  rcases successor_uses_refund hg with rfl|rfl|rfl
  · rfl
  · rfl
  · rfl

/-- Every actual adjacent generated field pair takes an enabled successor edge
of the existing V3 table, with refund branches selected by the real input flag. -/
theorem fields_successor (x : Input) {a b : Nat}
    (hab : (a,b)∈(fields x.refund).zip ((fields x.refund).drop 1)) (pub : List Fp) :
    ∃g,(a,b,g)∈succ ∧ g.eval (shapeTrace x) 0 0 pub=1 := by
  have he := List.all_eq_true.mp (fields_transitions x.refund) (a,b) hab
  obtain ⟨⟨s,t,g⟩,hg,hen⟩ := List.any_eq_true.mp he
  have hf : s=a ∧ t=b ∧ g.eval (refundTrace x.refund) 0 0 []=1 := by
    simpa only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using hen
  rcases hf with ⟨rfl,rfl,hg1⟩
  exact ⟨g,hg,(successor_shape x hg pub).trans hg1⟩

theorem fields_all_transitions (refund : Bool) :
    ((fields refund).zip ((fields refund).drop 1)).all (fun (a,b)=>
      succ.all (fun (s,t,g)=>s != a || decide (g.eval (refundTrace refund) 0 0 []=0) || t==b))=true := by
  cases refund <;> decide

theorem fields_successor_unique (x : Input) {a b s t : Nat} {g : Expr}
    (hab : (a,b)∈(fields x.refund).zip ((fields x.refund).drop 1))
    (hg : (s,t,g)∈succ) (hs : s=a) (pub : List Fp) :
    g.eval (shapeTrace x) 0 0 pub=0 ∨ t=b := by
  have he := List.all_eq_true.mp (fields_all_transitions x.refund) (a,b) hab
  have h := List.all_eq_true.mp he (s,t,g) hg
  rw [successor_shape x hg pub]
  simpa only [hs,bne_self_eq_false,Bool.false_or,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] using h

theorem fields_first (refund : Bool) : (fields refund).head?=some sPL := by
  cases refund <;> rfl

theorem fields_last (refund : Bool) :
    (fields refund).getLast?=some (if refund then sXRZ else sXLH) := by
  cases refund <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
