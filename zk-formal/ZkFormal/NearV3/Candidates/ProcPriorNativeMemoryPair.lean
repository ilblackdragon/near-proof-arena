import ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ProcPriorMemoryTable ProcPriorCells

theorem address_cast (a : Tagged) : Fp.ofNat (address a)=
    (4096:Fp)*Fp.ofNat a.tau+Fp.ofNat a.row.event.link := by
  rw [address,←ofNat_add',←ofNat_mul']
  rfl

theorem address_delta (a b : Nat) (ha:a<P) (hb:b<P) :
    (Fp.ofNat b-Fp.ofNat a=0) ↔ a=b := by
  constructor
  · intro h
    have he:Fp.ofNat b=Fp.ofNat a:=by grind
    have hn:=congrArg Fp.toNat he
    simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hn
    exact hn.symm
  · intro h;subst b;grind

theorem address_inverse (a b : Nat) (ha:a<P) (hb:b<P) :
    (Fp.ofNat b-Fp.ofNat a)*(Fp.ofNat b-Fp.ofNat a)⁻¹=1-bit (decide (a=b)) := by
  by_cases h:a=b
  · subst b;simp [bit];grind
  · have hd:(Fp.ofNat b-Fp.ofNat a)≠0:=fun he=>h ((address_delta a b ha hb).mp he)
    rw [Fp.mul_inv_cancel hd]
    simp [bit,h]
    grind

def pairEnv (a b : Tagged) (first : Fp) (ns : Bool) (ni : Fp) : Env Fp :=
  env (cell a.row a.tau (decide (address a=address b))
    (Fp.ofNat (address b)-Fp.ofNat (address a))⁻¹)
    (cell b.row b.tau ns ni) first 0 1

/-- Packed-address geometry permits honest adjacent rows from different
instances without assuming their timestamps or local link indices agree. -/
theorem pair_constraints (a b : Tagged) (first : Fp) (ns : Bool) (ni : Fp)
    (ha:address a<P) (hb:address b<P)
    (hf:first=0 ∨ a.row.before=ProcPriorCarry.zero)
    (hq:a.row.event.query=true → a.row.before=ProcPriorValues.value a.row.event)
    (hn:b.row.before=if address a=address b then ProcPriorValues.value a.row.event else ProcPriorCarry.zero)
    (he:a.row.event.query=true → address a≠address b)
    (e : Expr) (hm:e∈constraints) : e.evalWith (pairEnv a b first ns ni)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hzero:Fp.ofNat 0=(0:Fp):=rfl
  have h4096:Fp.ofNat 4096=(4096:Fp):=rfl
  have hd:=address_inverse (address a) (address b) ha hb
  have hdz:=address_delta (address a) (address b) ha hb
  have hea:=address_cast a
  have heb:=address_cast b
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
    exact active_boolean a.row a.tau _ _ _ first 0 1 c hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,pairEnv,env,cell,adjacent,delta,addr,nextAddr,
      notE,sub,k,c,n,act,ProcPriorMemoryTable.tau,link,query,lo,hi,beforeLo,beforeHi,same,inverse,
      Bool.false_eq_true,ite_false,ite_true,hone,h4096,←hea,←heb]
    all_goals try grind
    all_goals by_cases hk:address a=address b
    all_goals cases hquery:a.row.event.query
    all_goals simp [bit,hk,hquery,ProcPriorValues.value,ProcPriorCarry.zero] at *
    all_goals try grind
    all_goals rcases hf with hf|hf <;> simp_all <;> grind
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
