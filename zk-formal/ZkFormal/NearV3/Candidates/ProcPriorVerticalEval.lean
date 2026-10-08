import ZkFormal.NearV3.Candidates.ProcPriorVertical
import ZkFormal.Near.Extract.Eval
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E

def windowEnv (en : Env Fp) : Env Fp:=
  {en with
    isFirst:=en.col first false
    isLast:=en.col last false
    isTransition:=en.add (en.ofNat 1) (en.neg (en.col last false))}

theorem expression_eval (en : Env Fp) (e : Expr) :
    (expression e).evalWith en=e.evalWith (windowEnv en) := by
  induction e <;> simp_all [expression,Expr.evalWith,windowEnv,c,k,sub]

def multWith (en : Env Fp) : List Expr→Nat→Nat
  | [],_=>0
  | e::es,k=>(if e.evalWith en=1 then 2^k else 0)+multWith en es (k+1)

theorem mult_one (en : Env Fp) (i : Nat) (es : List Expr) (k : Nat)
    (hm:en.col (stage i) false=1) (hr:en.mul=(·*·)) :
    multWith en (es.map (fun e=>.mul (c (stage i)) (expression e))) k=
      multWith (windowEnv en) es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [c] at ih
    simp only [List.map_cons,multWith,Expr.evalWith,c,hm,hr,expression_eval]
    have he:(1:Fp)*e.evalWith (windowEnv en)=e.evalWith (windowEnv en):=by grind
    rw [he,ih]

theorem mult_zero (en : Env Fp) (i : Nat) (es : List Expr) (k : Nat)
    (hm:en.col (stage i) false=0) (hr:en.mul=(·*·)) :
    multWith en (es.map (fun e=>.mul (c (stage i)) (expression e))) k=0 := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [c] at ih
    simp only [List.map_cons,multWith,Expr.evalWith,c,hm,hr,expression_eval]
    have he:(0:Fp)*e.evalWith (windowEnv en)=0:=by grind
    rw [he,ih]
    have hz:(0:Fp)≠1:=by decide +kernel
    simp [hz]

theorem active_constraints (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (h:TableLocal table tr tt pub) (hr:r<tr.height tt) (T : Air.Table) (i : Nat)
    (hi:(T,i)∈components.zipIdx) (hm:(c (stage i)).eval tr tt r pub=1)
    (e : Expr) (he:e∈T.constraints) : e.evalWith (windowEnv (rowEnv tr tt r pub))=0 := by
  have hmem:.mul (c (stage i)) (expression e)∈table.constraints :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨(T,i),hi,List.mem_map.mpr ⟨e,he,rfl⟩⟩)
  have hc:=h.constr r hr _ hmem
  simp only [eval_mul,hm] at hc
  have hh:(expression e).eval tr tt r pub=0:=by grind
  exact (expression_eval (rowEnv tr tt r pub) e).symm.trans hh

theorem active_bits (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (h:TableLocal table tr tt pub) (hr:r<tr.height tt) (T : Air.Table) (i : Nat)
    (hi:(T,i)∈components.zipIdx) (hm:(c (stage i)).eval tr tt r pub=1)
    (a : Interaction) (ha:a∈T.interactions) (e : Expr) (he:e∈a.mult) :
    e.evalWith (windowEnv (rowEnv tr tt r pub))=0 ∨ e.evalWith (windowEnv (rowEnv tr tt r pub))=1 := by
  have hmem:interaction i a∈table.interactions :=
    List.mem_flatMap.mpr ⟨(T,i),hi,List.mem_map.mpr ⟨a,ha,rfl⟩⟩
  have hh:=h.bits r hr (interaction i a) hmem (.mul (c (stage i)) (expression e))
    (List.mem_map.mpr ⟨e,he,rfl⟩)
  simp only [eval_mul,hm] at hh
  have hx:(expression e).eval tr tt r pub=e.evalWith (windowEnv (rowEnv tr tt r pub)):=expression_eval _ _
  rw [hx] at hh
  rcases hh with hh|hh <;> grind

end ZkFormal.NearV3.Candidates.ProcPriorVertical
