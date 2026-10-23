import NearCompression.RecursiveSourceProgram
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def recursiveSourceSize : RecursiveSourceExpr → Nat
  | .zero | .input _ => 1
  | .binary _ a b => recursiveSourceSize a+recursiveSourceSize b+1

/-- Verified postorder compiler. Preserves arithmetic association/order but
expands sharing; this is NOT yet the byte-identical Python shared emitter. -/
def recursiveSourceCompile (offset : Nat) : RecursiveSourceExpr → List (TerminalDAGNode K)
  | .zero => [.constant 0]
  | .input slot => [.input slot]
  | .binary op a b => recursiveSourceCompile offset a ++
      recursiveSourceCompile (offset+recursiveSourceSize a) b ++
      [.binary op (offset+recursiveSourceSize a-1)
        (offset+recursiveSourceSize a+recursiveSourceSize b-1)]

theorem recursive_source_size_positive (expr : RecursiveSourceExpr) : 0<recursiveSourceSize expr := by
  cases expr <;> simp only [recursiveSourceSize] <;> omega

theorem recursive_source_compile_length (offset : Nat) (expr : RecursiveSourceExpr) :
    (recursiveSourceCompile (K:=K) offset expr).length=recursiveSourceSize expr := by
  induction expr generalizing offset with
  | zero => rfl
  | input slot => rfl
  | binary op a b ia ib => simp only [recursiveSourceCompile,List.length_append,List.length_cons,List.length_nil,ia,ib,recursiveSourceSize]

omit [Field K] in
private theorem acyclic_append (offset : Nat) (a b : List (TerminalDAGNode K))
    (ha : TerminalDAGAcyclic offset a) (hb : TerminalDAGAcyclic (offset+a.length) b) :
    TerminalDAGAcyclic offset (a++b) := by
  induction a generalizing offset with
  | nil => simpa using hb
  | cons node rest ih =>
    exact ⟨ha.1,ih (offset+1) ha.2 (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hb)⟩

theorem recursive_source_compile_acyclic (offset : Nat) (expr : RecursiveSourceExpr) :
    TerminalDAGAcyclic offset (recursiveSourceCompile (K:=K) offset expr) := by
  induction expr generalizing offset with
  | zero => exact ⟨True.intro,True.intro⟩
  | input slot => exact ⟨True.intro,True.intro⟩
  | binary op a b ia ib =>
    apply acyclic_append
    · apply acyclic_append
      · exact ia offset
      · simpa only [recursive_source_compile_length] using ib (offset+recursiveSourceSize a)
    · simp only [List.length_append,recursive_source_compile_length,TerminalDAGAcyclic,TerminalNodeBefore]
      have pa := recursive_source_size_positive a
      have pb := recursive_source_size_positive b
      exact ⟨by omega,True.intro⟩

private theorem getD_append_left (a b : List (TerminalDAGNode K)) (i : Nat) (h : i<a.length) :
    (a++b).getD i (.constant 0)=a.getD i (.constant 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem getD_append_right (a b : List (TerminalDAGNode K)) (i : Nat) (h : a.length≤i) :
    (a++b).getD i (.constant 0)=b.getD (i-a.length) (.constant 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right h]

/-- Any embedding of the compiled node block obtains a route by construction. -/
theorem recursive_source_compile_route (offset : Nat) (expr : RecursiveSourceExpr)
    (nodes : Nat → TerminalDAGNode K)
    (embedded : ∀ i,i<recursiveSourceSize expr →
      nodes (offset+i)=(recursiveSourceCompile offset expr).getD i (.constant 0)) :
    RecursiveSourceRoute nodes expr (offset+recursiveSourceSize expr-1) := by
  induction expr generalizing offset with
  | zero =>
    apply RecursiveSourceRoute.zero
    simpa [recursiveSourceSize,recursiveSourceCompile] using embedded 0 (by simp [recursiveSourceSize])
  | input slot =>
    apply RecursiveSourceRoute.input
    simpa [recursiveSourceSize,recursiveSourceCompile] using embedded 0 (by simp [recursiveSourceSize])
  | binary op a b ia ib =>
    have pa := recursive_source_size_positive a
    have pb := recursive_source_size_positive b
    have ea : ∀ i,i<recursiveSourceSize a → nodes (offset+i)=
        (recursiveSourceCompile offset a).getD i (.constant 0) := by
      intro i hi
      have h := embedded i (by simp only [recursiveSourceSize];omega)
      rw [recursiveSourceCompile,getD_append_left _ _ _ (by simp only [List.length_append,recursive_source_compile_length];omega),
        getD_append_left _ _ _ (by simpa only [recursive_source_compile_length] using hi)] at h
      exact h
    have eb : ∀ i,i<recursiveSourceSize b → nodes (offset+recursiveSourceSize a+i)=
        (recursiveSourceCompile (offset+recursiveSourceSize a) b).getD i (.constant 0) := by
      intro i hi
      have h := embedded (recursiveSourceSize a+i) (by simp only [recursiveSourceSize];omega)
      rw [recursiveSourceCompile,getD_append_left _ _ _ (by simp only [List.length_append,recursive_source_compile_length];omega),
        getD_append_right _ _ _ (by simp only [recursive_source_compile_length];omega),recursive_source_compile_length] at h
      simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using h
    have root := embedded (recursiveSourceSize a+recursiveSourceSize b) (by simp only [recursiveSourceSize];omega)
    rw [recursiveSourceCompile,getD_append_right _ _ _ (by simp only [List.length_append,recursive_source_compile_length];omega)] at root
    simp only [List.length_append,recursive_source_compile_length,Nat.sub_self,List.getD_cons_zero] at root
    have rout := RecursiveSourceRoute.binary (ia offset ea) (ib (offset+recursiveSourceSize a) eb) root
    have ix : offset+recursiveSourceSize (.binary op a b)-1=offset+(recursiveSourceSize a+recursiveSourceSize b) := by simp only [recursiveSourceSize];omega
    rw [ix]
    simpa only [Nat.add_assoc] using rout

/-- No route, acyclicity, node-equation or output-value premise. -/
theorem recursive_source_compile_value (expr : RecursiveSourceExpr) (inputs : Nat → K) :
    terminalDAGRun inputs 0 (fun _=>0) (recursiveSourceCompile 0 expr)
      (recursiveSourceSize expr-1)=recursiveSourceExprEval inputs expr := by
  apply recursive_source_route_executed _ inputs (recursive_source_compile_acyclic 0 expr)
  have h := recursive_source_compile_route (K:=K) 0 expr
    (fun i=>(recursiveSourceCompile 0 expr).getD i (.constant 0)) (by intro i _;simp only [Nat.zero_add])
  simpa only [Nat.zero_add] using h

/-- Concrete source-query output has no caller-supplied structural certificate. -/
theorem recursive_source_output_compiled (query : RecursiveSourceQuery) (side : Bool)
    (offset : Nat) (values : Nat → K) :
    terminalDAGRun (fun i=>values (offset+i)) 0 (fun _=>0)
      (recursiveSourceCompile 0 (recursiveSourceOutputExpr query side))
      (recursiveSourceSize (recursiveSourceOutputExpr query side)-1)=
        recursiveSourceOutputValue (fun i=>values (offset+i)) query side := by
  rw [recursive_source_compile_value,recursive_source_output_eval]

/-- The two duplicate target slots and firstfold slots are tied through the
same native expected input vector, not a supplied equality of witnesses. -/
theorem recursive_source_duplicate_target (rows total firstRow target side : Nat)
    (values expected : Nat → K) (arithmetic : List K)
    (fits : 7*rows≤total) (first : firstRow<rows) (sideBound : side<2)
    (targetLower : 7*rows≤target) (targetUpper : target+side<total)
    (expectedAlias : expected (target+side)=expected (7*firstRow+side))
    (zero : ∀ x∈recursiveFixedResiduals rows total values expected arithmetic,x=0) :
    values (target+side)=values (7*firstRow+side) := by
  have fixed := ((recursive_fixed_residuals_zero_iff rows total values expected arithmetic).mp zero).2
  have source := (recursive_fixed_slot_coverage rows total (target+side)).mp
    (recursive_source_fixed_coverage rows total (target+side) (by omega) targetUpper)
  have fold := (recursive_fixed_slot_coverage rows total (7*firstRow+side)).mp
    (recursive_fold_fixed_coverage rows total firstRow side fits first (by omega))
  rw [fixed _ source.1 source.2,fixed _ fold.1 fold.2,expectedAlias]
end NearCompression
