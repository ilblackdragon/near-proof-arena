import ZkFormal.NearV3.Candidates.ProcPriorIdValue
namespace ZkFormal.NearV3.Candidates.ProcPriorIdCarry
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched ProcPriorIds ProcPriorIdValue

abbrev Value := Option Nat
def zero : Value := none
def update (v : Value) (e : Event) : Value :=
  match v with
  | some n=>some n
  | none=>if e.isPublic then some e.ordinal else none
structure State where
  key : Option Nat
  val : Value
  deriving DecidableEq, Repr

def atKey (s : State) (k : Nat) : Value := if s.key=some k then s.val else zero
def step (s : State) (e : Event) : State := ⟨some e.key,update (atKey s e.key) e⟩
def run (es : List Event) : State := es.foldl step ⟨none,zero⟩
def foldKey (es : List Event) (k : Nat) : Value := (es.filter fun e=>e.key==k).foldl update zero

theorem run_append (es : List Event) (e : Event) : run (es++[e])=step (run es) e := by
  simp [run,List.foldl_append]

theorem foldKey_append (es : List Event) (e : Event) (k : Nat) :
    foldKey (es++[e]) k=if e.key=k then update (foldKey es k) e else foldKey es k := by
  by_cases h:e.key=k <;> simp [foldKey,List.filter_append,List.foldl_append,h]

theorem foldKey_absent (es : List Event) (k : Nat) (h:∀ e∈es,e.key≠k) : foldKey es k=zero := by
  have hf:(es.filter fun e=>e.key==k)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simpa using h e he
  simp [foldKey,hf]

/-- Linear-time segmented carry equals the semantic fold for every key at or
above the processed prefix. The key-order premise is supplied by mergeSort. -/
theorem run_extreme (es : List Event) (hs:es.Pairwise (fun a b=>a.key≤b.key))
    (k : Nat) (hk:∀ e∈es,e.key≤k) : atKey (run es) k=foldKey es k := by
  induction es using snoc_induction with
  | h0 => rfl
  | hs es e ih =>
    obtain ⟨hpre,_,hcross⟩:=List.pairwise_append.mp hs
    have he:e.key≤k := hk e (by simp)
    have hle:∀ x∈es,x.key≤e.key := fun x hx=>hcross x hx e (by simp)
    rw [run_append,foldKey_append]
    by_cases heq:e.key=k
    · subst k
      rw [ite_eq_left rfl]
      have hx:atKey (step (run es) e) e.key=update (atKey (run es) e.key) e := by simp [atKey,step]
      rw [hx,ih hpre hle]
    · rw [ite_eq_right heq]
      have hz:foldKey es k=zero := foldKey_absent es k (fun x hx=>by have hh:=hle x hx; omega)
      rw [hz]
      simp [atKey,step,heq]

end ZkFormal.NearV3.Candidates.ProcPriorIdCarry
