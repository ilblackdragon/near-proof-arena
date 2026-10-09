import ZkFormal.NearV3.Candidates.ProcPriorRawBoolean
namespace ZkFormal.NearV3.Candidates.ProcPriorRawChecks
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec.Bandwidth ProcPriorRawGen ProcPriorRawSlots ProcPriorCells ProcPriorRawBoolean

def Valid (n : Nat) : Slot→Prop
  | .header g=>g<5
  | .record j g=>j<n ∧ g<24
  | .hash g=>g<32
  | .padding=>True

theorem slot_valid (n i : Nat) : Valid n (slot n i) := by
  by_cases h:i<length n
  · rcases coverage n i h with ⟨g,hg,_,he⟩|⟨j,g,hj,hg,_,he⟩|⟨g,hg,_,he⟩
    · rw [he]; exact hg
    · rw [he]; exact ⟨hj,hg⟩
    · rw [he]; exact hg
  · rw [ProcPriorRawSlots.padding n i (by omega)]; trivial

theorem cell_bits (st : State) (vid pos : Nat) (present : Bool) (s : Slot)
    (nxt : Nat→Fp) (first last trans : Fp) (pb lb bb sb rb : Nat)
    (i : Interaction) (hi:i∈ProcPriorRawFrame.interactions pb lb bb sb rb)
    (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (cells st vid present pos s) nxt first last trans)=0 ∨
    e.evalWith (env (cells st vid present pos s) nxt first last trans)=1 := by
  simp only [ProcPriorRawFrame.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals exact boolean_cells st vid pos present s _ (by decide +kernel)

theorem trace_bits (st : State) (vid : Nat) (present : Bool) (tt r : Nat) (pub : List Fp)
    (pb lb bb sb rb : Nat) (i : Interaction) (hi:i∈ProcPriorRawFrame.interactions pb lb bb sb rb)
    (e : Expr) (he:e∈i.mult) :
    e.eval (trace st vid present) tt r pub=0 ∨ e.eval (trace st vid present) tt r pub=1 := by
  simp only [ProcPriorRawFrame.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals exact boolean_cells st vid r present (slot st.links.length r) _ (by decide +kernel)

/-- The inverse witnesses decide ordinary canonical equality; no field
wraparound equality is substituted for a native integer comparison. -/
theorem zero_values (g : Bool) (a b : Nat) (ha:a<P) (hb:b<P) :
    let flag:=bit (g && decide (a=b))
    let x:=Fp.ofNat a-Fp.ofNat b
    bit g*(x*x⁻¹-(1-flag))=0 ∧ bit g*(x*flag)=0 ∧ (1-bit g)*flag=0 := by
  have hi:=inv_delta a b ha hb
  cases g <;> by_cases h:a=b <;> simp [bit,h] at * <;> grind

end ZkFormal.NearV3.Candidates.ProcPriorRawChecks
