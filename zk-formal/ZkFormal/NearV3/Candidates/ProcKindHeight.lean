import ZkFormal.NearV3.Candidates.ProcNativeRows
namespace ZkFormal.NearV3.Candidates.ProcKindHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows

theorem cell_cast (R : Run) (t r c : Nat) :
    (trace R).cell t r c=Fp.ofNat ((atRow R r).cell c) := by
  change Fp.ofNat (natCell (Gen.Proc.rows R) (pad R) r c)=_
  rw [cell]

theorem act_cast (R : Run) (t r : Nat) :
    (trace R).cell t r Proc.act=if r<(procVs R).length then 1 else 0 := by
  rw [cell_cast]
  change Fp.ofNat ((atRow R r).act)=_
  rw [act]
  split <;> rfl

/-- The native initial instance starts at tau zero; later instances will be
assembled after its rows, rather than incorrectly reusing an isFirst row. -/
theorem kind_constraints (R : Run) (htau : R.tau=0)
    (hrows : (procVs R).length+1≤2^22) (t r : Nat) (pub : List Fp)
    (hr : r<2^22) : ∀ e ∈ Proc.cKind, e.eval (trace R) t r pub=0 := by
  intro e he
  simp only [Proc.cKind,List.mem_append] at he
  rcases he with he | he
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.1 he
    exact trace_bool R t r pub c hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · change (trace R).cell t r Proc.act + -((trace R).cell t r Proc.kK+
        ((trace R).cell t r Proc.kH+(trace R).cell t r Proc.kE))=0
      simp only [cell_cast]
      change Fp.ofNat ((atRow R r).act) + -(Fp.ofNat ((atRow R r).kK)+
        (Fp.ofNat ((atRow R r).kH)+Fp.ofNat ((atRow R r).kE)))=0
      rw [shape]
      change (((atRow R r).kK+(atRow R r).kH+(atRow R r).kE : Nat) : Fp)+
        -(((atRow R r).kK : Fp)+(((atRow R r).kH : Fp)+((atRow R r).kE : Fp)))=0
      grind
    · change (if r+1=2^22 then (1 : Fp) else 0)*(trace R).cell t r Proc.act=0
      rw [act_cast]
      by_cases hl : r+1=2^22
      · rw [if_pos hl,if_neg (by omega)]
        grind
      · rw [if_neg hl]; grind
    · change ((if r+1=2^22 then (0 : Fp) else 1)*(1 + -(trace R).cell t r Proc.act))*
        (trace R).cell t ((r+1)%2^22) Proc.act=0
      rw [act_cast,act_cast]
      by_cases hl : r+1=2^22
      · rw [if_pos hl]; grind
      · rw [if_neg hl,Nat.mod_eq_of_lt (by omega)]
        by_cases ha : r<(procVs R).length
        · rw [if_pos ha]; grind
        · rw [if_neg ha,if_neg (by omega)]; grind
    · change (if r=0 then (1 : Fp) else 0)*
        ((trace R).cell t r Proc.act*(1 + -(trace R).cell t r Proc.kK))=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,cell_cast,first]
        change 1*(1*(1 + -(1 : Fp)))=0
        grind
      · rw [if_neg h0]; grind
    · change (if r=0 then (1 : Fp) else 0)*(trace R).cell t r Proc.kc=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,first]
        change (1 : Fp)*0=0
        grind
      · rw [if_neg h0]; grind
    · change (if r=0 then (1 : Fp) else 0)*(trace R).cell t r Proc.tau=0
      by_cases h0 : r=0
      · subst r
        rw [if_pos rfl,cell_cast,first]
        change (1 : Fp)*Fp.ofNat R.tau=0
        rw [htau]
        rfl
      · rw [if_neg h0]; grind
end ZkFormal.NearV3.Candidates.ProcKindHeight
