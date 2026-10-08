import ZkFormal.NearV3.Candidates.ProcPriorRawGen
namespace ZkFormal.NearV3.Candidates.ProcPriorRawBoolean
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec.Bandwidth ProcPriorRawGen ProcPriorRawSlots ProcPriorCells

theorem bit_range (b : Bool) : bit b=0 ∨ bit b=1 := by cases b <;> simp [bit]

theorem boolean_cells (st : State) (vid pos : Nat) (present : Bool) (s : Slot) (c : Nat)
    (hc:c∈[0,3,6,7,8,12,14,16,18,20,22]) :
    cells st vid present pos s c=0 ∨ cells st vid present pos s c=1 := by
  by_cases hs:s=.padding
  · simp [cells,hs]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [cells,hs,ite_false]
    all_goals first | exact Or.inr trivial | exact bit_range _

theorem boolean_constraints (st : State) (vid pos : Nat) (present : Bool) (s : Slot)
    (nxt : Nat→Fp) (first last trans : Fp) (c : Nat)
    (hc:c∈[ProcPriorRawFrame.act,ProcPriorRawFrame.present,ProcPriorRawFrame.hdr,
      ProcPriorRawFrame.rec,ProcPriorRawFrame.hash,ProcPriorRawFrame.phaseEnd,
      ProcPriorRawFrame.recordEnd,ProcPriorRawFrame.empty,ProcPriorRawFrame.first,
      ProcPriorRawFrame.byteGate,ProcPriorRawFrame.lengthGate]) :
    (ZkFormal.Chacha.Table.boolC c).evalWith (env (cells st vid present pos s) nxt first last trans)=0 := by
  have h:=boolean_cells st vid pos present s c hc
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  simp only [ZkFormal.Chacha.Table.boolC,sub,k,ZkFormal.Chacha.Table.E.c,Expr.evalWith,env,hone]
  rcases h with h|h <;> rw [h] <;> grind

/-- Canonical scalar equality is preserved by the field embedding. -/
theorem nat_delta (a b : Nat) (ha:a<P) (hb:b<P) :
    Fp.ofNat a-Fp.ofNat b=0 ↔ a=b := by
  constructor
  · intro h
    have he:Fp.ofNat a=Fp.ofNat b:=by grind
    have hn:=congrArg Fp.toNat he
    simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hn
  · intro h; subst b; grind

theorem inv_delta (a b : Nat) (ha:a<P) (hb:b<P) :
    (Fp.ofNat a-Fp.ofNat b)*(Fp.ofNat a-Fp.ofNat b)⁻¹=1-bit (decide (a=b)) := by
  by_cases h:a=b
  · subst b; simp [bit]; grind
  · have he:(Fp.ofNat a-Fp.ofNat b)≠0:=fun he=>h ((nat_delta a b ha hb).mp he)
    rw [Fp.mul_inv_cancel he]
    simp [bit,h]
    grind

end ZkFormal.NearV3.Candidates.ProcPriorRawBoolean
