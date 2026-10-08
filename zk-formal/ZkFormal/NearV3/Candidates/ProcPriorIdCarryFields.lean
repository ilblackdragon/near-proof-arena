import ZkFormal.NearV3.Candidates.ProcPriorIdCells
namespace ZkFormal.NearV3.Candidates.ProcPriorIdCarryFields
open ZkFormal.Algebra ProcPriorIdRows ProcPriorIdCarry ProcPriorCells ProcPriorIdCells

theorem carry_fields (a b : Row)
    (hb:b.before=if a.event.key=b.event.key then update a.before a.event else zero) :
    bit b.before.isSome=bit (gateAll a (some b))*(bit a.before.isSome+bit (take a)) ∧
    Fp.ofNat (b.before.getD 0)=bit (gateAll a (some b))*
      (Fp.ofNat (a.before.getD 0)+bit (take a)*Fp.ofNat a.event.ordinal) := by
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  rw [gateAll_key,hb]
  by_cases hk:a.event.key=b.event.key <;> cases hv:a.before <;> cases hp:a.event.isPublic
  all_goals simp [hk,hv,hp,update,zero,take,bit,hz]
  all_goals change _ ∧ _
  all_goals grind

theorem missing_index (a : Row) :
    (1-bit a.before.isSome)*Fp.ofNat (a.before.getD 0)=0 := by
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  cases a.before <;> simp [bit,hz] <;> grind

theorem take_field (a : Row) : bit (take a)=bit a.event.isPublic*(1-bit a.before.isSome) := by
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  cases hp:a.event.isPublic <;> cases hv:a.before <;> simp [take,hp,hv,bit] <;> grind

theorem no_query_public (a b : Row) (ho:ProcPriorIds.precedes a.event b.event=true) :
    bit (gateAll a (some b))*(1-bit a.event.isPublic)*bit b.event.isPublic=0 := by
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  rw [gateAll_key]
  by_cases hk:a.event.key=b.event.key
  · have hh:¬(a.event.isPublic=false ∧ b.event.isPublic=true) := by
      simp only [ProcPriorIds.precedes,decide_eq_true_eq,ProcPriorIds.rank] at ho
      intro hh
      simp [hh.1,hh.2,hk] at ho
    cases ha:a.event.isPublic <;> cases hb:b.event.isPublic
    all_goals simp [hk,ha,hb,bit] at *
    all_goals grind
  · simp [hk,bit]
    grind

end ZkFormal.NearV3.Candidates.ProcPriorIdCarryFields
