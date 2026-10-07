import ZkFormal.NearV3.Render.Ups.GMemLengthTrace

/-! All 29 memory constraints on the generated update trace. -/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

/-- Full memory constraint completeness; carry bounds and serialized memory
bytes remain explicit semantic inputs to be established by the actual upsert. -/
theorem cMem_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H UpsV3.cMem := by
  have hcur := cMemCurrent_ok ok hf hm hH
  have hcar := cMemCarry_ok ok hf hm hH
  have hlen := cMemLengths_ok ok hf hH
  intro q hq C D P hC hD e he
  change e ∈ ((UpsV3.cMem.take 4 ++ cMemCarry) ++
    (UpsV3.cMem.drop 6).take 5) ++ cMemLengths at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact hcur q hq C D P hC hD e (List.mem_append_left _ he)
      · exact hcar q hq C D P hC hD e he
    · exact hcur q hq C D P hC hD e (List.mem_append_right _ he)
  · exact hlen q hq C D P hC hD e he

end UpsGen
end ZkFormal.NearV3.Render
