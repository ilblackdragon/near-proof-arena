import ZkFormal.NearV3.Render.Ups.NativeChildLengthBinding
import ZkFormal.NearV3.Assembly.UpsertSplitSize

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly

private theorem range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun k=>xs.getD k d)=xs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2,Option.getD_some]

/-- Exact physical row cost: four walk rows, every fresh value byte, every
serialized output node byte. This states a cost, not an assumed table cap. -/
theorem recsI_length_exact (I : UpsInst) :
    (recsI I).length=4+L I+(I.parts.map (fun Q=>Q.q.length)).sum := by
  have hm : (List.range (nQ I)).map (fun k=>(part I k).q.length)=
      I.parts.map (fun Q=>Q.q.length) := by
    conv => rhs; rw [←range_getD I.parts default]
    simp only [List.map_map]
    rfl
  simp only [recsI,List.length_append,List.length_map,List.length_range,List.length_flatMap]
  rw [hm]

theorem encodeTreeParts_output_lengths (base : Nat→UpsPartI) :
    ∀ parts offset Qs,encodeTreeParts base offset parts=some Qs →
      Qs.map (fun Q=>Q.q.length)=parts.map (fun p=>(nodeEnc p.output).length)
  | [],_,Qs,h => by simp [encodeTreeParts] at h; subst Qs; rfl
  | p::ps,offset,Qs,h => by
    cases hQ : encodeTreePart (base offset) p with
    | none => simp [encodeTreeParts,hQ] at h
    | some Q =>
      cases hQs : encodeTreeParts base (offset+1) ps with
      | none => simp [encodeTreeParts,hQ,hQs] at h
      | some tail =>
        simp [encodeTreeParts,hQ,hQs] at h
        subst Qs
        have hl := congrArg List.length (encodeTreePart_native_bytes hQ).2
        simp only [List.length_map] at hl
        simp only [List.map_cons,hl,encodeTreeParts_output_lengths base ps (offset+1) tail hQs]

/-- Native encoding realizes exactly the byte costs charged by scheduler bounds. -/
theorem nativeInstance_rowCost (recordId : PTrie→Nat) (baseI : UpsInst) (root : PTrie)
    (run : TreeRun) (value : Bytes) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) :
    (recsI (nativeInstance recordId baseI root run value Qs)).length=
      4+value.length+outputByteCharge run := by
  rw [recsI_length_exact]
  have hq := encodeTreeParts_output_lengths (nativePartBase recordId root run base) run.parts 0 Qs he
  simpa only [nativeInstance,signedInstance,positionedInstance,traceInstance,L,List.length_map,
    List.map_map,withMemorySign,Function.comp_def,outputByteCharge,hq] using
    (show 4+value.length+(Qs.map (fun Q=>Q.q.length)).sum=4+value.length+outputByteCharge run from by rw [hq]; rfl)
end ZkFormal.NearV3.Render.UpsGen
