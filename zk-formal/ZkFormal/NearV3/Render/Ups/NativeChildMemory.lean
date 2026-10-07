import ZkFormal.NearV3.Render.Ups.NativePlanFamily
import ZkFormal.NearV3.Render.Ups.NativeChildId
import ZkFormal.NearV3.Render.Ups.TreeMemoryUp

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- The old child memory read by an upper part is the native source child's exact
memory, recovered from the actual preceding serialized source node. -/
theorem nativeInstance_childMemory (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k+1<Qs.length)
    (hu : (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=11) :
    ∃ p oldChild, run.parts[k+1]?=some p ∧ sourcePathChild p=some oldChild ∧
      pfx (memRb (child (nativeInstance recordId baseI root run v Qs)
        (part (nativeInstance recordId baseI root run v Qs) (k+1)))) 8=(oldChild.memD:Int) := by
  let I := nativeInstance recordId baseI root run v Qs
  obtain ⟨a,A,ha,hA,henca,hparta⟩ := nativeInstance_part recordId baseI hr base he k (by omega)
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he (k+1) hk
  have hkind := encodeTreePart_kind henc
  have hupper : upperKind p.kind := by
    rw [hpart] at hu
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [hkind] at hu
    cases hc : p.kind <;> simp_all [UKind.ix,upperKind]
  refine ⟨p,a.source,hp,traceUpsert_sourceChild hr ha hp hupper,?_⟩
  have hplan := nativeInstance_plan recordId baseI hr hw base he (k+1) hk
  have hj : (part I (k+1)).jm=k+1 :=
    hplan.jmD (by rcases hu with h|h|h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inr h)))
  have hchild : child I (part I (k+1))=part I k := by simp [child,hj]
  change pfx (memRb (child I (part I (k+1)))) 8=(a.source.memD:Int)
  rw [hchild]
  change pfx (memRb (part (nativeInstance recordId baseI root run v Qs) k)) 8=(a.source.memD:Int)
  rw [hparta]
  change pfx (memRb A) 8=(a.source.memD:Int)
  exact encoded_source_memory_exact henca ((traceUpsert_sources root [0,15] v run hw hr).2 a (List.mem_of_getElem? ha))
end ZkFormal.NearV3.Render.UpsGen
