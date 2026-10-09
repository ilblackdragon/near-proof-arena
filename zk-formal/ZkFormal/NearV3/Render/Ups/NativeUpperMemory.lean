import ZkFormal.NearV3.Render.Ups.NativeMemoryAllocation
import ZkFormal.NearV3.Render.Ups.TreeMemoryDelta

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem withMemorySign_signedInstance (I : UpsInst) (Q : UpsPartI) :
    withMemorySign (signedInstance I) (withMemorySign I Q)=withMemorySign I Q := by
  change {withMemorySign I Q with neg:=if pfx (X1V (signedInstance I) (withMemorySign I Q)) 8<0 then 1 else 0}=
    withMemorySign I Q
  rw [signedInstance_X1V,withMemorySign_X1V]
  rfl

/-- Every upper memory scalar is exactly the actual native output memory. The proof
uses constructed old/new child links and the native clamped subtraction equation. -/
theorem nativeInstance_upperRV (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : v.length<2^24) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) (k : Nat) (hk : k+1<Qs.length)
    (hu : (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=11) :
    ∃ p, run.parts[k+1]?=some p ∧
      RV (nativeInstance recordId baseI root run v Qs)
        (part (nativeInstance recordId baseI root run v Qs) (k+1))=(p.output.memD:Int) := by
  let I := nativeInstance recordId baseI root run v Qs
  let B := nativeMemoryBase run base
  obtain ⟨a,A,ha,hA,henca,hparta⟩ := nativeInstance_part recordId baseI hr B he k (by omega)
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he (k+1) hk
  have hkind := encodeTreePart_kind henc
  have hupper : upperKind p.kind := by
    rw [hpart] at hu
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [hkind] at hu
    cases hc : p.kind <;> simp_all [UKind.ix,upperKind]
  have hs := traceUpsert_sources root [0,15] v run hw hr
  have hwa := hs.2 a (List.mem_of_getElem? ha)
  have hwp := hs.2 p (List.mem_of_getElem? hp)
  have hplan := nativeInstance_plan recordId baseI hr hw B he (k+1) hk
  have hj : (part I (k+1)).jm=k+1 :=
    hplan.jmD (by rcases hu with h|h|h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inr h)))
  have hchild : child I (part I (k+1))=part I k := by simp [child,hj]
  have hold : pfx (memByte (child I (part I (k+1)))) 8=(a.source.memD:Int) := by
    rw [hchild]
    change pfx (memByte (part (nativeInstance recordId baseI root run v Qs) k)) 8=(a.source.memD:Int)
    rw [hparta]
    change pfx (memByte A) 8=(a.source.memD:Int)
    exact encoded_child_memory henca hwa
  have hparent : pfx (memRb (part I (k+1))) 8=(p.source.memD:Int) := by
    rw [show part I (k+1)=withMemorySign (positionedInstance recordId baseI root run v Qs) Q from hpart]
    change pfx (memRb Q) 8=(p.source.memD:Int)
    exact encoded_source_memory_exact henc hwp
  have hmb : (part I (k+1)).mB=a.output.memD := by
    rw [show part I (k+1)=withMemorySign (positionedInstance recordId baseI root run v Qs) Q from hpart]
    change Q.mB=a.output.memD
    rw [encodeTreePart_mB henc]
    simp [positionedPart,withPlanPosition,withDescentPosition,B,nativeMemoryBase,hp,ha,
      show p.kind=.RDB ∨ p.kind=.RDE ∨ p.kind=.PT from hupper]
  obtain ⟨oldChild,newChild,holdChild,hnewChild,hdelta⟩ :=
    traceUpsert_deltas root [0,15] v run hr hw p (List.mem_of_getElem? hp) hupper
  have holdEq : oldChild=a.source := Option.some.inj (holdChild.symm.trans (traceUpsert_sourceChild hr ha hp hupper))
  have hnewEq : newChild=a.output := Option.some.inj (hnewChild.symm.trans (traceUpsert_outputChild hr ha hp hupper))
  rw [holdEq,hnewEq] at hdelta
  have hL : L I<2^24 := by simpa [I,L,nativeInstance,signedInstance,positionedInstance,traceInstance] using hv
  have scalar := up_memory_scalar I (part I (k+1)) hL hu p.source.memD a.source.memD hparent hold
  have hsign : withMemorySign I (part I (k+1))=part I (k+1) := by
    rw [show part I (k+1)=withMemorySign (positionedInstance recordId baseI root run v Qs) Q from hpart]
    exact withMemorySign_signedInstance _ Q
  rw [hsign,hmb,←hdelta] at scalar
  exact ⟨p,hp,scalar⟩
/-- All carry and serialized-memory constraints for actual upper updates follow
from the constructed native scalar. Header capacities remain explicit renderer bounds. -/
theorem nativeInstance_upperMemOk (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : v.length<2^24) (hd : fdepth root [0,15]≤400)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) (k : Nat) (hk : k+1<Qs.length)
    (hu : (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=11)
    (hq : (part (nativeInstance recordId baseI root run v Qs) (k+1)).qhk<2^22)
    (hpref : (part (nativeInstance recordId baseI root run v Qs) (k+1)).phk<2^22) :
    MemOk (nativeInstance recordId baseI root run v Qs)
      (part (nativeInstance recordId baseI root run v Qs) (k+1)) := by
  let I0 := positionedInstance recordId baseI root run v Qs
  let B := nativeMemoryBase run base
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he (k+1) hk
  obtain ⟨data⟩ := encodedNativePart_byteInput recordId baseI hr hw Qs (k+1) p hp (B (k+1)) henc
  obtain ⟨p',hp',hscalar⟩ := nativeInstance_upperRV recordId baseI hr hw hv base he k hk hu
  have heq : p'=p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  rw [hpart] at hscalar hq hpref ⊢
  have hraw : RV I0 (withMemorySign I0 Q)=(p.output.memD:Int) := by
    simpa only [nativeInstance,RV,TV,signedInstance_X1V,signedInstance_EinV] using hscalar
  have hkind := encodeTreePart_kind henc
  have hupper : upperKind p.kind := by
    rw [hpart] at hu
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [hkind] at hu
    cases hc : p.kind <;> simp_all [UKind.ix,upperKind]
  have hm : Q.mB<2^74 := by
    rw [encodeTreePart_mB henc]
    exact nativeMemoryBase_upper_bound hr hw hd hv base k p hp hupper
  have hL : L I0<2^24 := by simpa [I0,L,positionedInstance,traceInstance] using hv
  have hchild : SourceBytes (child I0 Q) :=
    trace_encoded_child_sourceBytes hr hw (nativePartBase recordId root run B) he I0 rfl Q
  have hmem := data.native_memOk henc (traceInstance_bounds hr hw baseI).1 hq hpref hL hchild hm hraw
  exact hmem.signedInstance
end ZkFormal.NearV3.Render.UpsGen
