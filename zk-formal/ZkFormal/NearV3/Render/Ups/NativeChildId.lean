import ZkFormal.NearV3.Render.Ups.TreeSourceChain
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- The allocator's child id is the record id of the actual native path child,
not merely an unconstrained number copied between adjacent rows. -/
theorem positionedPart_nativeChild (recordId : PTrie→Nat) (depth : Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (k : Nat) (p : TreePart)
    (hp : run.parts[k+1]?=some p) (hu : upperKind p.kind) (base : UpsPartI) :
    ∃ child, sourcePathChild p=some child ∧
      (positionedPart recordId depth run (k+1) p base).cN=recordId child := by
  have hn := List.getElem?_eq_some_iff.mp hp |>.1
  have hk : k<run.parts.length := by omega
  let a := run.parts[k]'hk
  have ha : run.parts[k]?=some a := List.getElem?_eq_getElem hk
  refine ⟨a.source,traceUpsert_sourceChild hr ha hp hu,?_⟩
  simp [positionedPart,ha]

/-- Byte serialization preserves the authenticated-child candidate selected from
native upsert. Connecting `recordId` to stored node views is a separate obligation. -/
theorem encoded_nativeChild (recordId : PTrie→Nat) (depth : Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (k : Nat) (p : TreePart)
    (hp : run.parts[k+1]?=some p) (hu : upperKind p.kind) (base : UpsPartI)
    {Q : UpsPartI} (he : encodeTreePart (positionedPart recordId depth run (k+1) p base) p=some Q) :
    ∃ child, sourcePathChild p=some child ∧ Q.cN=recordId child := by
  obtain ⟨child,hchild,hid⟩ := positionedPart_nativeChild recordId depth hr k p hp hu base
  refine ⟨child,hchild,?_⟩
  exact (encodeTreePart_positions he).2.2.2.2.1.trans hid

/-- The final signed instance retains the native parent-child record-id relation. -/
theorem nativeInstance_childId (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k+1<Qs.length)
    (hu : (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=11) :
    ∃ p child, run.parts[k+1]?=some p ∧ sourcePathChild p=some child ∧
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).cN=recordId child := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he (k+1) hk
  rw [hpart] at hu ⊢
  have hkind : Q.kind=p.kind.ix := encodeTreePart_kind henc
  have hupper : upperKind p.kind := by
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [hkind] at hu
    cases hc : p.kind <;> simp_all [UKind.ix,upperKind]
  obtain ⟨child,hchild,hid⟩ := encoded_nativeChild recordId _ hr k p hp hupper (base (k+1)) henc
  exact ⟨p,child,hp,hchild,hid⟩
end ZkFormal.NearV3.Render.UpsGen
