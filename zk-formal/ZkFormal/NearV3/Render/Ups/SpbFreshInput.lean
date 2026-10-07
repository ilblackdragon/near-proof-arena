import ZkFormal.NearV3.Render.Ups.SpbSlots
import ZkFormal.NearV3.Render.Ups.SpbFreshCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def spb_fresh_some_input (I : UpsInst) (base : UpsPartI) (hk : base.kind=10)
    (hi : I.ci=5 ∨ I.ci=7) (src : NodeV3) (sv : NSlot3) (child : NKid) (mem : List Nat)
    (hw : (NodeV3.branch (some sv) (splitKids I child .none) mem).wf)
    (hchild : child≠.none) (hlen : sv.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hbytes : ∀b∈src.ser true,b<256) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base src (.branch (some sv) (splitKids I child .none) mem)) := by
  let Q := encodePart base src (.branch (some sv) (splitKids I child .none) mem)
  let enc := encodePart_encoding base src (.branch (some sv) (splitKids I child .none) mem) hw
  have hnew : ¬splitHasNew I := by rcases hi with h|h <;> simp [splitHasNew,h]
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ⟨fun _ _ => ⟨sv,rfl,hlen⟩⟩
    splitBitmap := splitKids_bitmap I base src (some sv) child .none mem hw hx (fun _ => hchild)
      (fun h => False.elim (hnew h)) (fun _ h => False.elim (hnew h))
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := spb_fresh_copy I Q hk (by rcases hi with h|h; exact Or.inl h; exact Or.inr (Or.inr (Or.inl h))) }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; apply False.elim; rcases hi with hi|hi <;> simp [HeaderNeeded,XcpB,Q,encodePart,hk,hi] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ h; apply False.elim; rcases hi with hi|hi <;> simp [VcpB,Q,encodePart,hk,hi] at h

def spb_fresh_none_input (I : UpsInst) (base : UpsPartI) (hk : base.kind=10)
    (hi : I.ci=6 ∨ I.ci=9) (src : NodeV3) (old new : NKid) (mem : List Nat)
    (hw : (NodeV3.branch none (splitKids I old new) mem).wf)
    (ho : old≠.none) (hn : new≠.none) (hxy : I.x≠splitNewSlot I)
    (hbytes : ∀b∈src.ser true,b<256) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base src (.branch none (splitKids I old new) mem)) := by
  let Q := encodePart base src (.branch none (splitKids I old new) mem)
  let enc := encodePart_encoding base src (.branch none (splitKids I old new) mem) hw
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := splitKids_bitmap I base src none old new mem hw hx (fun _ => ho)
      (fun _ => hn) (fun _ _ => hxy)
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := spb_fresh_copy I Q hk (by rcases hi with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inr h))) }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩; intro h _; simp [Q,encodePart,nodeTypeCode] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; apply False.elim; rcases hi with hi|hi <;> simp [HeaderNeeded,XcpB,Q,encodePart,hk,hi] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ h; apply False.elim; rcases hi with hi|hi <;> simp [VcpB,Q,encodePart,hk,hi] at h

end ZkFormal.NearV3.Render.UpsGen
