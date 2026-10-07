import ZkFormal.NearV3.Render.Ups.FreshCopy
import ZkFormal.NearV3.Render.Ups.GBytes

/-! Byte inputs for actual fresh leaf and wrapping-extension constructors. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def nlf_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=8)
    (src : NodeV3) (sv : NSlot3) (mem : List Nat)
    (hd : (NodeV3.leaf ([0,15].drop I.ts) sv mem).wf)
    (hlen : sv.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hbytes : ∀ b ∈ src.ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base src (.leaf ([0,15].drop I.ts) sv mem)) := by
  let Q := encodePart base src (.leaf ([0,15].drop I.ts) sv mem)
  let enc := encodePart_encoding base src (.leaf ([0,15].drop I.ts) sv mem) hd
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := nlf_copy I base hk src _ sv mem }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk,enc,encodePart_encoding,NodeGen3.keyOf,NodeGen3.isLeaf]
  · refine ⟨?_⟩
    intro _ _
    exact ⟨sv,rfl,hlen⟩
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [VcpB,Q,encodePart,hk] at h

def wex_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=9)
    (src : NodeV3) (kid : NKid) (mem : List Nat)
    (hd : (NodeV3.ext (([0,15].drop (I.ts-1-I.ti)).take I.ti) kid mem).wf)
    (hbytes : ∀ b ∈ src.ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16)
    (wrap : I.ts=2 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=2) :
    ByteInput I (encodePart base src (.ext (([0,15].drop (I.ts-1-I.ti)).take I.ti) kid mem)) := by
  let key := ([0,15].drop (I.ts-1-I.ti)).take I.ti
  let Q := encodePart base src (.ext key kid mem)
  let enc := encodePart_encoding base src (.ext key kid mem) hd
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := wex_copy I base hk src key kid mem }
  · refine ⟨hts,?_,?_,?_⟩
    · simp [Q,encodePart,hk]
    · intro _; exact ⟨wrap,rfl,rfl⟩
    · simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro h
    simp [Q,encodePart,nodeTypeCode] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [VcpB,Q,encodePart,hk] at h

end ZkFormal.NearV3.Render.UpsGen
