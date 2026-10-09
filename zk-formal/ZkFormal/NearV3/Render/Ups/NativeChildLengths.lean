import ZkFormal.NearV3.Render.Ups.NativeMemoryAllocation
import ZkFormal.NearV3.Render.Ups.SourceCidBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Fill the MEMD/digest child length from the actual native output selected by
the executable part plan. Serialization includes the native u64 truncation. -/
def nativeLengthBase (run : TreeRun) (base : Nat→UpsPartI) (k : Nat) : UpsPartI :=
  {base k with clen :=
    match run.parts[k]? with
    | none => 0
    | some p => ((run.parts[planMemoryIndex p.kind.ix k-1]?).map
        (fun child=>(nodeEnc child.output).length)).getD 0}

/-- All constructed byte, memory and length source inputs compose without
changing one another's assigned fields. -/
def nativeSourceBase (recordId : PTrie→Nat) (run : TreeRun) (base : Nat→UpsPartI) : Nat→UpsPartI :=
  nativeCidBase recordId run (nativeMemoryBase run (nativeLengthBase run base))

theorem nativeSourceBase_clen (recordId : PTrie→Nat) (run : TreeRun) (base : Nat→UpsPartI) (k : Nat) :
    (nativeSourceBase recordId run base k).clen=(nativeLengthBase run base k).clen := by
  unfold nativeSourceBase nativeCidBase nativeMemoryBase
  split <;> rfl

theorem encodeTreePart_clen {base Q : UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) : Q.clen=base.clen := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  subst Q
  rfl

theorem planMemoryIndex_bound (kind k len : Nat) (hk : k<len) : planMemoryIndex kind k-1<len := by
  unfold planMemoryIndex
  split
  · omega
  · split <;> omega

/-- The final signed part names an actual native child output and carries its
exact serialized length; no caller-supplied child length is trusted. -/
theorem nativeInstance_nativeChildLength (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length) :
    let I := nativeInstance recordId baseI root run value Qs
    ∃ child,run.parts[(part I k).jm-1]?=some child ∧ (part I k).clen=(nodeEnc child.output).length := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr
    (nativeSourceBase recordId run base) he k hbound
  have hk : k<run.parts.length := List.getElem?_eq_some_iff.mp hp |>.1
  have hidx := planMemoryIndex_bound p.kind.ix k run.parts.length hk
  let child := run.parts[planMemoryIndex p.kind.ix k-1]'hidx
  have hchild : run.parts[planMemoryIndex p.kind.ix k-1]?=some child := List.getElem?_eq_getElem hidx
  have hjm : Q.jm=planMemoryIndex p.kind.ix k := (encodeTreePart_positions henc).2.2.2.2.2
  have hclen : Q.clen=(nodeEnc child.output).length := by
    rw [encodeTreePart_clen henc]
    change (nativeSourceBase recordId run base k).clen=_
    rw [nativeSourceBase_clen]
    simp only [nativeLengthBase,hp,hchild,Option.map_some,Option.getD_some]
  dsimp only
  rw [hpart]
  exact ⟨child,hjm ▸ hchild,hclen⟩
end ZkFormal.NearV3.Render.UpsGen
