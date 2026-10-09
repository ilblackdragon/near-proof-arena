import ZkFormal.NearV3.Render.Ups.NativeValueEdge

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- Reveal precisely the value bytes present in the runtime trie; preserve references. -/
def nativeValueSlot (valueId : Slot→Nat) (slot : Slot) : NSlot3 :=
  match slot with
  | .ref len hash => treeSlot (.ref len hash)
  | .val bytes => .val ((u32 bytes.length).map UInt8.toNat) (valueId slot) bytes.length
      ((sha256 bytes).map UInt8.toNat) ((sha256 bytes).map UInt8.toNat) false

def nativeValueNode (valueId : Slot→Nat) : PTrie→Option NodeV3
  | .hash _ => none
  | .leaf key slot mem => some (.leaf key (nativeValueSlot valueId slot) ((u64 mem).map UInt8.toNat))
  | .ext key child mem => some (.ext key (treeKid child) ((u64 mem).map UInt8.toNat))
  | .branch value kids mem => some (.branch (value.map (nativeValueSlot valueId)) (treeKids kids)
      ((u64 mem).map UInt8.toNat))

theorem nativeValueSlot_bytes (valueId : Slot→Nat) (slot : Slot) (post : Bool) :
    (nativeValueSlot valueId slot).bytes post=(treeSlot slot).bytes post := by
  cases slot <;> simp [nativeValueSlot,treeSlot,NSlot3.bytes]

/-- Value-ID annotation changes no source serialization bytes. -/
theorem nativeValueNode_serialization (valueId : Slot→Nat) (source : PTrie) (post : Bool) :
    (nativeValueNode valueId source).map (NodeV3.ser post)=(treeNode source).map (NodeV3.ser post) := by
  cases source with
  | hash => rfl
  | leaf key slot mem => simp [nativeValueNode,treeNode,NodeV3.ser,nativeValueSlot_bytes]
  | ext => rfl
  | branch value kids mem => cases value <;> simp [nativeValueNode,treeNode,NodeV3.ser,nativeValueSlot_bytes]

/-- The executable annotation supplies exactly the ordinary source-view relation
used to authenticate native value-terminal edges. -/
theorem nativeValueNode_view (valueId : Slot→Nat) (source : PTrie) (view : NodeV3)
    (hv : nativeValueNode valueId source=some view) : NativeValueView valueId source view := by
  cases source with
  | hash => simp [nativeValueNode] at hv
  | ext => trivial
  | leaf key slot mem =>
    cases slot with
    | ref => trivial
    | val bytes =>
      simp only [nativeValueNode,Option.some.injEq] at hv
      subst view
      exact ⟨_,_,_,_,_,_,rfl⟩
  | branch value kids mem =>
    cases value with
    | none => trivial
    | some slot =>
      cases slot with
      | ref => trivial
      | val bytes =>
        simp only [nativeValueNode,Option.some.injEq] at hv
        subst view
        exact ⟨_,_,_,_,_,_,_,rfl⟩
/-- The concrete value annotation supplies a generated native terminal edge. -/
theorem nativeValueNode_terminal_edge (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hfind : root.find [0,15]≠none)
    (hc : run.terminal=.LP ∨ run.terminal=.BR) (Qs : List UpsPartI) (s : NodeS3)
    (hnode : nativeValueNode valueId run.terminalSource=some s.v) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s :=
  nativeInstance_value_edge recordId valueId resolvedId baseI hr hfind hc Qs s
    (nativeValueNode_view valueId run.terminalSource s.v hnode)
end ZkFormal.NearV3.Render.UpsGen
