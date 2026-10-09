import ZkFormal.NearV3.Render.Ups.SeedWalkEdges
import ZkFormal.NearV3.Render.Ups.NativeTerminalProvider

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Ordinary occurrence-ID agreement for the child selected by an extension edge.
No agreement is demanded of unrelated sibling IDs or serialized AIR rows. -/
def SeedResolved (n : Nat) (resolvedId : PTrie→Nat) : PTrie→Prop
  | .ext _ child _ => isNode child=true → resolvedId child=viewTarget (n+1) child
  | _ => True

/-- Every constructed absent-key terminal edge is supplied by its occurrence seed,
including extension transitions to resolved revealed children. -/
theorem seedInstance_key_edge (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run)
    (hc : 4≤run.terminal.ix) (Qs : List UpsPartI) (tau depth vid : Nat) (s : NodeS3)
    (hres : SeedResolved (recordId run.terminalSource) resolvedId run.terminalSource)
    (hnode : s=seedNodeView tau depth (recordId run.terminalSource) vid run.terminalSource) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hb := trace_fixedKey_bounds hr
  have ht : 1≤I.ts ∧ I.ts≤3 := ⟨hb.2.2.1,hb.2.2.2⟩
  change (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0))
    target.1 target.2) I.ts).e∈edgesOf3 (recordId run.terminalSource) s
  rw [fourWalk_absent_terminal I _ _ _ _ _ _ ht hc]
  change [(sourceLevelIds recordId run).getD (descentCount run.parts) 0,run.matched,
    (if run.terminal.ix=4 then SYM_END else run.splitNibble),target.1,target.2,
    if run.terminal.ix=4 then EK_LEND else EK_KEY]∈edgesOf3 (recordId run.terminalSource) s
  rw [sourceLevelIds_terminal]
  have hk := traceUpsert_keyTerminal root [0,15] v run hr
  cases hcs : run.terminal with
  | LP | BR | BV | BI => simp [hcs,UCase.ix] at hc
  | LSa =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,slot,mem,hs,hi⟩ := hk
    have hv : s.v=.leaf key (viewSlot vid slot) ((u64 mem).map UInt8.toNat) := by
      simp only [hnode,seedNodeView,hs,viewNode]
    have he := leaf_end_edge (recordId run.terminalSource) s key _ _ hv
    simpa [target,nativeTerminalTarget,hcs,UCase.ix,hs,hi] using he
  | LSb | LSc =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,slot,mem,hs,hi⟩ := hk
    have hv : s.v=.leaf key (viewSlot vid slot) ((u64 mem).map UInt8.toNat) := by
      simp only [hnode,seedNodeView,hs,viewNode]
    have he := leaf_key_edge (recordId run.terminalSource) run.matched s key _ _ hv hi
    simpa [target,nativeTerminalTarget,hcs,UCase.ix,hs,TreeRun.splitNibble] using he
  | ESl0 | ESl1 | ESn0 | ESn1 =>
    simp only [KeyTerminal,hcs] at hk
    obtain ⟨key,child,mem,hs,hi⟩ := hk
    have hv : s.v=.ext key (viewKid (recordId run.terminalSource+1) child) ((u64 mem).map UInt8.toNat) := by
      simp only [hnode,seedNodeView,hs,viewNode]
    have he := ext_key_edge (recordId run.terminalSource) run.matched s key _ _ hv hi
    have htarget : target=extKeyTarget (recordId run.terminalSource) run.matched key
        (viewKid (recordId run.terminalSource+1) child) := by
      have hrr : isNode child=true → resolvedId child=viewTarget (recordId run.terminalSource+1) child := by
        simpa only [SeedResolved,hs] using hres
      cases child with
      | hash => simp [target,nativeTerminalTarget,hcs,hs,extKeyTarget,viewKid,isNode]
      | leaf | ext | branch => simp [target,nativeTerminalTarget,hcs,hs,extKeyTarget,viewKid,isNode,hrr rfl]
    rw [htarget]
    simpa [hcs,UCase.ix,hs,TreeRun.splitNibble] using he


/-- The generated absent-branch lookup uses the provider node's actual bitmap/value bit. -/
theorem seedInstance_branch_bitmap (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hc : run.terminal=.BV ∨ run.terminal=.BI)
    (Qs : List UpsPartI) (tau depth vid : Nat) (s : NodeS3)
    (hnode : s=seedNodeView tau depth (recordId run.terminalSource) vid run.terminalSource) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv) := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hb := trace_fixedKey_bounds hr
  have ht : 1≤I.ts ∧ I.ts≤3 := ⟨hb.2.2.1,hb.2.2.2⟩
  change s.v.bmap=some (
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) I.ts).bm,
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) I.ts).hv)
  have hbits := fourWalk_terminal_bitmap I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2 ht
  rw [hbits.1,hbits.2]
  have hbranch := traceUpsert_branchTerminal root [0,15] v run hr
  have hs : ∃ value kids mem,run.terminalSource=.branch value kids mem := by
    rcases hc with hc|hc
    · obtain ⟨kids,mem,hs,_⟩ := hbranch.1 hc
      exact ⟨none,kids,mem,hs⟩
    · obtain ⟨value,kids,mem,slot,rest,hs,_⟩ := hbranch.2 hc
      exact ⟨value,kids,mem,hs⟩
  obtain ⟨value,kids,mem,hs⟩ := hs
  have hv : s.v=.branch (value.map (viewSlot vid))
      (viewKids (recordId run.terminalSource+1) kids) ((u64 mem).map UInt8.toNat) := by
    simp only [hnode,seedNodeView,hs,viewNode]
  simp [hv,NodeV3.bmap,terminalBitmap,terminalHasVal,hs,viewKids_bitmap,treeKids_bitmap]



/-- The terminal occurrence's revealed value gets its allocated value record. -/
def SeedValueId (vid : Nat) (valueId : Slot→Nat) : PTrie→Prop
  | .leaf _ (.val bytes) _ => valueId (.val bytes)=vid
  | .branch (some (.val bytes)) _ _ => valueId (.val bytes)=vid
  | _ => True

theorem seed_valueView (tau depth n vid : Nat) (valueId : Slot→Nat) (source : PTrie)
    (hv : SeedValueId vid valueId source) :
    NativeValueView valueId source (seedNodeView tau depth n vid source).v := by
  cases source with
  | hash | ext => trivial
  | leaf key slot mem =>
    cases slot with
    | ref => trivial
    | val bytes =>
      change valueId (.val bytes)=vid at hv
      refine ⟨(u32 bytes.length).map UInt8.toNat,(sha256 bytes).map UInt8.toNat,
        (sha256 bytes).map UInt8.toNat,(u64 mem).map UInt8.toNat,bytes.length,false,?_⟩
      simp [seedNodeView,viewNode,viewSlot,hv]
  | branch value kids mem =>
    cases value with
    | none => trivial
    | some slot =>
      cases slot with
      | ref => trivial
      | val bytes =>
        change valueId (.val bytes)=vid at hv
        refine ⟨(u32 bytes.length).map UInt8.toNat,(sha256 bytes).map UInt8.toNat,
          (sha256 bytes).map UInt8.toNat,(u64 mem).map UInt8.toNat,bytes.length,false,viewKids (n+1) kids,?_⟩
        simp [seedNodeView,viewNode,viewSlot,hv]

/-- Every physical terminal lookup is supplied by the actual occurrence seed.
Only the value/resolved-child occurrence IDs need agreement; sibling maps are irrelevant. -/
theorem seedInstance_terminalProvider (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hfind : root.find [0,15]≠none)
    (Qs : List UpsPartI) (tau depth vid : Nat)
    (hres : SeedResolved (recordId run.terminalSource) resolvedId run.terminalSource)
    (hvid : SeedValueId vid valueId run.terminalSource) :
    let s := seedNodeView tau depth (recordId run.terminalSource) vid run.terminalSource
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    ((run.terminal=.BV ∨ run.terminal=.BI) ∧
      s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
      (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s := by
  dsimp only
  by_cases hbr : run.terminal=.BV ∨ run.terminal=.BI
  · exact Or.inl ⟨hbr,seedInstance_branch_bitmap recordId valueId resolvedId baseI hr hbr Qs
      tau depth vid _ rfl⟩
  right
  by_cases hval : run.terminal=.LP ∨ run.terminal=.BR
  · exact nativeInstance_value_edge recordId valueId resolvedId baseI hr hfind hval Qs _
      (seed_valueView tau depth _ vid valueId run.terminalSource hvid)
  · have hc : 4≤run.terminal.ix := by cases h : run.terminal <;> simp_all [UCase.ix]
    exact seedInstance_key_edge recordId valueId resolvedId baseI hr hc Qs tau depth vid _ hres rfl
end ZkFormal.NearV3.Render.UpsGen
