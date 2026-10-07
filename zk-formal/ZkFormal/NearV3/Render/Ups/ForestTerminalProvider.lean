import ZkFormal.NearV3.Assembly.SourceCoverage
import ZkFormal.NearV3.Render.Ups.SeedTerminalEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

theorem traceUpsert_terminal_revealed {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (hf : root.find key≠none) :
    isNode run.terminalSource=true := by
  have hv := traceUpsert_valueTerminal root key value run hr hf
  have hb := traceUpsert_branchTerminal root key value run hr
  have hk := traceUpsert_keyTerminal root key value run hr
  cases ht : run.terminal with
  | LP => obtain ⟨k,b,m,hs,_⟩ := hv.1 ht; rw [hs]; rfl
  | BR => obtain ⟨b,cs,m,hs,_⟩ := hv.2 ht; rw [hs]; rfl
  | BV => obtain ⟨cs,m,hs,_⟩ := hb.1 ht; rw [hs]; rfl
  | BI => obtain ⟨b,cs,m,i,rest,hs,_⟩ := hb.2 ht; rw [hs]; rfl
  | LSa | LSb | LSc | ESl0 | ESl1 | ESn0 | ESn1 =>
    simp only [KeyTerminal,ht] at hk
    obtain ⟨k,s,m,hs,_⟩ := hk
    rw [hs]; rfl

/-- The actual native terminal source is present at its coherent record ID in the
concrete global forest; this includes the allocated value position and source depth. -/
theorem forest_terminal_seed {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree key value=some run) (hf : root.tree.find key≠none) :
    ∃ a∈sourceAddresses root.nid root.vid root.depth root.tree key,
      a.tree=run.terminalSource ∧
      pathRecordId (sourceAddresses root.nid root.vid root.depth root.tree key) run.terminalSource=a.nid ∧
      (forestStoreViews ts).nodes[a.nid]?=
        some (seedNodeView tau a.depth a.nid a.vid run.terminalSource) := by
  obtain ⟨a,ha,he⟩ := (traceUpsert_source_addresses hr root.nid root.vid root.depth).1
  have hs := forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  have hv := sourceAddresses_view _ _ _ _ _ hs a ha
  have hn : isNode a.tree=true := he ▸ traceUpsert_terminal_revealed hr hf
  refine ⟨a,ha,he,he ▸ sourceAddresses_ids _ _ _ _ _ ha,?_⟩
  simpa only [forestStoreViews,Nat.zero_add,he] using hv.get hn



/-- Global placement and terminal traffic compose. The value ID is constructed from
its actual occurrence; only the off-path extension resolution agreement remains explicit. -/
theorem forest_terminal_provider {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) (Qs : List UpsPartI)
    (hres : SeedResolved
      (pathRecordId (sourceAddresses root.nid root.vid root.depth root.tree [0,15]) run.terminalSource)
      resolvedId run.terminalSource) :
    ∃ (a : OccurrenceAddress) (s : NodeS3), (forestStoreViews ts).nodes[a.nid]?=some s ∧
      let recordId := pathRecordId (sourceAddresses root.nid root.vid root.depth root.tree [0,15])
      let I := nativeInstance recordId (nativeWalkBase recordId (fun _=>a.vid) resolvedId baseI root.tree run value)
        root.tree run value Qs
      ((run.terminal=.BV ∨ run.terminal=.BI) ∧
        s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
        (step I I.ts).e∈edgesOf3 a.nid s := by
  obtain ⟨a,ha,he,hid,hget⟩ := forest_terminal_seed hroot hr hf
  let recordId := pathRecordId (sourceAddresses root.nid root.vid root.depth root.tree [0,15])
  have hv : SeedValueId a.vid (fun _=>a.vid) run.terminalSource := by
    cases run.terminalSource with
    | hash | ext => trivial
    | leaf k slot m => cases slot <;> trivial
    | branch value kids m => cases value with
      | none => trivial
      | some slot => cases slot <;> trivial
  have hp := seedInstance_terminalProvider recordId resolvedId (fun _=>a.vid) baseI hr hf Qs
    tau a.depth a.vid hres hv
  refine ⟨a,seedNodeView tau a.depth a.nid a.vid run.terminalSource,hget,?_⟩
  have hid' : recordId run.terminalSource=a.nid := hid
  simpa only [hid'] using hp
end ZkFormal.NearV3.Render.UpsGen
