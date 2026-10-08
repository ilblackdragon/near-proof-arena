import ZkFormal.NearV3.Render.Ups.NativeTerminalId
import ZkFormal.NearV3.Assembly.OccurrenceResolvedId

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

/-- Actual native terminal execution is authenticated by the concrete forest.
Source, value, and child-resolution IDs are all constructed from occurrences,
including a mismatching extension whose child ends in an unrevealed hash. -/
theorem forest_terminal_exact {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (baseI : UpsInst) (Qs : List UpsPartI) :
    ∃ (a : OccurrenceAddress) (s : NodeS3), (forestStoreViews ts).nodes[a.nid]?=some s ∧
      let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
      let resolvedId := occurrenceResolvedId recordId
      let I := nativeInstance recordId (nativeWalkBase recordId (fun _=>a.vid) resolvedId baseI root.tree run value)
        root.tree run value Qs
      ((step I I.ts).e).getD 0 0=a.nid ∧
      (((run.terminal=.BV ∨ run.terminal=.BI) ∧
        s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
        (step I I.ts).e∈edgesOf3 a.nid s) := by
  obtain ⟨a,ha,he,_,hget⟩ := forest_terminal_seed hroot hr hf
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  have hid : recordId run.terminalSource=a.nid := he ▸ extendedRecordId_source ha
  have hres : SeedResolved (recordId run.terminalSource) (occurrenceResolvedId recordId) run.terminalSource := by
    cases hs : run.terminalSource with
    | hash | leaf | branch => trivial
    | ext k c m =>
      change isNode c=true → occurrenceResolvedId recordId c=viewTarget (recordId (.ext k c m)+1) c
      intro _
      rw [←hs,hid]
      exact occurrenceResolvedId_ext_target ha (he.trans hs)
  have hv : SeedValueId a.vid (fun _=>a.vid) run.terminalSource := by
    cases run.terminalSource with
    | hash | ext => trivial
    | leaf k slot m => cases slot <;> trivial
    | branch value kids m => cases value with
      | none => trivial
      | some slot => cases slot <;> trivial
  have hp := seedInstance_terminalProvider recordId (occurrenceResolvedId recordId) (fun _=>a.vid)
    baseI hr hf Qs tau a.depth a.vid hres hv
  refine ⟨a,seedNodeView tau a.depth a.nid a.vid run.terminalSource,hget,?_⟩
  constructor
  · simpa only [hid] using nativeInstance_terminal_id recordId (fun _=>a.vid)
      (occurrenceResolvedId recordId) baseI hr Qs
  · simpa only [hid] using hp
end ZkFormal.NearV3.Render.UpsGen
