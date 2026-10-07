import ZkFormal.NearV3.Render.Ups.ForestPrefixProviders
import ZkFormal.NearV3.Render.Ups.ForestWalkHeads
import ZkFormal.NearV3.Assembly.ProperTarget

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

/-- Every actual physical prefix lookup has its existing global occurrence provider;
all selected-child offsets are derived from native execution and read determinacy. -/
theorem forest_prefix_safe {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (valueId : Slot→Nat) (resolvedId : PTrie→Nat) (baseI : UpsInst) (Qs : List UpsPartI)
    (t : Nat) (hrow : 1≤t ∧ t<run.splitCursor [0,15]) :
    let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root.tree run value)
      root.tree run value Qs
    ∃ n s, (forestStoreViews ts).nodes[n]?=some s ∧ (step I t).e∈edgesOf3 n s := by
  apply forest_physical_prefix_provider hroot hr hf _ valueId resolvedId baseI Qs t hrow
  intro p hp hd
  apply traceUpsert_seedProperTargets hr hf root.nid root.vid root.depth p
  exact List.mem_reverse.mpr (List.mem_filter.mpr ⟨hp,hd⟩)

/-- Native upsert constructs a locally valid instance and authenticates every active
walk row against concrete global head/node providers. No edge, bitmap, source-ID,
resolved-ID, selected-slot, or local AIR evaluation premise is supplied.
Global use counters, memory/child windows, and whole-table bounds remain separate. -/
theorem forest_native_walk {pairs : List (PTrie×PTrie)} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (pairs.map Prod.fst) tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (hw : root.tree.wf=true) (hv : 1≤value.length) (hsmall : value.length<2^24)
    (baseI : UpsInst) (base : Nat→UpsPartI) :
    let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
    let resolvedId := occurrenceResolvedId recordId
    ∃ (Qs : List UpsPartI) (a : OccurrenceAddress) (s : NodeS3) (h : HeadE),
      encodeNativeParts recordId root.tree run base=some Qs ∧
      (forestStoreViews (pairs.map Prod.fst)).nodes[a.nid]?=some s ∧
      (forestWalkHeads 0 0 pairs)[tau]?=some h ∧
      let I := nativeInstance recordId
        (nativeWalkBase recordId (fun _=>a.vid) resolvedId {baseI with tau:=tau} root.tree run value)
        root.tree run value Qs
      InstOk I ∧ (step I 0).e++[0]=startEdgeMsg h 0 ∧
      (∀ t,1≤t → t<I.ts → ∃ n provider,
        (forestStoreViews (pairs.map Prod.fst)).nodes[n]?=some provider ∧
          (step I t).e∈edgesOf3 n provider) ∧
      (((run.terminal=.BV ∨ run.terminal=.BI) ∧
        s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
        (step I I.ts).e∈edgesOf3 a.nid s) := by
  dsimp only
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let resolvedId := occurrenceResolvedId recordId
  obtain ⟨Qs,he,_⟩ := encodeNativeParts_total recordId hr base
  obtain ⟨a,s,hs,hterminal⟩ := forest_terminal_safe hroot hr hf {baseI with tau:=tau} Qs
  obtain ⟨h,hh,hstart⟩ := forest_start_provider hroot hr hf (fun _=>a.vid) resolvedId baseI Qs
  refine ⟨Qs,a,s,h,he,hs,hh,?_,hstart,?_,hterminal⟩
  · exact nativeInstance_constructed_ok recordId (fun _=>a.vid) resolvedId {baseI with tau:=tau}
      hr hw hv hsmall base he
  · intro t hpos hbefore
    exact forest_prefix_safe hroot hr hf (fun _=>a.vid) resolvedId {baseI with tau:=tau} Qs t ⟨hpos,hbefore⟩
end ZkFormal.NearV3.Render.UpsGen
