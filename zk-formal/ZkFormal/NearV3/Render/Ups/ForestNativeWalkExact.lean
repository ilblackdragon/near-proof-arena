import ZkFormal.NearV3.Render.Ups.ForestNativeWalk
import ZkFormal.NearV3.Render.Ups.ForestTerminalExact
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly
theorem forest_native_walk_exact {pairs : List (PTrie×PTrie)} {tau : Nat} {root : OccurrenceAddress}
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
      ((step I I.ts).e).getD 0 0=a.nid ∧
      ((run.terminal=.BV ∨ run.terminal=.BI) → s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∧
      (((run.terminal=.BV ∨ run.terminal=.BI) ∧
        s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
        (step I I.ts).e∈edgesOf3 a.nid s) := by
  dsimp only
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let resolvedId := occurrenceResolvedId recordId
  obtain ⟨Qs,he,_⟩ := encodeNativeParts_total recordId hr base
  obtain ⟨a,s,hs,hterminalId,hbitmap,hterminal⟩ := forest_terminal_exact hroot hr hf {baseI with tau:=tau} Qs
  obtain ⟨h,hh,hstart⟩ := forest_start_provider hroot hr hf (fun _=>a.vid) resolvedId baseI Qs
  refine ⟨Qs,a,s,h,he,hs,hh,?_,hstart,?_,hterminalId,hbitmap,hterminal⟩
  · exact nativeInstance_constructed_ok recordId (fun _=>a.vid) resolvedId {baseI with tau:=tau}
      hr hw hv hsmall base he
  · intro t hpos hbefore
    exact forest_prefix_safe hroot hr hf (fun _=>a.vid) resolvedId {baseI with tau:=tau} Qs t ⟨hpos,hbefore⟩
end ZkFormal.NearV3.Render.UpsGen
