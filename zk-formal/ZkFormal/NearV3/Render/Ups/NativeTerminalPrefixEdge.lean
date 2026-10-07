import ZkFormal.NearV3.Render.Ups.NativeTerminalProvider
import ZkFormal.NearV3.Render.Ups.TreeTerminalPrefix

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

theorem terminalPrefix_symbol {run : TreeRun} (hp : TerminalPrefix run) (i : Nat)
    (hi : i<run.matched) :
    run.terminalKey.getD i 0=(nativeNodeKey run.terminalSource).getD i 0 := by
  have he := congrArg (fun key : List Nat => key.getD i 0) hp.2
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_take,hi,ite_true] using he

theorem traceUpsert_terminalNodeShape {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hfind : root.find key≠none) :
    (∃ key slot mem,run.terminalSource=.leaf key slot mem) ∨
    (∃ key child mem,run.terminalSource=.ext key child mem ∧ run.matched<key.length) ∨
    run.matched=0 := by
  have hv := traceUpsert_valueTerminal root key v run hr hfind
  have hb := traceUpsert_branchTerminal root key v run hr
  have hk := traceUpsert_keyTerminal root key v run hr
  cases hc : run.terminal with
  | LP =>
    obtain ⟨key,bytes,mem,hs,_⟩ := hv.1 hc
    exact Or.inl ⟨key,.val bytes,mem,hs⟩
  | BR =>
    obtain ⟨bytes,kids,mem,_,hi⟩ := hv.2 hc
    exact Or.inr (Or.inr hi)
  | BV =>
    obtain ⟨kids,mem,_,hi⟩ := hb.1 hc
    exact Or.inr (Or.inr hi)
  | BI =>
    obtain ⟨value,kids,mem,slot,rest,_,_,_,hi⟩ := hb.2 hc
    exact Or.inr (Or.inr hi)
  | LSa | LSb | LSc =>
    simp only [KeyTerminal,hc] at hk
    obtain ⟨key,slot,mem,hs,_⟩ := hk
    exact Or.inl ⟨key,slot,mem,hs⟩
  | ESl0 | ESl1 | ESn0 | ESn1 =>
    exact Or.inr (Or.inl (by simpa only [KeyTerminal,hc] using hk))

/-- Earlier key steps inside the terminal record are supplied with the actual query
symbol. Their source and target remain in that record until the terminal position. -/
theorem nativePathNode_terminal_prefix_edge (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hfind : root.find key≠none)
    (i : Nat) (hi : i<run.matched) (s : NodeS3)
    (hnode : nativePathNode recordId resolvedId valueId run.terminalSource=some s.v) :
    [recordId run.terminalSource,i,run.terminalKey.getD i 0,
      recordId run.terminalSource,i+1,EK_KEY]∈edgesOf3 (recordId run.terminalSource) s := by
  have hp := traceUpsert_terminalPrefix root key v run hr
  rw [terminalPrefix_symbol hp i hi]
  rcases traceUpsert_terminalNodeShape hr hfind with ⟨key,slot,mem,hs⟩|⟨key,child,mem,hs,hm⟩|hm
  · have hv : s.v=.leaf key (nativeValueSlot valueId slot) ((u64 mem).map UInt8.toNat) := by
      simpa only [hs,nativePathNode,nativeKeyNode,Option.some.injEq] using hnode.symm
    have hb : run.matched≤key.length := by simpa only [hs,nativeNodeKey] using hp.1
    simpa only [hs,nativeNodeKey] using leaf_key_edge (recordId run.terminalSource) i s key _ _ hv (by omega)
  · have hv : s.v=.ext key (nativeWalkKid recordId resolvedId child) ((u64 mem).map UInt8.toNat) := by
      simpa only [hs,nativePathNode,nativeKeyNode,Option.some.injEq] using hnode.symm
    simpa only [hs,nativeNodeKey] using ext_inner_edge (recordId run.terminalSource) i s key _ _ hv (by omega)
  · omega
end ZkFormal.NearV3.Render.UpsGen
