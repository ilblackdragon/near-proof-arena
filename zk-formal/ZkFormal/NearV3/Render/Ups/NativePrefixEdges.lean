import ZkFormal.NearV3.Render.Ups.NativePathIds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

def ancestorWalkEdges (recordId : PTrie→Nat) (run : TreeRun) : List (List Nat) :=
  (properPath run).flatMap fun p => (List.range (partWalkKey p).length).map
    (partWalkEdge recordId (resolvedRecordId recordId) p)

def terminalWalkEdges (recordId : PTrie→Nat) (run : TreeRun) : List (List Nat) :=
  (List.range run.matched).map fun i =>
    [recordId run.terminalSource,i,run.terminalKey.getD i 0,recordId run.terminalSource,i+1,EK_KEY]

/-- All successful query-consuming steps before the terminal lookup, in native order. -/
def nativePrefixEdges (recordId : PTrie→Nat) (run : TreeRun) : List (List Nat) :=
  ancestorWalkEdges recordId run++terminalWalkEdges recordId run

theorem ancestorWalkEdges_length (recordId : PTrie→Nat) (run : TreeRun) :
    (ancestorWalkEdges recordId run).length=((properPath run).flatMap partWalkKey).length := by
  simp [ancestorWalkEdges,List.length_flatMap,Function.comp_def]

/-- Successful native traversal emits exactly the rows before its terminal cursor. -/
theorem nativePrefixEdges_length (recordId : PTrie→Nat) {root : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root key v=some run) :
    (nativePrefixEdges recordId run).length+1=run.splitCursor key := by
  have hq := congrArg List.length (traceUpsert_walkQuery root key v run hr)
  change ((properPath run).flatMap partWalkKey++run.terminalKey).length=key.length at hq
  simp only [List.length_append] at hq
  simp only [nativePrefixEdges,List.length_append,ancestorWalkEdges_length,terminalWalkEdges,
    List.length_map,List.length_range,TreeRun.splitCursor,TreeRun.consumed]
  omega

private theorem range_getD_take (xs : List Nat) (n : Nat) (hn : n≤xs.length) :
    (List.range n).map (fun i => xs.getD i 0)=xs.take n := by
  apply List.ext_getElem
  · simp [hn]
  · intro i h1 h2
    simp only [List.length_map,List.length_range] at h1
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show i<xs.length by omega),h1]

theorem ancestorWalkEdges_symbols (recordId : PTrie→Nat) (run : TreeRun) :
    (ancestorWalkEdges recordId run).map (fun edge => edge.getD 2 0)=
      (properPath run).flatMap partWalkKey := by
  simp only [ancestorWalkEdges,List.map_flatMap]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro p hp
  have hh := range_getD_take (partWalkKey p) (partWalkKey p).length (Nat.le_refl _)
  simpa [List.map_map,Function.comp_def,partWalkEdge,List.getD_eq_getElem?_getD] using hh

/-- The explicit prefix edge symbols are precisely the consumed native query prefix. -/
theorem nativePrefixEdges_symbols (recordId : PTrie→Nat) {root : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root key v=some run) :
    (nativePrefixEdges recordId run).map (fun edge => edge.getD 2 0)=
      key.take ((nativePrefixEdges recordId run).length) := by
  have ht := (traceUpsert_keys root key v run hr)
  obtain ⟨consumed,_,_,hmatched⟩ := ht
  have he : (terminalWalkEdges recordId run).map (fun edge => edge.getD 2 0)=
      run.terminalKey.take run.matched := by
    simpa [terminalWalkEdges,List.map_map,Function.comp_def,List.getD_eq_getElem?_getD] using
      range_getD_take run.terminalKey run.matched hmatched
  rw [nativePrefixEdges,List.map_append,ancestorWalkEdges_symbols,he]
  have hq := traceUpsert_walkQuery root key v run hr
  change (properPath run).flatMap partWalkKey++run.terminalKey=key at hq
  have hlen : (ancestorWalkEdges recordId run++terminalWalkEdges recordId run).length=
      ((properPath run).flatMap partWalkKey).length+run.matched := by
    simp only [List.length_append,ancestorWalkEdges_length,terminalWalkEdges,List.length_map,List.length_range]
  rw [hlen,←hq,List.take_append,List.take_of_length_le (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
end ZkFormal.NearV3.Render.UpsGen
