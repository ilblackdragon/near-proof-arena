import ZkFormal.NearV3.Assembly.ForestViews
import ZkFormal.NearV3.Assembly.ExactReplay

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def forestDepths (ts : List PTrie) : List Nat := ts.flatMap (depsT 0)
def forestCount (ts : List PTrie) : Nat := (ts.map tsize).sum

def forestSelect {α : Type} (f : PTrie → List α) : Nat → Nat → List PTrie → List α
  | _, _, [] => []
  | tau, target, t :: ts => (if tau = target then f t else []) ++ forestSelect f (tau+1) target ts

def nodeEntryAt (ns : List NodeRec3) (vs : List ValRec3) (tau : Nat) (n : Nat) : Option Bytes :=
  match ns[n]? with
  | some nr => if nr.tau = tau then some (nodeEnc (fullTree ns vs n)) else none
  | none => none

theorem forestRecs_length : ∀ tau nid vid ts,
    (forestRecs tau nid vid ts).length = forestCount ts
  | _, _, _, [] => rfl
  | tau, nid, vid, t :: ts => by
    simp [forestRecs, forestCount, recsT_length, forestRecs_length]

private theorem filterMap_range_none {α : Type} (f : Nat → Option α) :
    ∀ count start, (∀ i < count, f (start+i) = none) →
      (List.range' start count).filterMap f = []
  | 0, _, _ => rfl
  | count+1, start, h => by
    rw [List.range'_succ, List.filterMap_cons, show f start = none from by simpa using h 0 (by omega)]
    apply filterMap_range_none f count (start+1)
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm 1] using h (i+1) (by omega)

theorem Seg.nodeEntryRange {ns : List NodeRec3} {vs : List ValRec3} {ds : List Nat}
    {tau nid vid d : Nat} {t : PTrie} (hs : Seg ns vs ds tau nid vid d t) (target : Nat) :
    (List.range' nid (tsize t)).filterMap (nodeEntryAt ns vs target) =
      if tau = target then (occs t).map nodeEnc else [] := by
  by_cases he : tau = target
  · rw [if_pos he]
    apply filterMap_range'
    intro i hi
    obtain ⟨o, ho, v', d', hseg, _⟩ := hs.all i hi
    have hon := occs_isNode t o (List.mem_of_getElem? ho)
    have hg := (hseg.get hon).1
    have ht : fullTree ns vs (nid+i) = o :=
      hseg.tree hon ns.length (by have := hseg.len; omega)
    simp only [nodeEntryAt, hg, he, ite_true, ht]
    rw [(List.getElem?_eq_some_iff.mp ho).2]
  · rw [if_neg he]
    apply filterMap_range_none
    intro i hi
    obtain ⟨o, ho, v', d', hseg, _⟩ := hs.all i hi
    have hg := (hseg.get (occs_isNode t o (List.mem_of_getElem? ho))).1
    simp only [nodeEntryAt, hg, he, ite_false]

/-- The global record lists reconstruct every offset subtree using existing Seg proofs. -/
theorem forestNodeRange (ns : List NodeRec3) (vs : List ValRec3) (ds : List Nat) (target : Nat) :
    ∀ tau nid vid ts,
    ns.drop nid = forestRecs tau nid vid ts → vs.drop vid = forestVals tau ts →
    ds.drop nid = forestDepths ts →
    (List.range' nid (forestCount ts)).filterMap (nodeEntryAt ns vs target) =
      forestSelect (fun t => (occs t).map nodeEnc) tau target ts
  | _, _, _, [], _, _, _ => rfl
  | tau, nid, vid, t :: ts, hn, hv, hd => by
    have hs : Seg ns vs ds tau nid vid 0 t :=
      ⟨⟨_, hn⟩, ⟨_, hv⟩, ⟨_, hd⟩⟩
    have hn' := drop_of_append hn
    have hv' := drop_of_append hv
    have hd' := drop_of_append hd
    simp only [forestRecs, recsT_length] at hn'
    simp only [forestVals, valsT, List.length_map] at hv'
    simp only [forestDepths, List.flatMap_cons, depsT_length] at hd'
    simp only [forestCount, List.map_cons, List.sum_cons, forestSelect]
    rw [show List.range' nid (tsize t + (ts.map tsize).sum) =
      List.range' nid (tsize t) ++ List.range' (nid+tsize t) (ts.map tsize).sum from
      by simpa using (List.range'_append (s := nid) (n := tsize t) (m := (ts.map tsize).sum) (step := 1)).symm]
    rw [List.filterMap_append, Seg.nodeEntryRange hs target]
    exact congrArg ((if tau = target then (occs t).map nodeEnc else []) ++ ·)
      (forestNodeRange ns vs ds target (tau+1) (nid+tsize t) (vid+(valsOf t).length) ts hn' hv' hd')

theorem forest_nodeEntries (ts : List PTrie) (target : Nat) :
    nodeEntries (forestRecs 0 0 0 ts) (forestVals 0 ts) target =
      forestSelect (fun t => (occs t).map nodeEnc) 0 target ts := by
  unfold nodeEntries
  change (List.range (forestRecs 0 0 0 ts).length).filterMap
    (nodeEntryAt (forestRecs 0 0 0 ts) (forestVals 0 ts) target) = _
  rw [forestRecs_length, List.range_eq_range']
  exact forestNodeRange _ _ (forestDepths ts) target 0 0 0 ts (by simp) (by simp) (by simp)

theorem forest_valEntries : ∀ tau target ts,
    valEntries (forestVals tau ts) target = forestSelect valsOf tau target ts
  | _, _, [] => rfl
  | tau, target, t :: ts => by
    simp only [forestVals, valEntries, List.filter_append, List.map_append, forestSelect]
    have ih := forest_valEntries (tau+1) target ts
    simp only [valEntries] at ih
    rw [ih]
    by_cases he : tau = target
    · simp [valsT, he, List.filter_map, List.map_map, Function.comp_def]
    · simp [valsT, he, List.filter_map, List.map_map, Function.comp_def]

theorem forestSelect_below {α : Type} (f : PTrie → List α) : ∀ tau target ts,
    target < tau → forestSelect f tau target ts = []
  | _, _, [], _ => rfl
  | tau, target, t :: ts, h => by
    simp only [forestSelect, show tau ≠ target by omega, ite_false, List.nil_append]
    exact forestSelect_below f (tau+1) target ts (by omega)

theorem forestSelect_at {α : Type} (f : PTrie → List α) : ∀ tau i ts,
    forestSelect f tau (tau+i) ts = ((ts[i]?).map f).getD []
  | _, _, [] => by simp [forestSelect]
  | tau, 0, t :: ts => by
    simp only [Nat.add_zero, forestSelect, ite_true, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [forestSelect_below f (tau+1) tau ts (by omega), List.append_nil]
  | tau, i+1, t :: ts => by
    simp only [forestSelect, show tau ≠ tau+(i+1) by omega, ite_false, List.nil_append,
      List.getElem?_cons_succ]
    have he : tau+(i+1) = (tau+1)+i := by omega
    rw [he]
    exact forestSelect_at f (tau+1) i ts

/-- Every instance's global record store is exactly its original occurrence bytes. -/
theorem forest_storeOf {ts : List PTrie} {i : Nat} {t : PTrie} (ht : ts[i]? = some t) :
    storeOf (forestRecs 0 0 0 ts) (forestVals 0 ts) i = (occs t).map nodeEnc ++ valsOf t := by
  rw [storeOf, forest_nodeEntries, forest_valEntries]
  have hn := forestSelect_at (fun t => (occs t).map nodeEnc) 0 i ts
  have hv := forestSelect_at valsOf 0 i ts
  simp only [Nat.zero_add, ht, Option.map_some, Option.getD_some] at hn hv
  rw [hn, hv]

/-- Shared actual view allocation emits each normalized native store independently. -/
theorem forestStoreViews_store {ts : List PTrie} (hw : ∀ t ∈ ts, t.wf = true)
    (hc : (forestBytes ts).length ≤ ZkFormal.Algebra.P) {i : Nat} {t : PTrie}
    (ht : ts[i]? = some t) : (forestStoreViews ts).store i = normalStore t := by
  have he := forestStoreViews_records ts hw hc
  unfold ExtV3.store ExtV3.rawStore
  rw [he.1, he.2, forest_storeOf ht]
  rfl

/-- The shared allocator simultaneously preserves native replay and encoded store cost. -/
theorem forestStoreViews_native_store {ts : List PTrie} (hw : ∀ t ∈ ts, t.wf = true)
    (hc : (forestBytes ts).length ≤ ZkFormal.Algebra.P) {i : Nat}
    (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (hr : root.length = 32)
    (ht : ts[i]? = some (partialTrie ws root keys)) :
    storeCost ((forestStoreViews ts).store i) ≤ storeCost ws ∧
    partialTrie ((forestStoreViews ts).store i) root keys = partialTrie ws root keys := by
  rw [forestStoreViews_store hw hc ht]
  exact ⟨partialTrie_normalStore_cost ws root keys hr, partialTrie_normalStore ws root keys hr⟩

end ZkFormal.NearV3.Assembly
