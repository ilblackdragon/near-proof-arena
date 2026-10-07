import ZkFormal.NearV3.Assembly.TreeStore

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- Allocate all transition trees in one node/value address space. -/
def forestNodes : Nat → Nat → Nat → List PTrie → List NodeS3
  | _, _, _, [] => []
  | tau, nid, vid, t :: ts =>
    seedNodesT tau 0 nid vid t ++
      forestNodes (tau + 1) (nid + tsize t) (vid + (valsOf t).length) ts

def forestBytes (ts : List PTrie) : List Bytes := ts.flatMap valsOf

def forestRecs : Nat → Nat → Nat → List PTrie → List NodeRec3
  | _, _, _, [] => []
  | tau, nid, vid, t :: ts =>
    recsT tau nid vid t ++
      forestRecs (tau + 1) (nid + tsize t) (vid + (valsOf t).length) ts

def forestVals : Nat → List PTrie → List ValRec3
  | _, [] => []
  | tau, t :: ts => valsT tau t ++ forestVals (tau + 1) ts

/-- Executable store-only view allocation; heads and receipts are assembled separately. -/
def forestStoreViews (ts : List PTrie) : ExtV3 :=
  {nodes := forestNodes 0 0 0 ts, values := seedValuesFrom 0 (forestBytes ts),
   heads := [], receipts := [], dictionary := []}

theorem forestNodes_valueIds : ∀ tau nid vid ts,
    (forestNodes tau nid vid ts).filterMap seedValueId =
      List.range' vid (forestBytes ts).length
  | _, _, _, [] => by simp [forestNodes, forestBytes]
  | tau, nid, vid, t :: ts => by
    simp only [forestNodes, List.filterMap_append, seedNodesT_valueIds,
      forestNodes_valueIds, forestBytes, List.flatMap_cons, List.length_append]
    simpa using (List.range'_append (s := vid) (n := (valsOf t).length) (m := (forestBytes ts).length) (step := 1))

theorem seedNodesT_modular_records_at (tau nid vid : Nat) (t : PTrie)
    (hw : t.wf = true) (hc : vid + (valsOf t).length ≤ ZkFormal.Algebra.P) :
    Link3.recsOf (Link3.vpos 0) (seedNodesT tau 0 nid vid t) = recsT tau nid vid t := by
  rw [←seedNodesT_records tau 0 nid vid t hw]
  unfold Link3.recsOf
  apply List.map_congr_left
  intro s hs
  apply congrArg (NodeRec3.mk s.tau)
  apply node_toRec3_congr
  intro i len pre post written hv
  have hi : i ∈ (seedNodesT tau 0 nid vid t).filterMap seedValueId :=
    List.mem_filterMap.mpr ⟨s, hs, by simp [seedValueId, hv]⟩
  rw [seedNodesT_valueIds] at hi
  have hb : i < ZkFormal.Algebra.P := by simp only [List.mem_range'] at hi; omega
  simp [Link3.vpos, Nat.mod_eq_of_lt hb]

theorem forestNodes_modular_records : ∀ tau nid vid ts,
    (∀ t ∈ ts, t.wf = true) → vid + (forestBytes ts).length ≤ ZkFormal.Algebra.P →
    Link3.recsOf (Link3.vpos 0) (forestNodes tau nid vid ts) = forestRecs tau nid vid ts
  | _, _, _, [], _, _ => rfl
  | tau, nid, vid, t :: ts, hw, hc => by
    have hc' : vid + (valsOf t).length + (forestBytes ts).length ≤ ZkFormal.Algebra.P := by
      simpa [forestBytes, Nat.add_assoc] using hc
    simp only [forestNodes, forestRecs, Link3.recsOf, List.map_append]
    rw [show (seedNodesT tau 0 nid vid t).map (fun s => NodeRec3.mk s.tau (s.v.toRec3 (Link3.vpos 0))) =
      recsT tau nid vid t from seedNodesT_modular_records_at tau nid vid t (hw t (by simp)) (by omega)]
    rw [show (forestNodes (tau+1) (nid+tsize t) (vid+(valsOf t).length) ts).map
      (fun s => NodeRec3.mk s.tau (s.v.toRec3 (Link3.vpos 0))) = _ from
      forestNodes_modular_records _ _ _ ts (fun t ht => hw t (by simp [ht])) hc']

private theorem value_match_iff (s : NodeS3) (i : Nat) :
    (match s.v.value with | some (j, _) => j == i | none => false) = true ↔
      seedValueId s = some i := by
  cases h : s.v.value <;> simp [seedValueId, h]

theorem valTau_append_left (a b : List NodeS3) (i : Nat)
    (hi : i ∈ a.filterMap seedValueId) : Link3.valTau (a ++ b) i = Link3.valTau a i := by
  obtain ⟨s, hs, hv⟩ := List.mem_filterMap.mp hi
  have hm := (value_match_iff s i).mpr hv
  unfold Link3.valTau
  rw [List.find?_append]
  cases hf : a.find? (fun s => match s.v.value with | some (j, _) => j == i | none => false) with
  | none =>
    have hn := List.find?_eq_none.mp hf s hs
    rw [hm] at hn
    exact False.elim (hn rfl)
  | some found =>
    conv => lhs; pattern (List.find? _ a); tactic => exact hf
    conv => rhs; pattern (List.find? _ a); tactic => exact hf
    rfl

theorem valTau_append_right (a b : List NodeS3) (i : Nat)
    (hi : i ∉ a.filterMap seedValueId) : Link3.valTau (a ++ b) i = Link3.valTau b i := by
  have hn : a.find? (fun s => match s.v.value with | some (j, _) => j == i | none => false) = none := by
    apply List.find?_eq_none.mpr
    intro s hs
    intro hm
    exact hi (List.mem_filterMap.mpr ⟨s, hs, (value_match_iff s i).mp hm⟩)
  unfold Link3.valTau
  rw [List.find?_append]
  conv => lhs; pattern (List.find? _ a); tactic => exact hn
  rfl

theorem seedValuesFrom_append (vid : Nat) (a b : List Bytes) :
    seedValuesFrom vid (a ++ b) = seedValuesFrom vid a ++ seedValuesFrom (vid + a.length) b := by
  induction a generalizing vid with
  | nil => simp [seedValuesFrom]
  | cons x xs ih =>
    simp [seedValuesFrom, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem seedValuesFrom_vids (vid : Nat) (bs : List Bytes) :
    (seedValuesFrom vid bs).map ValE.vid = List.range' vid bs.length := by
  induction bs generalizing vid with
  | nil => rfl
  | cons b bs ih => simp [seedValuesFrom, seedValue, ih, List.range'_succ]

theorem valsOf3_congr_ids (a b : List NodeS3) (vid : Nat) (bs : List Bytes)
    (h : ∀ i ∈ List.range' vid bs.length, Link3.valTau a i = Link3.valTau b i) :
    Link3.valsOf3 a (seedValuesFrom vid bs) = Link3.valsOf3 b (seedValuesFrom vid bs) := by
  unfold Link3.valsOf3
  apply List.map_congr_left
  intro e he
  have hi : e.vid ∈ List.range' vid bs.length := by
    rw [←seedValuesFrom_vids]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  rw [h e.vid hi]

/-- Every value keeps the instance of its source node in the shared address space. -/
theorem forestViews_values : ∀ tau nid vid ts,
    Link3.valsOf3 (forestNodes tau nid vid ts) (seedValuesFrom vid (forestBytes ts)) =
      forestVals tau ts
  | _, _, _, [] => rfl
  | tau, nid, vid, t :: ts => by
    let a := seedNodesT tau 0 nid vid t
    let b := forestNodes (tau+1) (nid+tsize t) (vid+(valsOf t).length) ts
    have head : Link3.valsOf3 (a ++ b) (seedValuesFrom vid (valsOf t)) = valsT tau t := by
      apply seedValuesFrom_records
      intro i hi
      rw [valTau_append_left a b i (by simpa only [a, seedNodesT_valueIds] using hi)]
      exact seedNodesT_valTau tau 0 nid vid t i hi
    have tail : Link3.valsOf3 (a ++ b)
        (seedValuesFrom (vid+(valsOf t).length) (forestBytes ts)) =
        Link3.valsOf3 b (seedValuesFrom (vid+(valsOf t).length) (forestBytes ts)) := by
      apply valsOf3_congr_ids
      intro i hi
      apply valTau_append_right
      intro hbad
      simp only [a, seedNodesT_valueIds, List.mem_range'] at hbad
      simp only [List.mem_range'] at hi
      omega
    change Link3.valsOf3 (a ++ b) (seedValuesFrom vid (valsOf t ++ forestBytes ts)) =
      valsT tau t ++ forestVals (tau+1) ts
    rw [seedValuesFrom_append]
    simp only [Link3.valsOf3, List.map_append] at head tail ⊢
    rw [head, tail]
    exact congrArg (valsT tau t ++ ·) (forestViews_values (tau+1) (nid+tsize t)
      (vid+(valsOf t).length) ts)

theorem forestStoreViews_records (ts : List PTrie) (hw : ∀ t ∈ ts, t.wf = true)
    (hc : (forestBytes ts).length ≤ ZkFormal.Algebra.P) :
    Link3.recsOf (forestStoreViews ts).valuePosition (forestStoreViews ts).nodes =
      forestRecs 0 0 0 ts ∧
    Link3.valsOf3 (forestStoreViews ts).nodes (forestStoreViews ts).values = forestVals 0 ts := by
  constructor
  · have hv : (forestStoreViews ts).valuePosition = Link3.vpos 0 := by
      unfold ExtV3.valuePosition forestStoreViews
      change Link3.vpos (Link3.vid0 (seedValuesFrom 0 (forestBytes ts))) = _
      rw [seedValues_vid0]
    rw [hv]
    exact forestNodes_modular_records 0 0 0 ts hw (by simpa using hc)
  · exact forestViews_values 0 0 0 ts

end ZkFormal.NearV3.Assembly
