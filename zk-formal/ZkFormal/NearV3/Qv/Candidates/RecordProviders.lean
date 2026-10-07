import ZkFormal.NearV3.Qv.Candidates.RecordBusMessages

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Near

def Record.mode (v : Record) : Nat :=
  match v.payload with | .empty _ => 0 | .buffer _ => 1 | .raw _ => 2

theorem Record.firstFields (v : Record) (hv : v.Valid) :
    let r := v.rows.getD 0 []
    r.getD ValueTable.vid 0=v.vid ∧ r.getD ValueTable.tau 0=v.tau ∧
    r.getD ValueTable.users 0=v.users ∧
    r.getD ValueTable.mBuffer 0+2*r.getD ValueTable.mRaw 0=v.mode := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      simp only [Record.rows,Record.mode]
      rw [emptyRows_get vid tau users index hv (by decide : 0<16)]
      simp [ValueTable.vid,ValueTable.tau,ValueTable.users,ValueTable.mBuffer,ValueTable.mRaw]
    | buffer es =>
      simp only [Record.rows,Record.mode]
      rw [bufferRows_header_get vid tau users es 0 (by decide)]
      simp [ValueTable.vid,ValueTable.tau,ValueTable.users,ValueTable.mBuffer,ValueTable.mRaw]
    | raw bytes =>
      simp only [Record.rows,Record.mode]
      rw [rawRows_get]
      have hz : 0<bytes.length ∨ bytes.length=0 ∧ 0=0 := by omega
      rw [if_pos hz]
      simp [ValueTable.vid,ValueTable.tau,ValueTable.users,ValueTable.mBuffer,ValueTable.mRaw]

theorem filter_first_only {α : Type} (xs : List α) (d : α) (p : α → Bool)
    (hn : 0<xs.length)
    (hp : ∀ i, i<xs.length → p (xs.getD i d)=decide (i=0)) :
    xs.filter p=[xs.getD 0 d] := by
  cases xs with
  | nil => simp at hn
  | cons x xs =>
    have h0 := hp 0 (by simp)
    simp only [List.getD_cons_zero,decide_true] at h0
    have ht : xs.filter p=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hy
      have h := hp (i+1) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using h
    simp [List.filter_cons,h0,ht]

theorem Record.first_filter (v : Record) (hv : v.Valid) :
    v.rows.filter (fun r => r.getD ValueTable.vf 0=1)=[v.rows.getD 0 []] := by
  apply filter_first_only _ [] _ (by rw [v.rows_length hv]; exact v.size_pos)
  intro i hi
  have hm := v.markers hv i (by rw [v.rows_length hv] at hi; exact hi)
  simp only [hm.2.1]
  by_cases h : i=0 <;> simp [h]

def qvcMessages (rows : List (List Nat)) (sd : Bool) : List Msg :=
  (rows.filter (fun r => r.getD ValueTable.vf 0=1)).map fun r =>
    [r.getD ValueTable.vid 0,r.getD ValueTable.tau 0,
      r.getD ValueTable.mBuffer 0+2*r.getD ValueTable.mRaw 0,
      if sd then 0 else r.getD ValueTable.users 0]

theorem qvcMessages_natTraffic (rows : List (List Nat)) (sd : Bool) :
    rows.flatMap (fun r => natRowTraffic ValueTable.interactions r ValueTable.B_QVC sd)=
      qvcMessages rows sd := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.flatMap_cons,ih,natRowTraffic_qvc]
    clear ih
    by_cases h : row.getD ValueTable.vf 0=1
    all_goals simp_all [qvcMessages]

theorem Record.provider_messages (v : Record) (hv : v.Valid) (sd : Bool) :
    v.rows.flatMap (fun r => natRowTraffic ValueTable.interactions r ValueTable.B_QVC sd)=
      [[v.vid,v.tau,v.mode,if sd then 0 else v.users]] := by
  rw [qvcMessages_natTraffic]
  unfold qvcMessages
  rw [v.first_filter hv]
  simp only [List.map_cons,List.map_nil]
  have hf := v.firstFields hv
  rw [hf.1,hf.2.1,hf.2.2.1,hf.2.2.2]

theorem records_provider_messages (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) (sd : Bool) :
    (recordsRows vs).flatMap (fun r => natRowTraffic ValueTable.interactions r ValueTable.B_QVC sd)=
      vs.map (fun v => [v.vid,v.tau,v.mode,if sd then 0 else v.users]) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (v.rows++recordsRows vs).flatMap _ = _
    rw [List.flatMap_append,v.provider_messages (hv v (by simp)),
      ih (by intro w hw; exact hv w (by simp [hw]))]
    rfl

theorem recordsTraffic_providers (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    (recordsTraffic vs).sends ValueTable.B_QVC = vs.map (fun v => [v.vid,v.tau,v.mode,0]) ∧
    (recordsTraffic vs).recvs ValueTable.B_QVC = vs.map (fun v => [v.vid,v.tau,v.mode,v.users]) := by
  constructor
  · exact records_provider_messages vs hv true
  · exact records_provider_messages vs hv false

end ZkFormal.NearV3.Qv.Candidates.ValueGen
