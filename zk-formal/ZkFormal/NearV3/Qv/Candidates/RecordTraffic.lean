import ZkFormal.NearV3.Qv.Candidates.RecordConcat
import ZkFormal.NearV3.Qv.Candidates.ValueTraffic

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

def Record.bytes (v : Record) : Bytes :=
  match v.payload with
  | .empty index => index++index
  | .buffer es => byteBufferedBytes es
  | .raw bytes => bytes

theorem Record.byteMessages (v : Record) (hv : v.Valid) :
    byteMessages v.rows = numberedBytes v.vid 0 v.bytes := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index => exact emptyRows_bytes vid tau users index hv
    | buffer es => exact bufferRows_bytes vid tau users es hv.1
    | raw bytes => exact rawRows_bytes vid tau users bytes

theorem Record.size_bytes (v : Record) (hv : v.Valid) :
    v.size=max 1 v.bytes.length := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      change index.length=8 at hv
      simp [Record.size,Record.bytes,hv]
    | buffer es =>
      have hs : (byteBufferedBytes es).length=4+24*es.length := by
        rw [← byteBufferedBytes_eq es hv.1,bufferedBytes_length,List.length_map]
      simp only [Record.size,Record.bytes,hs]
      omega
    | raw bytes => rfl

theorem records_byteMessages (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    byteMessages (recordsRows vs) = vs.flatMap (fun v => numberedBytes v.vid 0 v.bytes) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change byteMessages (v.rows++recordsRows vs)=_
    rw [byteMessages_append,v.byteMessages (hv v (by simp)),
      ih (by intro w hw; exact hv w (by simp [hw]))]
    rfl

/-- Exact record cost: one row per byte plus one marker for each empty value.
This is a compositional bound; native ownership and the global byte budget
must still be supplied by the witness-to-record constructor. -/
theorem recordsSize_exact (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    recordsSize vs = (vs.map (fun v => v.bytes.length)).sum +
      (vs.filter (fun v => v.bytes.isEmpty)).length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have h := v.size_bytes (hv v (by simp))
    have ht := ih (by intro w hw; exact hv w (by simp [hw]))
    simp only [recordsSize,List.map_cons,List.sum_cons] at ht ⊢
    rw [h,ht]
    by_cases hz : v.bytes=[]
    · simp [hz]
      omega
    · have hp : 0<v.bytes.length := List.length_pos_iff.mpr hz
      simp [List.isEmpty_eq_false_iff.mpr hz,List.filter_cons,Nat.max_eq_right hp]
      omega

theorem recordsSize_le (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    recordsSize vs ≤ (vs.map (fun v => v.bytes.length)).sum + vs.length := by
  rw [recordsSize_exact vs hv]
  exact Nat.add_le_add_left (List.length_filter_le _ _) _

end ZkFormal.NearV3.Qv.Candidates.ValueGen
