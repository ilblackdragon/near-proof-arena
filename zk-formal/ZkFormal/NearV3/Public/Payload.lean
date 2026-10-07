import ZkFormal.NearV3.Public.Packing

/-! Exact extraction of fixed-width records from packed payload bytes. -/
namespace ZkFormal.NearV3.Public

theorem payload_length (rows : Payload) (width : Nat)
    (hw : ∀ row ∈ rows, row.length = width) :
    (payloadBytes rows).length = rows.length * width := by
  induction rows with
  | nil => simp [payloadBytes]
  | cons row rows ih =>
    simp only [payloadBytes,List.flatten_cons,List.length_append,List.length_cons]
    have ht := ih (fun r hr => hw r (by simp [hr]))
    change rows.flatten.length = rows.length * width at ht
    rw [hw row (by simp),ht,Nat.add_mul]
    omega

theorem payload_getD (rows : Payload) (width : Nat)
    (hw : ∀ row ∈ rows, row.length = width) {j c : Nat}
    (hj : j < rows.length) (hc : c < width) :
    (payloadBytes rows).getD (j*width+c) 0 = (rows.getD j []).getD c 0 := by
  induction rows generalizing j with
  | nil => simp at hj
  | cons row rows ih =>
    have hr : row.length = width := hw row (by simp)
    cases j with
    | zero =>
      simp only [payloadBytes,List.flatten_cons,Nat.zero_mul,Nat.zero_add,List.getD_cons_zero,
        List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
      rfl
    | succ j =>
      change (row ++ payloadBytes rows).getD ((j+1)*width+c) 0 = (rows.getD j []).getD c 0
      rw [show (j+1)*width+c = row.length+(j*width+c) by simp only [Nat.add_mul,Nat.one_mul,hr]; omega,getD_right]
      exact ih (fun r h => hw r (by simp [h])) (by simpa using hj)

/-- A packed block begins after exactly the bytes of the preceding blocks. -/
theorem data_getD (blocks : List Payload) {i c : Nat} (hi : i < blocks.length)
    (hc : c < (payloadBytes (blocks.getD i [])).length) :
    (dataBytes blocks).getD ((dataBytes (blocks.take i)).length+c) 0 =
      (payloadBytes (blocks.getD i [])).getD c 0 := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons rs blocks ih =>
    cases i with
    | zero =>
      simp only [dataBytes,List.flatMap_cons,List.take_zero,List.flatMap_nil,List.length_nil,
        Nat.zero_add,List.getD_cons_zero,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa using hc)]
      rfl
    | succ i =>
      simp only [dataBytes,List.flatMap_cons,List.take_succ_cons,List.length_append,List.getD_cons_succ]
      rw [Nat.add_assoc,getD_right]
      exact ih (by simpa using hi) hc

end ZkFormal.NearV3.Public
