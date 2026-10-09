import ZkFormal.NearV3.Rcpt.Candidates.DedupLayoutSize

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

def traffic (bs : List SrcpB) (repeated : Nat → Bool) : Traffic :=
  ⟨fun bb => if bb = B_SIZE then [[2, size bs]] else sourceMsgs bs repeated bb true,
   fun bb => if bb = B_SIZE then [] else sourceMsgs bs repeated bb false⟩

theorem cell_gz_eq {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool) (r : Nat) :
    cell bs repeated r SrcpV3.gz = if r + 1 = R bs then 1 else 0 := by
  by_cases he : r + 1 = R bs
  · have hr : r < R bs := by omega
    simp [cell_gz, he, hr]
  · simp [cell_gz, he]

/-- Even when terminal on a skipped header, SIZE is exactly the candidate's total charge. -/
theorem size_row_messages {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool)
    (r : Nat) (sd : Bool) :
    rowN (cell bs repeated r) B_SIZE sd =
      if sd = true ∧ r = R bs - 1 then [[2, size bs]] else [] := by
  have hp := R_pos hn
  by_cases hr : r = R bs - 1
  · subst r
    have he : R bs - 1 + 1 = R bs := by omega
    simp [rowN, B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, cell_gz_eq hn,
      he, last_size_cell hn]
  · have he : r + 1 ≠ R bs := by omega
    simp [rowN, B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, cell_gz_eq hn, he, hr]

theorem size_messages {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool)
    (H : Nat) (hH : R bs ≤ H) (sd : Bool) :
    (List.range H).flatMap (fun r => rowN (cell bs repeated r) B_SIZE sd) =
      if sd = true then [[2, size bs]] else [] := by
  have hr : (fun r => rowN (cell bs repeated r) B_SIZE sd) =
      (fun r => if sd = true ∧ r = R bs - 1 then [[2, size bs]] else []) := by
    funext r
    exact size_row_messages hn repeated r sd
  rw [hr]
  cases sd
  · simp
  · simp only [true_and, ite_true]
    apply flatMap_at
    have := R_pos hn
    omega

/-- Complete natural-message equality on every bus of the logical candidate trace. -/
theorem messages {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool)
    (H : Nat) (hH : R bs ≤ H)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32)
    (bb : Nat) (sd : Bool) :
    (List.range H).flatMap (fun r => rowN (cell bs repeated r) bb sd) =
      if sd then (traffic bs repeated).sends bb else (traffic bs repeated).recvs bb := by
  by_cases hb : bb = B_SIZE
  · subst bb
    rw [size_messages hn repeated H hH]
    cases sd <;> rfl
  · rw [all_messages bs repeated H hH bb sd hb h]
    cases sd <;> simp [traffic, hb]

/-- The actual logical candidate renderer realizes every bus contract, with silent
padding and exactly one SIZE record. No row-cap or old SrcpWf premise is needed. -/
theorem table_traffic {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hH : R bs ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated r x)) :
    TableTraffic DedupTable.interactions tr tt pub (traffic bs repeated) := by
  have hall : ∀ bb sd,
      (List.range (tr.height tt)).flatMap (fun r =>
        rowTraffic DedupTable.interactions tr tt r pub bb sd) =
      (if sd then (traffic bs repeated).sends bb else (traffic bs repeated).recvs bb).map Msg.toFp := by
    intro bb sd
    rw [← messages hn repeated (tr.height tt) hH h bb sd, List.map_flatMap]
    apply flatMap_congr'
    intro r hr
    exact row_traffic (cell bs repeated r) (hc r (List.mem_range.mp hr))
      (cell_bool_bound bs repeated r) bb sd
  apply Near.Render.traffic_of
  · intro bb; rw [hall bb true]; exact List.Perm.refl _
  · intro bb; rw [hall bb false]; exact List.Perm.refl _

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
