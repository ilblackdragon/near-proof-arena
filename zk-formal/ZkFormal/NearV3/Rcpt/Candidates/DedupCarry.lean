import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficProof

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- Exact field tuple authenticated at the partition overlap. -/
def carryRow (tr : Trace Fp) (tt r : Nat) : List Fp :=
  (List.range 57).map (fun x => tr.cell tt r x)

theorem left_carry_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic (leftInteractions sourceCarryBus) tr tt r pub sourceCarryBus true =
      if r + 1 = tr.height tt then [carryRow tr tt r] else [] := by
  by_cases hr : r + 1 = tr.height tt
  all_goals simp [leftInteractions, DedupTable.interactions, rowTraffic, sourceCarryBus,
    recv, send, carryMessage, DedupTable.width, carryRow, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_map, Function.comp_def,
    eval_c, eval_isLast, hr, B_BYTES, B_DIGEST, B_RCL, B_SRC, B_SIZE]

theorem right_carry_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic (rightInteractions sourceCarryBus) tr tt r pub sourceCarryBus false =
      if r = 0 then [carryRow tr tt r] else [] := by
  by_cases hr : r = 0
  all_goals simp [rightInteractions, DedupTable.interactions, rowTraffic, sourceCarryBus,
    recv, send, carryMessage, DedupTable.width, carryRow, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_map, Function.comp_def,
    eval_c, eval_isFirst, hr, B_BYTES, B_DIGEST, B_RCL, B_SRC, B_SIZE]

theorem left_carry_recv (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic (leftInteractions sourceCarryBus) tr tt r pub sourceCarryBus false = [] := by
  simp [leftInteractions, DedupTable.interactions, rowTraffic, sourceCarryBus,
    recv, send, B_BYTES, B_DIGEST, B_RCL, B_SRC, B_SIZE]

theorem right_carry_send (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic (rightInteractions sourceCarryBus) tr tt r pub sourceCarryBus true = [] := by
  simp [rightInteractions, DedupTable.interactions, rowTraffic, sourceCarryBus,
    recv, send, B_BYTES, B_DIGEST, B_RCL, B_SRC, B_SIZE]

/-- There is exactly one carry send and no spurious source-bus carry messages. -/
theorem left_carry_messages (tr : Trace Fp) (tt : Nat) (pub : List Fp) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic (leftInteractions sourceCarryBus) tr tt r pub sourceCarryBus true) =
        [carryRow tr tt (tr.height tt - 1)] := by
  have hp : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have he (r : Nat) : (if r + 1 = tr.height tt then [carryRow tr tt r] else []) =
      if r = tr.height tt - 1 then [carryRow tr tt (tr.height tt - 1)] else [] := by
    by_cases hr : r = tr.height tt - 1
    · subst r; simp [show tr.height tt - 1 + 1 = tr.height tt by omega]
    · simp [hr, show r + 1 ≠ tr.height tt by omega]
  simp only [left_carry_row, he]
  exact Render.SrcpGen.flatMap_at _ _ _ (by omega)

/-- There is exactly one carry receive at the second physical trace's first row. -/
theorem right_carry_messages (tr : Trace Fp) (tt : Nat) (pub : List Fp) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic (rightInteractions sourceCarryBus) tr tt r pub sourceCarryBus false) =
        [carryRow tr tt 0] := by
  have hp : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have he (r : Nat) : (if r = 0 then [carryRow tr tt r] else []) =
      if r = 0 then [carryRow tr tt 0] else [] := by split <;> simp_all
  simp only [right_carry_row, he]
  exact Render.SrcpGen.flatMap_at _ _ _ hp

/-- Ideal bus balance for this isolated pair forces equality of the entire overlap
row. The global assembly must prove every other table/public segment is absent on64. -/
theorem carry_equal_of_balance (tr : Trace Fp) (left right : Nat) (pub : List Fp)
    (h : ∀ m,
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m =
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m) :
    carryRow tr left (tr.height left - 1) = carryRow tr right 0 := by
  have hc := h (carryRow tr left (tr.height left - 1))
  simp only [tableBusCount_eq, left_carry_messages, right_carry_messages,
    left_carry_recv, right_carry_send] at hc
  have hz (t : Nat) : (List.range (tr.height t)).flatMap (fun _ => ([] : List (List Fp))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  by_cases he : carryRow tr left (tr.height left - 1) = carryRow tr right 0
  · exact he
  · simp [he, Ne.symm he, hz] at hc

/-- Equality of carry tuples is equality of every source AIR column. -/
theorem carry_cells (tr : Trace Fp) (left right : Nat)
    (h : carryRow tr left (tr.height left - 1) = carryRow tr right 0) :
    ∀ x, x < 57 → tr.cell left (tr.height left - 1) x = tr.cell right 0 x := by
  intro x hx
  have he := congrArg (fun xs => xs.getD x 0) h
  simpa [carryRow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < (List.range 57).length by simpa using hx)] using he

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
