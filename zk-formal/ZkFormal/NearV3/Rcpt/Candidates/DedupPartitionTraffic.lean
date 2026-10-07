import ZkFormal.NearV3.Rcpt.Candidates.DedupCarry

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- The carried copy contributes no ordinary traffic in the first partition. -/
theorem left_normal_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (bb : Nat) (sd : Bool) (hb : bb ≠ sourceCarryBus) :
    rowTraffic (leftInteractions sourceCarryBus) tr tt r pub bb sd =
      if r + 1 = tr.height tt then [] else
        rowTraffic DedupTable.interactions tr tt r pub bb sd := by
  have hz (v : Fp) : (1 - 1) * v = 0 := by grind
  have ho (v : Fp) : (1 - 0) * v = v := by grind
  by_cases hr : r + 1 = tr.height tt
  all_goals simp [leftInteractions, DedupTable.interactions, rowTraffic,
    recv, send, Interaction.multNat, Interaction.multNat.go, Interaction.msgVal,
    eval_mul, eval_not, eval_isLast, hr, Ne.symm hb, hz, ho,
    show ¬(0 : Fp) = 1 by decide]
  all_goals rfl

/-- The second partition emits all ordinary traffic, including its overlap row. -/
theorem right_normal_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (bb : Nat) (sd : Bool) (hb : bb ≠ sourceCarryBus) :
    rowTraffic (rightInteractions sourceCarryBus) tr tt r pub bb sd =
      rowTraffic DedupTable.interactions tr tt r pub bb sd := by
  simp [rightInteractions, rowTraffic, recv, Ne.symm hb]

private theorem drop_last_messages {α : Type} (f : Nat → List α) (H : Nat) (hp : 0 < H) :
    (List.range H).flatMap (fun r => if r + 1 = H then [] else f r) =
      (List.range (H - 1)).flatMap f := by
  have he : List.range H = List.range (H - 1) ++ [H - 1] := by
    simpa only [Nat.succ_eq_add_one, show H - 1 + 1 = H by omega] using (@List.range_succ (H - 1))
  rw [he, List.flatMap_append]
  have hh : (List.range (H - 1)).flatMap (fun r => if r + 1 = H then [] else f r) =
      (List.range (H - 1)).flatMap f := by
    apply flatMap_congr'
    intro r hr
    have := List.mem_range.mp hr
    simp [show r + 1 ≠ H by omega]
  rw [hh]
  simp [show H - 1 + 1 = H by omega]

/-- Exact traffic-once theorem for the two physical source traces. The overlap row
is counted in the second trace only; SIZE and all other external buses are included. -/
theorem pair_messages {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (bs : List SrcpB) (repeated : Nat → Bool) (hn : bs ≠ [])
    (hh : tr.height right = tr.height left)
    (hR : DedupRender.R bs ≤ 2 * tr.height left - 1)
    (hshape : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32)
    (hleft : ∀ r, r < tr.height left → ∀ x,
      tr.cell left r x = Fp.ofNat (DedupRender.cell bs repeated r x))
    (hright : ∀ r, r < tr.height right → ∀ x,
      tr.cell right r x = Fp.ofNat (DedupRender.cell bs repeated (tr.height left - 1 + r) x))
    (bb : Nat) (sd : Bool) (hb : bb ≠ sourceCarryBus) :
    ((List.range (tr.height left)).flatMap (fun r =>
      rowTraffic (leftInteractions sourceCarryBus) tr left r pub bb sd)) ++
    ((List.range (tr.height right)).flatMap (fun r =>
      rowTraffic (rightInteractions sourceCarryBus) tr right r pub bb sd)) =
      (if sd then (DedupRender.traffic bs repeated).sends bb
       else (DedupRender.traffic bs repeated).recvs bb).map Msg.toFp := by
  have hp : 0 < tr.height left := by unfold Trace.height; exact Nat.two_pow_pos _
  have hl : (List.range (tr.height left)).flatMap (fun r =>
      rowTraffic (leftInteractions sourceCarryBus) tr left r pub bb sd) =
      ((List.range (tr.height left - 1)).flatMap (fun r =>
        DedupRender.rowN (DedupRender.cell bs repeated r) bb sd)).map Msg.toFp := by
    calc
      _ = (List.range (tr.height left)).flatMap (fun r => if r + 1 = tr.height left then []
            else (DedupRender.rowN (DedupRender.cell bs repeated r) bb sd).map Msg.toFp) := by
          apply flatMap_congr'
          intro r hr
          rw [left_normal_row tr left r pub bb sd hb]
          split
          · rfl
          · exact DedupRender.row_traffic _ (hleft r (List.mem_range.mp hr))
              (DedupRender.cell_bool_bound bs repeated r) bb sd
      _ = _ := by rw [drop_last_messages _ _ hp, List.map_flatMap]
  have hr : (List.range (tr.height right)).flatMap (fun r =>
      rowTraffic (rightInteractions sourceCarryBus) tr right r pub bb sd) =
      ((List.range (tr.height left)).flatMap (fun r =>
        DedupRender.rowN (DedupRender.cell bs repeated (tr.height left - 1 + r)) bb sd)).map Msg.toFp := by
    rw [List.map_flatMap, ← hh]
    apply flatMap_congr'
    intro r hr
    rw [right_normal_row tr right r pub bb sd hb]
    simpa only [hh] using DedupRender.row_traffic _ (hright r (List.mem_range.mp hr))
      (DedupRender.cell_bool_bound bs repeated _) bb sd
  rw [hl, hr, ← List.map_append]
  have hj : (List.range (tr.height left - 1)).flatMap (fun r =>
      DedupRender.rowN (DedupRender.cell bs repeated r) bb sd) ++
      (List.range (tr.height left)).flatMap (fun r =>
      DedupRender.rowN (DedupRender.cell bs repeated (tr.height left - 1 + r)) bb sd) =
      (List.range (2 * tr.height left - 1)).flatMap (fun r =>
        DedupRender.rowN (DedupRender.cell bs repeated r) bb sd) := by
    rw [show 2 * tr.height left - 1 = (tr.height left - 1) + tr.height left by omega,
      List.range_add, List.flatMap_append, List.flatMap_map]
  rw [hj, DedupRender.messages hn repeated _ hR hshape bb sd]

/-- Actual bus multiplicities of both partitions equal the single logical source contract. -/
theorem pair_counts {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (bs : List SrcpB) (repeated : Nat → Bool) (hn : bs ≠ [])
    (hh : tr.height right = tr.height left)
    (hR : DedupRender.R bs ≤ 2 * tr.height left - 1)
    (hshape : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32)
    (hleft : ∀ r, r < tr.height left → ∀ x,
      tr.cell left r x = Fp.ofNat (DedupRender.cell bs repeated r x))
    (hright : ∀ r, r < tr.height right → ∀ x,
      tr.cell right r x = Fp.ofNat (DedupRender.cell bs repeated (tr.height left - 1 + r) x))
    (bb : Nat) (sd : Bool) (hb : bb ≠ sourceCarryBus) (m : List Fp) :
    tableBusCount (leftInteractions sourceCarryBus) tr left pub bb sd m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub bb sd m =
      ((if sd then (DedupRender.traffic bs repeated).sends bb
       else (DedupRender.traffic bs repeated).recvs bb).map Msg.toFp).count m := by
  rw [tableBusCount_eq, tableBusCount_eq, ← List.count_append,
    pair_messages bs repeated hn hh hR hshape hleft hright bb sd hb]

/-- The honest two-trace cell placement copies every overlap column exactly. -/
theorem rendered_carry_equal {tr : Trace Fp} {left right : Nat}
    (bs : List SrcpB) (repeated : Nat → Bool)
    (hleft : ∀ r, r < tr.height left → ∀ x,
      tr.cell left r x = Fp.ofNat (DedupRender.cell bs repeated r x))
    (hright : ∀ r, r < tr.height right → ∀ x,
      tr.cell right r x = Fp.ofNat (DedupRender.cell bs repeated (tr.height left - 1 + r) x)) :
    carryRow tr left (tr.height left - 1) = carryRow tr right 0 := by
  have hl : 0 < tr.height left := by unfold Trace.height; exact Nat.two_pow_pos _
  have hr : 0 < tr.height right := by unfold Trace.height; exact Nat.two_pow_pos _
  apply List.map_congr_left
  intro x _
  rw [hleft _ (by omega), hright _ hr, Nat.add_zero]

/-- Equal carry tuples discharge both directions of the isolated pair's bus balance. -/
theorem carry_balance_of_equal (tr : Trace Fp) (left right : Nat) (pub : List Fp)
    (h : carryRow tr left (tr.height left - 1) = carryRow tr right 0) (m : List Fp) :
    tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m =
    tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m := by
  have hz (t : Nat) : (List.range (tr.height t)).flatMap (fun _ => ([] : List (List Fp))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simp [tableBusCount_eq, left_carry_messages, right_carry_messages,
    left_carry_recv, right_carry_send, hz, h]

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
