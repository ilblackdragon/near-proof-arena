import ZkFormal.NearV3.Rcpt.Candidates.DedupJoinedBits
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Ordinary source messages depend only on their row's cells. -/
theorem base_traffic_current {tr tr' : Trace Fp} {t r t' r' : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell t r x=tr'.cell t' r' x) (bus : Nat) (sd : Bool) :
    rowTraffic DedupTable.interactions tr t r pub bus sd =
    rowTraffic DedupTable.interactions tr' t' r' pub bus sd := by
  simp [DedupTable.interactions, rowTraffic, Dsl.send, Dsl.recv,
    Interaction.multNat, Interaction.multNat.go, Interaction.msgVal,
    SrcpV3.regs, Function.comp_def, eval_c, hc]
  rfl

private theorem drop_last {α : Type} (f : Nat → List α) (H : Nat) (hp : 0<H) :
    (List.range H).flatMap (fun r => if r+1=H then [] else f r) =
    (List.range (H-1)).flatMap f := by
  have he : List.range H=List.range (H-1)++[H-1] := by
    simpa only [Nat.succ_eq_add_one, show H-1+1=H by omega] using (@List.range_succ (H-1))
  rw [he, List.flatMap_append]
  have hh : (List.range (H-1)).flatMap (fun r => if r+1=H then [] else f r)=
      (List.range (H-1)).flatMap f := by
    apply flatMap_congr'
    intro r hr
    have := List.mem_range.mp hr
    simp [show r+1≠H by omega]
  rw [hh]
  simp [show H-1+1=H by omega]

/-- Joining arbitrary accepting source partitions preserves every ordinary bus
message exactly, including SIZE. The cloned endpoint contributes no traffic. -/
theorem joined_messages {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hright : TableLocal (rightTable sourceCarryBus) tr right pub)
    (hheight : tr.height right=tr.height left)
    (bus : Nat) (sd : Bool) (hb : bus≠sourceCarryBus) :
    (List.range ((joinedTrace tr left right).height 0)).flatMap
      (fun r => rowTraffic DedupTable.interactions (joinedTrace tr left right) 0 r pub bus sd) =
    (List.range (tr.height left)).flatMap
      (fun r => rowTraffic (leftInteractions sourceCarryBus) tr left r pub bus sd) ++
    (List.range (tr.height right)).flatMap
      (fun r => rowTraffic (rightInteractions sourceCarryBus) tr right r pub bus sd) := by
  let H := tr.height left
  have hp : 0<H := Nat.two_pow_pos _
  have hclone : rowTraffic DedupTable.interactions (joinedTrace tr left right) 0 (2*H-1) pub bus sd=[] := by
    rw [base_traffic_current (tr' := tr) (t' := right) (r' := H-1)
      (fun x => congrFun (joined_clone (by omega) (tr.cell left) (tr.cell right)) x)]
    exact endpoint_base_traffic_empty (by omega) (hright.constr _ (by omega)) bus sd
  have hl : (List.range (H-1)).flatMap
      (fun r => rowTraffic DedupTable.interactions (joinedTrace tr left right) 0 r pub bus sd)=
      (List.range (H-1)).flatMap
      (fun r => rowTraffic DedupTable.interactions tr left r pub bus sd) := by
    apply flatMap_congr'
    intro r hr
    exact base_traffic_current (fun x => congrFun
      (joined_left H (tr.cell left) (tr.cell right) (List.mem_range.mp hr)) x) bus sd
  have hr : (List.range H).flatMap
      (fun r => rowTraffic DedupTable.interactions (joinedTrace tr left right) 0 (H-1+r) pub bus sd)=
      (List.range H).flatMap
      (fun r => rowTraffic DedupTable.interactions tr right r pub bus sd) := by
    apply flatMap_congr'
    intro r hr
    exact base_traffic_current (fun x => congrFun
      (joined_right (by omega) (tr.cell left) (tr.cell right) (List.mem_range.mp hr)) x) bus sd
  have hsplit : List.range (2*H)=
      (List.range (H-1) ++ (List.range H).map (fun r => H-1+r)) ++ [2*H-1] := by
    have he : 2*H=(H-1+H)+1 := by omega
    rw [he, List.range_succ, List.range_add]
    congr 1
  simp only [joined_height]
  change (List.range (2*H)).flatMap _ = _
  rw [hsplit, List.flatMap_append, List.flatMap_append, List.flatMap_map]
  simp only [Function.comp_def, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    hclone, hl, hr, hheight, left_normal_row _ _ _ _ _ _ hb,
    right_normal_row _ _ _ _ _ _ hb]
  rw [drop_last _ H hp]

/-- Exact multiplicity counts are preserved for every non-carry bus and payload. -/
theorem joined_counts {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hright : TableLocal (rightTable sourceCarryBus) tr right pub)
    (hheight : tr.height right=tr.height left)
    (bus : Nat) (sd : Bool) (hb : bus≠sourceCarryBus) (m : List Fp) :
    tableBusCount DedupTable.interactions (joinedTrace tr left right) 0 pub bus sd m =
      tableBusCount (leftInteractions sourceCarryBus) tr left pub bus sd m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub bus sd m := by
  simp only [tableBusCount_eq]
  rw [joined_messages hright hheight bus sd hb, List.count_append]

/-- Sound reconstruction of an accepting physical source pair: local equations
and every external bus count are preserved. Global bus isolation and the
cryptographic theorem must supply the stated exact carry balance. -/
theorem joined_sound {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable sourceCarryBus) tr left pub)
    (hright : TableLocal (rightTable sourceCarryBus) tr right pub)
    (hheight : tr.height right=tr.height left)
    (hbal : ∀ m,
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m =
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m +
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m) :
    TableLocal (DedupTable.table 24) (joinedTrace tr left right) 0 pub ∧
    ∀ bus, bus≠sourceCarryBus → ∀ sd m,
      tableBusCount DedupTable.interactions (joinedTrace tr left right) 0 pub bus sd m =
        tableBusCount (leftInteractions sourceCarryBus) tr left pub bus sd m +
        tableBusCount (rightInteractions sourceCarryBus) tr right pub bus sd m := by
  refine ⟨joined_table_local hleft hright hheight
    (carry_cells tr left right (carry_equal_of_balance tr left right pub hbal)), ?_⟩
  intro bus hb sd m
  exact joined_counts hright hheight bus sd hb m

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
