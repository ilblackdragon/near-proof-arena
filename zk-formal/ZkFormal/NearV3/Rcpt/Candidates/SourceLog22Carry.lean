import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Tables

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra
open DedupPartitionTable

/-- On a reserved carry bus the middle table has precisely its named endpoint
messages, including when the caller inspects another boundary's bus. -/
theorem middle_carry_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (incoming outgoing b : Nat) (hb : 64 ≤ b) (sd : Bool) :
    rowTraffic (middleInteractions incoming outgoing) tr tt r pub b sd =
      (if outgoing=b ∧ sd=true ∧ r+1=tr.height tt then [carryRow tr tt r] else []) ++
      (if incoming=b ∧ sd=false ∧ r=0 then [carryRow tr tt r] else []) := by
  have hn : B_BYTES≠b ∧ B_DIGEST≠b ∧ B_RCL≠b ∧ B_SRC≠b ∧ B_SIZE≠b := by
    simp only [B_BYTES,B_DIGEST,B_RCL,B_SRC,B_SIZE]
    omega
  rcases hn with ⟨h0,h1,h2,h3,h4⟩
  cases sd <;> by_cases hi : incoming=b <;> by_cases ho : outgoing=b <;>
    by_cases hf : r=0 <;> by_cases hl : r+1=tr.height tt
  all_goals simp [middleInteractions,leftInteractions,DedupTable.interactions,
    rowTraffic,send,recv,h0,h1,h2,h3,h4,hi,ho,hf,hl,
    carryRow,carryMessage,DedupTable.width,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,List.map_map,Function.comp_def,
    eval_c,eval_isFirst,eval_isLast]
  all_goals split <;> simp

/-- Each actual middle table forwards exactly its final full row. -/
theorem middle_send (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (incoming outgoing : Nat) (hb : 64 ≤ outgoing) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic (middleInteractions incoming outgoing) tr tt r pub outgoing true) =
      [carryRow tr tt (tr.height tt-1)] := by
  have hp : 0 < tr.height tt := Nat.two_pow_pos _
  have he (r : Nat) : (if r+1=tr.height tt then [carryRow tr tt r] else []) =
      if r=tr.height tt-1 then [carryRow tr tt (tr.height tt-1)] else [] := by
    by_cases hr : r=tr.height tt-1
    · subst r; simp [show tr.height tt-1+1=tr.height tt by omega]
    · simp [hr,show r+1≠tr.height tt by omega]
  simp only [middle_carry_row tr tt _ pub incoming outgoing outgoing hb,
    Bool.true_eq_false, and_false, false_and, ite_false, List.append_nil,
    true_and, he]
  exact Render.SrcpGen.flatMap_at _ _ _ (by omega)

/-- Each actual middle table receives exactly its initial full row. -/
theorem middle_recv (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (incoming outgoing : Nat) (hb : 64 ≤ incoming) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic (middleInteractions incoming outgoing) tr tt r pub incoming false) =
      [carryRow tr tt 0] := by
  have hp : 0 < tr.height tt := Nat.two_pow_pos _
  have he (r : Nat) : (if r=0 then [carryRow tr tt r] else []) =
      if r=0 then [carryRow tr tt 0] else [] := by split <;> simp_all
  simp only [middle_carry_row tr tt _ pub incoming outgoing incoming hb,
    Bool.false_eq_true, and_false, false_and, ite_false, List.nil_append,
    true_and, he]
  exact Render.SrcpGen.flatMap_at _ _ _ hp

/-- The central boundary's actual send/receive balance authenticates all57
columns. Isolation of these counts from the rest of the AIR remains separate. -/
theorem middle_carry_equal (tr : Trace Fp) (left right : Nat) (pub : List Fp)
    (h : ∀ m, tableBusCount (middleInteractions 64 65) tr left pub 65 true m =
      tableBusCount (middleInteractions 65 66) tr right pub 65 false m) :
    carryRow tr left (tr.height left-1) = carryRow tr right 0 := by
  have hc := h (carryRow tr left (tr.height left-1))
  rw [tableBusCount_eq,tableBusCount_eq,middle_send tr left pub 64 65 (by decide),
    middle_recv tr right pub 65 66 (by decide)] at hc
  by_cases he : carryRow tr left (tr.height left-1) = carryRow tr right 0
  · exact he
  · simp [Ne.symm he] at hc

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
