import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22HonestTraffic

set_option maxRecDepth 32768
namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open DedupPartitionTable DedupRender

/-- Exact reserved-bus behavior excludes carry messages from unrelated endpoints. -/
theorem first_reserved_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (b : Nat) (hb : 64≤b) (sd : Bool) :
    rowTraffic firstTable.interactions tr tt r pub b sd=
      if b=64 ∧ sd=true ∧ r+1=tr.height tt then [carryRow tr tt r] else [] := by
  have hn : B_BYTES≠b ∧ B_DIGEST≠b ∧ B_RCL≠b ∧ B_SRC≠b ∧ B_SIZE≠b := by
    simp only [B_BYTES,B_DIGEST,B_RCL,B_SRC,B_SIZE]; omega
  rcases hn with ⟨h0,h1,h2,h3,h4⟩
  cases sd <;> by_cases hc : b=64 <;> by_cases hl : r+1=tr.height tt
  all_goals simp_all [firstTable,leftTable,leftInteractions,DedupTable.interactions,
    rowTraffic,send,recv,
    carryRow,carryMessage,DedupTable.width,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,List.map_map,Function.comp_def,eval_c,eval_isLast,B_BYTES,B_DIGEST,B_RCL,B_SRC,B_SIZE]
  all_goals omega

theorem last_reserved_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (b : Nat) (hb : 64≤b) (sd : Bool) :
    rowTraffic lastTable.interactions tr tt r pub b sd=
      if b=66 ∧ sd=false ∧ r=0 then [carryRow tr tt r] else [] := by
  have hn : B_BYTES≠b ∧ B_DIGEST≠b ∧ B_RCL≠b ∧ B_SRC≠b ∧ B_SIZE≠b := by
    simp only [B_BYTES,B_DIGEST,B_RCL,B_SRC,B_SIZE]; omega
  rcases hn with ⟨h0,h1,h2,h3,h4⟩
  cases sd <;> by_cases hc : b=66 <;> by_cases hf : r=0
  all_goals simp_all [lastTable,rightTable,rightInteractions,DedupTable.interactions,
    rowTraffic,send,recv,
    carryRow,carryMessage,DedupTable.width,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,List.map_map,Function.comp_def,eval_c,eval_isFirst,B_BYTES,B_DIGEST,B_RCL,B_SRC,B_SIZE]
  all_goals omega

private theorem at_last (tr : Trace Fp) (tt : Nat) :
    (List.range (tr.height tt)).flatMap (fun r =>
      if r+1=tr.height tt then [carryRow tr tt r] else [])=
      [carryRow tr tt (tr.height tt-1)] := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  have he (r : Nat) : (if r+1=tr.height tt then [carryRow tr tt r] else [])=
      if r=tr.height tt-1 then [carryRow tr tt (tr.height tt-1)] else [] := by
    by_cases hr : r=tr.height tt-1
    · subst r; simp [show tr.height tt-1+1=tr.height tt by omega]
    · simp [hr,show r+1≠tr.height tt by omega]
  simp only [he]
  exact Render.SrcpGen.flatMap_at _ _ _ (by omega)

private theorem at_first (tr : Trace Fp) (tt : Nat) :
    (List.range (tr.height tt)).flatMap (fun r =>
      if r=0 then [carryRow tr tt r] else [])=[carryRow tr tt 0] := by
  have he (r : Nat) : (if r=0 then [carryRow tr tt r] else [])=
      if r=0 then [carryRow tr tt 0] else [] := by split <;> simp_all
  simp only [he]
  exact Render.SrcpGen.flatMap_at _ _ _ (Nat.two_pow_pos _)

theorem first_reserved_messages (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (b : Nat) (hb : 64≤b) (sd : Bool) :
    physicalMessages firstTable tr tt pub b sd=
      if b=64 ∧ sd=true then [carryRow tr tt (tr.height tt-1)] else [] := by
  unfold physicalMessages
  simp only [first_reserved_row tr tt _ pub b hb sd]
  by_cases hc : b=64 ∧ sd=true
  · simp only [hc.1,hc.2, true_and,ite_true]
    exact at_last tr tt
  · have he (r : Nat) : ¬(b=64 ∧ sd=true ∧ r+1=tr.height tt) := by intro he; exact hc ⟨he.1,he.2.1⟩
    simp [hc,he]

theorem last_reserved_messages (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (b : Nat) (hb : 64≤b) (sd : Bool) :
    physicalMessages lastTable tr tt pub b sd=
      if b=66 ∧ sd=false then [carryRow tr tt 0] else [] := by
  unfold physicalMessages
  simp only [last_reserved_row tr tt _ pub b hb sd]
  by_cases hc : b=66 ∧ sd=false
  · simp only [hc.1,hc.2,true_and,ite_true]
    exact at_first tr tt
  · have he (r : Nat) : ¬(b=66 ∧ sd=false ∧ r=0) := by intro he; exact hc ⟨he.1,he.2.1⟩
    simp [hc,he]

theorem middle_reserved_messages (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (incoming outgoing b : Nat) (hb : 64≤b) (sd : Bool) :
    physicalMessages (middleTable incoming outgoing) tr tt pub b sd=
      (if outgoing=b ∧ sd=true then [carryRow tr tt (tr.height tt-1)] else []) ++
      (if incoming=b ∧ sd=false then [carryRow tr tt 0] else []) := by
  cases sd
  · by_cases hi : incoming=b
    · subst b
      simpa only [physicalMessages,middleTable,Bool.false_eq_true,and_false,ite_false,List.nil_append,and_self,ite_true]
        using middle_recv tr tt pub incoming outgoing hb
    · simp [physicalMessages,middleTable,middle_carry_row tr tt _ pub incoming outgoing b hb,
        hi]
  · by_cases ho : outgoing=b
    · subst b
      simpa only [physicalMessages,middleTable,Bool.true_eq_false,and_false,ite_false,List.append_nil,and_self,ite_true]
        using middle_send tr tt pub incoming outgoing hb
    · simp [physicalMessages,middleTable,middle_carry_row tr tt _ pub incoming outgoing b hb,
        ho]

/-- Honest shifted placement copies every carried column across a boundary. -/
theorem placed_carry_equal {tr : Trace Fp} {left right off : Nat}
    (bs : List SrcpB) (rep : Nat → Bool)
    (hl : ∀ r,r<tr.height left → ∀ x,tr.cell left r x=Fp.ofNat (cell bs rep (off+r) x))
    (hr : ∀ r,r<tr.height right → ∀ x,tr.cell right r x=
      Fp.ofNat (cell bs rep (off+(tr.height left-1)+r) x)) :
    carryRow tr left (tr.height left-1)=carryRow tr right 0 := by
  have hp : 0<tr.height left := Nat.two_pow_pos _
  have hq : 0<tr.height right := Nat.two_pow_pos _
  apply List.map_congr_left
  intro x _
  rw [hl _ (by omega),hr _ hq,Nat.add_zero]

/-- Full four-table carry balance, excluding extraneous reserved-bus messages.
Distinct boundary bus IDs prevent reordering the middle partitions. -/
theorem four_carry_messages {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (h01 : carryRow tr t0 (tr.height t0-1)=carryRow tr t1 0)
    (h12 : carryRow tr t1 (tr.height t1-1)=carryRow tr t2 0)
    (h23 : carryRow tr t2 (tr.height t2-1)=carryRow tr t3 0)
    (b : Nat) (hb : 64≤b) :
    physicalMessages firstTable tr t0 pub b true ++
      physicalMessages (middleTable 64 65) tr t1 pub b true ++
      physicalMessages (middleTable 65 66) tr t2 pub b true ++
      physicalMessages lastTable tr t3 pub b true=
    physicalMessages firstTable tr t0 pub b false ++
      physicalMessages (middleTable 64 65) tr t1 pub b false ++
      physicalMessages (middleTable 65 66) tr t2 pub b false ++
      physicalMessages lastTable tr t3 pub b false := by
  rw [first_reserved_messages tr t0 pub b hb,first_reserved_messages tr t0 pub b hb,
    last_reserved_messages tr t3 pub b hb,last_reserved_messages tr t3 pub b hb,
    middle_reserved_messages tr t1 pub 64 65 b hb,middle_reserved_messages tr t1 pub 64 65 b hb,
    middle_reserved_messages tr t2 pub 65 66 b hb,middle_reserved_messages tr t2 pub 65 66 b hb]
  by_cases h0 : b=64 <;> by_cases h1 : b=65 <;> by_cases h2 : b=66
  all_goals simp_all [eq_comm]

/-- Explicit honest placement closes every carry bus for the actual SIZE-wrapped
four-table family; no carry-balance premise is assumed. -/
theorem honest_four_carries {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool)
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (cell bs rep (3*(H-1)+r) x))
    (b : Nat) (hb : 64≤b) :
    physicalMessages (SizeCount.sourceTable firstTable) tr t0 pub b true ++
      physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub b true ++
      physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub b true ++
      physicalMessages (SizeCount.sourceTable lastTable) tr t3 pub b true=
    physicalMessages (SizeCount.sourceTable firstTable) tr t0 pub b false ++
      physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub b false ++
      physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub b false ++
      physicalMessages (SizeCount.sourceTable lastTable) tr t3 pub b false := by
  have H0 := hh t0 (by simp)
  have H1 := hh t1 (by simp)
  have H2 := hh t2 (by simp)
  have H3 := hh t3 (by simp)
  have h01 : carryRow tr t0 (tr.height t0-1)=carryRow tr t1 0 := by
    apply placed_carry_equal bs rep (off:=0)
    · simpa only [H0,Nat.zero_add] using h0
    · simpa only [H0,H1,Nat.zero_add] using h1
  have h12 : carryRow tr t1 (tr.height t1-1)=carryRow tr t2 0 := by
    apply placed_carry_equal bs rep (off:=H-1)
    · simpa only [H1] using h1
    · simpa only [H1,H2,show (H-1)+(H-1)=2*(H-1) by omega] using h2
  have h23 : carryRow tr t2 (tr.height t2-1)=carryRow tr t3 0 := by
    apply placed_carry_equal bs rep (off:=2*(H-1))
    · simpa only [H2] using h2
    · simpa only [H2,H3,show 2*(H-1)+(H-1)=3*(H-1) by omega] using h3
  rw [counted_four_messages,counted_four_messages,four_carry_messages h01 h12 h23 b hb]

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
