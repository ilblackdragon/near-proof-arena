import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22HonestTraffic
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Join

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Row-local traffic concatenates across an arbitrary-length physical prefix.
This lemma is independent of equal-height padding or honest renderer cells. -/
theorem prefix_messages {α : Type} (n m : Nat) (A B : Nat → Nat → Fp)
    (F : (Nat → Fp) → List α) :
    (List.range (n+m)).flatMap (fun r => F (prefixCells n A B r))=
      (List.range n).flatMap (fun r => F (A r)) ++
      (List.range m).flatMap (fun r => F (B r)) := by
  rw [List.range_add,List.flatMap_append,List.flatMap_map]
  congr 1
  · apply flatMap_congr'
    intro r hr
    rw [prefix_before n A B (List.mem_range.mp hr)]
  · apply flatMap_congr'
    intro r _
    rw [prefix_after]

/-- Unequal physical prefixes each own their first height-minus-one rows; the
last partition owns all its rows. Ordered multiplicity is preserved exactly. -/
theorem four_prefix_messages {α : Type} (a b c d : Nat)
    (A B C D : Nat → Nat → Fp) (F : (Nat → Fp) → List α) :
    (List.range (a+b+c+d)).flatMap
      (fun r => F (prefixCells a A (prefixCells b B (prefixCells c C D)) r))=
      (List.range a).flatMap (fun r => F (A r)) ++
      (List.range b).flatMap (fun r => F (B r)) ++
      (List.range c).flatMap (fun r => F (C r)) ++
      (List.range d).flatMap (fun r => F (D r)) := by
  rw [show a+b+c+d=a+(b+(c+d)) by omega,prefix_messages,prefix_messages,prefix_messages]
  simp only [List.append_assoc]

/-- Cloning an inactive endpoint to fill a power-of-two logical trace contributes
no messages. The retained prefix need not have any particular row length. -/
theorem clamped_messages {α : Type} (N n : Nat) (hn : n≤N)
    (C : Nat → Nat → Fp) (F : (Nat → Fp) → List α) (hz : F (C n)=[]) :
    (List.range N).flatMap (fun r => F (C (min r n)))=
      (List.range n).flatMap (fun r => F (C r)) := by
  conv => lhs; rw [show N=n+(N-n) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hpre : (List.range n).flatMap (fun r => F (C (min r n)))=
      (List.range n).flatMap (fun r => F (C r)) := by
    apply flatMap_congr'
    intro r hr
    rw [Nat.min_eq_left (by have := List.mem_range.mp hr; omega)]
  rw [hpre]
  have htail : (List.range (N-n)).flatMap (fun r => F (C (min (n+r) n)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r _
    rw [Nat.min_eq_right (by omega),hz]
  rw [htail,List.append_nil]

/-- Traffic is determined by current cells alone; this bridge covers all source
messages, including SIZE and SRC34, without canonical-natural assumptions. -/
def cellMessages (C : Nat → Fp) (bb : Nat) (sd : Bool) : List (List Fp) :=
  rowTraffic DedupTable.interactions
    ({log:=fun _ => 1,cell:=fun _ _ => C} : Trace Fp) 0 0 [] bb sd

theorem source_row_messages (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (bb : Nat) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt r pub bb sd=cellMessages (tr.cell tt r) bb sd := by
  simp only [cellMessages,DedupRender.candidate_rowT,SrcpProof.regsF]

/-- No extra SIZE output may hide in a cloned endpoint: all four traffic gates
must be zero. The local extraction theorem supplies these gate equations. -/
theorem cell_messages_zero (C : Nat → Fp)
    (hs : C SrcpV3.sg=0) (hr : C SrcpV3.rt=0)
    (hd : C SrcpV3.gD=0) (hz : C SrcpV3.gz=0) (bb : Nat) (sd : Bool) :
    cellMessages C bb sd=[] := by
  simp [cellMessages,DedupRender.candidate_rowT,hs,hr,hd,hz]

/-- Actual gated physical prefixes contribute their owned rows only. -/
theorem physical_prefix_messages {T : Air.Table} {tr : Trace Fp} {tt bb : Nat}
    {pub : List Fp} {sd : Bool}
    (hn : ∀ r,rowTraffic T.interactions tr tt r pub bb sd=
      if r+1=tr.height tt then [] else rowTraffic DedupTable.interactions tr tt r pub bb sd) :
    physicalMessages T tr tt pub bb sd=
      (List.range (tr.height tt-1)).flatMap (fun r => cellMessages (tr.cell tt r) bb sd) := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  unfold physicalMessages
  simp only [hn,source_row_messages]
  have he : List.range (tr.height tt)=List.range (tr.height tt-1)++[tr.height tt-1] := by
    simpa only [Nat.succ_eq_add_one,show tr.height tt-1+1=tr.height tt by omega]
      using (@List.range_succ (tr.height tt-1))
  rw [he,List.flatMap_append]
  have hf : (List.range (tr.height tt-1)).flatMap (fun r => if r+1=tr.height tt then []
      else cellMessages (tr.cell tt r) bb sd)=
      (List.range (tr.height tt-1)).flatMap (fun r => cellMessages (tr.cell tt r) bb sd) := by
    apply flatMap_congr'
    intro r hr
    have := List.mem_range.mp hr
    simp only [show r+1≠tr.height tt by omega,ite_false]
  rw [hf]
  simp only [List.flatMap_cons,List.flatMap_nil,show tr.height tt-1+1=tr.height tt by omega,
    ite_true,List.append_nil]

/-- External traffic from arbitrary four physical traces equals the unequal-
length splice of their current cells. No carry, local validity, or honest witness
premise is used in this purely physical ownership identity. -/
theorem physical_four_splice (tr : Trace Fp) (a b c d : Nat) (pub : List Fp)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) :
    physicalMessages firstTable tr a pub bb sd ++
      physicalMessages (middleTable 64 65) tr b pub bb sd ++
      physicalMessages (middleTable 65 66) tr c pub bb sd ++
      physicalMessages lastTable tr d pub bb sd=
    (List.range ((tr.height a-1)+(tr.height b-1)+(tr.height c-1)+tr.height d)).flatMap
      (fun r => cellMessages
        (prefixCells (tr.height a-1) (tr.cell a)
          (prefixCells (tr.height b-1) (tr.cell b)
            (prefixCells (tr.height c-1) (tr.cell c) (tr.cell d))) r) bb sd) := by
  have p0 := physical_prefix_messages (T:=firstTable)
    (fun r => DedupPartitionTable.left_normal_row tr a r pub bb sd h0)
  have p1 := physical_prefix_messages (T:=middleTable 64 65)
    (fun r => middle_normal_row tr b r pub 64 65 bb sd h0 h1)
  have p2 := physical_prefix_messages (T:=middleTable 65 66)
    (fun r => middle_normal_row tr c r pub 65 66 bb sd h1 h2)
  have p3 : physicalMessages lastTable tr d pub bb sd=
      (List.range (tr.height d)).flatMap (fun r => cellMessages (tr.cell d r) bb sd) := by
    apply flatMap_congr'
    intro r _
    have he : rowTraffic lastTable.interactions tr d r pub bb sd=
        rowTraffic DedupTable.interactions tr d r pub bb sd := by
      simp [lastTable,DedupPartitionTable.rightTable,DedupPartitionTable.rightInteractions,
        rowTraffic,ZkFormal.Near.Dsl.recv,Ne.symm h2]
    rw [he,source_row_messages]
  rw [p0,p1,p2,p3]
  exact (four_prefix_messages (tr.height a-1) (tr.height b-1) (tr.height c-1) (tr.height d)
    (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d) (fun C => cellMessages C bb sd)).symm

/-- The physical splice identity also holds for actual arity-three SIZE tables. -/
theorem counted_physical_four_splice (tr : Trace Fp) (a b c d : Nat) (pub : List Fp)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) :
    physicalMessages (SizeCount.sourceTable firstTable) tr a pub bb sd ++
      physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr b pub bb sd ++
      physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr c pub bb sd ++
      physicalMessages (SizeCount.sourceTable lastTable) tr d pub bb sd=
    ((List.range ((tr.height a-1)+(tr.height b-1)+(tr.height c-1)+tr.height d)).flatMap
      (fun r => cellMessages
        (prefixCells (tr.height a-1) (tr.cell a)
          (prefixCells (tr.height b-1) (tr.cell b)
            (prefixCells (tr.height c-1) (tr.cell c) (tr.cell d))) r) bb sd)).map
      (fun m => if bb=B_SIZE then m++[0] else m) := by
  rw [counted_four_messages,physical_four_splice tr a b c d pub bb sd h0 h1 h2]

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
