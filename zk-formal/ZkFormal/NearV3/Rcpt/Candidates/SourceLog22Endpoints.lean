import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Local

set_option maxRecDepth 32768
namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra
open DedupPartitionTable DedupRender

/-- The first partition needs no two-partition capacity assumption. Its final
row is copied to the next partition and is locally gated. -/
theorem first_rows {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H r : Nat) (hr : r<H) (pub : Nat → Int) :
    ∀ ex∈leftConstraints,
      ev (cellsI bs rep r) (cellsI bs rep ((r+1)%H))
        (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
        (if r+1=H then 0 else 1) pub ex=0 := by
  by_cases hl : r+1=H
  · simp only [hl,ite_true]
    exact left_last _ _ _ 0 pub
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hl,ite_false,hm]
    apply left_of_not_last _ _ _ 1 pub
    have hh := row_local h (R bs+H+1) r (by omega) (by omega) pub
    have hg : r+1≠R bs+H+1 := by omega
    have hmg : (r+1)%(R bs+H+1)=r+1 := Nat.mod_eq_of_lt (by omega)
    simpa only [hg,ite_false,hmg] using hh

/-- A final partition may begin at any positive offset. Actual capacity places
padding at its last row and discharges the ungated cyclic-endpoint constraints. -/
theorem last_rows {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H off r : Nat) (hoff : 0<off) (hR : R bs≤off+H-1) (hr : r<H)
    (pub : Nat → Int) :
    ∀ ex∈rightConstraints,
      ev (cellsI bs rep (off+r)) (cellsI bs rep (off+((r+1)%H)))
        (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
        (if r+1=H then 0 else 1) pub ex=0 := by
  by_cases hl : r+1=H
  · simp only [hl,ite_true,Nat.mod_self,Nat.add_zero]
    rw [padding_cellsI bs rep (off+r) (by omega)]
    apply right_of_zero_first _ _ _ 1 0 pub
    · exact padding_physical_last (size bs) (cellsI bs rep off) pub
    · simp [SrcpV3.rt,SrcpV3.sg,SrcpV3.sz]
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hl,ite_false,hm]
    apply right_of_zero_first _ _ _ 0 1 pub _ (by simp)
    have hh := row_local h (R bs+off+H+1) (off+r) (by omega) (by omega) pub
    have hz : off+r≠0 := by omega
    have hg : off+r+1≠R bs+off+H+1 := by omega
    have hmg : (off+r+1)%(R bs+off+H+1)=off+r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hz,hg,ite_false,hmg] at hh
    simpa only [Nat.add_assoc] using hh

theorem first_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlo : 1≤tr.log tt) (hhi : tr.log tt≤22)
    (hc : ∀ r,r<tr.height tt → ∀ x,tr.cell tt r x=Fp.ofNat (cell bs rep r x)) :
    TableLocal firstTable tr tt pub := by
  refine ⟨hlo,hhi,?_,?_⟩
  · intro r hr ex hex
    have hp : 0<tr.height tt := Nat.two_pow_pos _
    apply eval_zero_of_ev (C:=cellsI bs rep r) (D:=cellsI bs rep ((r+1)%tr.height tt))
      (fun x => (hc r hr x).trans (ofNat_int _))
      (fun x => (hc _ (Nat.mod_lt _ hp) x).trans (ofNat_int _))
    exact first_rows h (tr.height tt) r hr (fun i => ((pub.getD i 0).toNat:Int)) ex hex
  · intro r hr
    exact left_mult_bits (hc r hr)

theorem last_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt off : Nat} {pub : List Fp}
    (hoff : 0<off) (hlo : 1≤tr.log tt) (hhi : tr.log tt≤22)
    (hR : R bs≤off+tr.height tt-1)
    (hc : ∀ r,r<tr.height tt → ∀ x,tr.cell tt r x=Fp.ofNat (cell bs rep (off+r) x)) :
    TableLocal lastTable tr tt pub := by
  refine ⟨hlo,hhi,?_,?_⟩
  · intro r hr ex hex
    have hp : 0<tr.height tt := Nat.two_pow_pos _
    apply eval_zero_of_ev
      (C:=cellsI bs rep (off+r)) (D:=cellsI bs rep (off+((r+1)%tr.height tt)))
      (fun x => (hc r hr x).trans (ofNat_int _))
      (fun x => (hc _ (Nat.mod_lt _ hp) x).trans (ofNat_int _))
    exact last_rows h (tr.height tt) off r hoff hR hr
      (fun i => ((pub.getD i 0).toNat:Int)) ex hex
  · intro r hr
    exact right_mult_bits (hc r hr)

/-- Four honest cap22 partitions, including the actual arity-three SIZE wrapper.
The same renderer cells are placed with one overlap row at each boundary. -/
theorem honest_four_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (hR : R bs≤16334272) {tr : Trace Fp} {t0 t1 t2 t3 : Nat} {pub : List Fp}
    (hl : ∀ t∈[t0,t1,t2,t3],tr.log t=22)
    (h0 : ∀ r,r<2^22 → ∀ x,tr.cell t0 r x=Fp.ofNat (cell bs rep r x))
    (h1 : ∀ r,r<2^22 → ∀ x,tr.cell t1 r x=Fp.ofNat (cell bs rep ((2^22-1)+r) x))
    (h2 : ∀ r,r<2^22 → ∀ x,tr.cell t2 r x=Fp.ofNat (cell bs rep (2*(2^22-1)+r) x))
    (h3 : ∀ r,r<2^22 → ∀ x,tr.cell t3 r x=Fp.ofNat (cell bs rep (3*(2^22-1)+r) x)) :
    TableLocal (SizeCount.sourceTable firstTable) tr t0 pub ∧
    TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr t1 pub ∧
    TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr t2 pub ∧
    TableLocal (SizeCount.sourceTable lastTable) tr t3 pub := by
  have l0 := hl t0 (by simp)
  have l1 := hl t1 (by simp)
  have l2 := hl t2 (by simp)
  have l3 := hl t3 (by simp)
  have H0 : tr.height t0=2^22 := congrArg (2^·) l0
  have H1 : tr.height t1=2^22 := congrArg (2^·) l1
  have H2 : tr.height t2=2^22 := congrArg (2^·) l2
  have H3 : tr.height t3=2^22 := congrArg (2^·) l3
  refine ⟨source_local (first_local h (by omega) (by omega) ?_),
    source_local (middle_local h (off:=2^22-1) (by decide) (by omega) (by omega) ?_),
    source_local (middle_local h (off:=2*(2^22-1)) (by decide) (by omega) (by omega) ?_),
    source_local (last_local h (off:=3*(2^22-1)) (by decide) (by omega) (by omega) ?_ ?_)⟩
  · simpa only [H0] using h0
  · simpa only [H1] using h1
  · simpa only [H2] using h2
  · rw [H3]; omega
  · simpa only [H3] using h3

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
