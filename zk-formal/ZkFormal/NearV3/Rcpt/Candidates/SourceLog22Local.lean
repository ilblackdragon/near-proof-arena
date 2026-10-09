import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Tables
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionLocal

set_option maxRecDepth 32768
namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra
open DedupPartitionTable DedupRender

/-- An interior partition starts at any positive logical offset. Its copied last
row is gated; every preceding transition uses the actual next logical row. -/
theorem middle_rows {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H off r : Nat) (hoff : 0 < off) (hr : r < H) (pub : Nat → Int) :
    ∀ ex ∈ middleConstraints,
      ev (cellsI bs rep (off+r)) (cellsI bs rep (off+((r+1)%H)))
        (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
        (if r+1=H then 0 else 1) pub ex = 0 := by
  intro ex hex
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hex
  by_cases hl : r+1=H
  · simp [hl,ev,Dsl.not,Dsl.sub,Dsl.k]
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    have hh := row_local h (R bs+off+H+1) (off+r) (by omega) (by omega) pub
    have hz : off+r≠0 := by omega
    have hlast : off+r+1≠R bs+off+H+1 := by omega
    have hmod : (off+r+1)%(R bs+off+H+1)=off+r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hz,hlast,ite_false,hmod] at hh
    have ht := right_of_zero_first (cellsI bs rep (off+r)) (cellsI bs rep (off+r+1))
      (if r=0 then 1 else 0) 0 1 pub hh (by simp)
    have hv := ht e (List.mem_append_left _ he)
    simpa [hl,hm,ev,Dsl.not,Dsl.sub,Dsl.k,Nat.add_assoc] using hv

theorem middle_mult_bits {bs : List SrcpB} {rep : Nat → Bool}
    {tr : Trace Fp} {tt r pos incoming outgoing : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x=Fp.ofNat (cell bs rep pos x)) :
    ∀ i∈middleInteractions incoming outgoing, ∀ b∈i.mult,
      b.eval tr tt r pub=0 ∨ b.eval tr tt r pub=1 := by
  intro i hi b hb
  rcases List.mem_append.mp hi with hi|hi
  · exact left_mult_bits hc i hi b hb
  · have he : i=Dsl.recv incoming .isFirst carryMessage := by simpa using hi
    subst i
    have he : b=.isFirst := by simpa [Dsl.recv] using hb
    subst b
    by_cases hf : r=0 <;> simp [eval_isFirst,hf]

/-- Complete honest TableLocal for either middle partition at the unchanged
protocol height cap. Its offset and row cells are explicit renderer inputs. -/
theorem middle_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt off incoming outgoing : Nat} {pub : List Fp}
    (hoff : 0 < off) (hlo : 1 ≤ tr.log tt) (hhi : tr.log tt ≤ 22)
    (hc : ∀ r, r<tr.height tt → ∀ x, tr.cell tt r x=Fp.ofNat (cell bs rep (off+r) x)) :
    TableLocal (middleTable incoming outgoing) tr tt pub := by
  refine ⟨hlo,hhi,?_,?_⟩
  · intro r hr ex hex
    have hp : 0<tr.height tt := Nat.two_pow_pos _
    apply eval_zero_of_ev
      (C:=cellsI bs rep (off+r)) (D:=cellsI bs rep (off+((r+1)%tr.height tt)))
      (fun x => (hc r hr x).trans (ofNat_int _))
      (fun x => (hc _ (Nat.mod_lt _ hp) x).trans (ofNat_int _))
    exact middle_rows h (tr.height tt) off r hoff hr
      (fun i => ((pub.getD i 0).toNat : Int)) ex hex
  · intro r hr
    exact middle_mult_bits (hc r hr)

/-- Extending the SIZE tuple leaves all local constraints and bits intact. -/
theorem source_local {T : Air.Table} {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal T tr tt pub) : TableLocal (SizeCount.sourceTable T) tr tt pub := by
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hm : b∈j.mult := by
    unfold SizeCount.withCount at hb
    split at hb <;> exact hb
  exact h.bits r hr j hj b hm

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
