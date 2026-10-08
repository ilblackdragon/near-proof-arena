import ZkFormal.NearV3.Render.Ups.CompactExtract.Kinds
import ZkFormal.NearV3.Extract.Ups.Layout
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows

/-- Segment boundary facts extracted from a compact physical table. -/
structure Wf (v : List UpsSeg) : Prop where
  canon : ∀s∈v,(∀i x,s.row i x<P) ∧ ∀x,s.nxt x<P
  rows : ∀s∈v,∀i,i<s.rows.length → RowOk (s.row i) (s.next i)
  start : ∀s∈v,0<s.rows.length ∧ s.row 0 sf=1
  act : ∀s∈v,∀i,i<s.rows.length → s.row i UpsV3.act=1
  stop : ∀s∈v,∀i,i<s.rows.length →
    (s.row i qb=1 ∧ s.row i pl=1 ∧ s.row i rootP=1 ↔ i+1=s.rows.length)
  after : ∀s∈v,s.nxt UpsV3.act=s.nxt sf
  count : (v.map (·.rows.length)).sum≤2^22

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
include hw hs

theorem rowLt (i x : Nat) : s.row i x<P := (hw.canon s hs).1 i x

theorem nextLt (i x : Nat) : s.next i x<P := by
  unfold UpsSeg.next
  split
  · exact rowLt hw hs _ _
  · exact (hw.canon s hs).2 x

theorem okRow {i : Nat} (hi : i<s.rows.length) : RowOk (s.row i) (s.next i) := hw.rows s hs i hi

theorem okIn {i : Nat} (hi : i+1<s.rows.length) : RowOk (s.row i) (s.row (i+1)) := by
  have h:=okRow hw hs (by omega : i<s.rows.length)
  simpa only [UpsSeg.next,hi,ite_true] using h

theorem notLast {i : Nat} (hi : i<s.rows.length) (hq : s.row i qb≠1) : i+1<s.rows.length := by
  by_cases h : i+1<s.rows.length
  · exact h
  · exact False.elim (hq ((hw.stop s hs i hi).2 (by omega)).1)

/-- The only layout boundary changed by compaction: W3 is followed by node part
one at physical row four, with no value-row interval. -/
theorem walkRows : 4<s.rows.length ∧ s.row 0 sf=1 ∧ s.row 1 wt1=1 ∧ s.row 2 wt2=1 ∧
    s.row 3 wt3=1 ∧ s.row 4 qb=1 ∧ s.row 4 pf=1 ∧ s.row 4 j=1 := by
  obtain ⟨h0,hf⟩:=hw.start s hs
  have nq : ∀i,i<s.rows.length →
      (s.row i sf=1 ∨ s.row i wt1=1 ∨ s.row i wt2=1 ∨ s.row i wt3=1) → s.row i qb≠1 := by
    intro i hi he
    obtain ⟨ha,hq,hk,-⟩:=currentKinds (okRow hw hs hi) (rowLt hw hs i)
    intro hb
    rcases ha with ha|ha <;> rcases he with he|he|he|he <;> omega
  have h1 : 1<s.rows.length:=notLast hw hs h0 (nq 0 h0 (.inl hf))
  have k0:=kinds (earlyWalkRowOk (okIn hw hs h1) (rowLt hw hs 0) (.inl hf)) (rowLt hw hs 0) (rowLt hw hs 1)
  have w1 : s.row 1 wt1=1:=k0.2.2.2.2.2.2.2.2.2.2.2.1 hf
  have h2 : 2<s.rows.length:=notLast hw hs h1 (nq 1 h1 (.inr (.inl w1)))
  have k1:=kinds (earlyWalkRowOk (okIn hw hs h2) (rowLt hw hs 1) (.inr (.inl w1))) (rowLt hw hs 1) (rowLt hw hs 2)
  have w2 : s.row 2 wt2=1:=k1.2.2.2.2.2.2.2.2.2.2.2.2.1 w1
  have h3 : 3<s.rows.length:=notLast hw hs h2 (nq 2 h2 (.inr (.inr (.inl w2))))
  have k2:=kinds (earlyWalkRowOk (okIn hw hs h3) (rowLt hw hs 2) (.inr (.inr w2))) (rowLt hw hs 2) (rowLt hw hs 3)
  have w3 : s.row 3 wt3=1:=k2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 w2
  have h4 : 4<s.rows.length:=notLast hw hs h3 (nq 3 h3 (.inr (.inr (.inr w3))))
  exact ⟨h4,hf,w1,w2,w3,w3_next (okIn hw hs h4) (rowLt hw hs 4) w3⟩
end
end ZkFormal.NearV3.Render.UpsRelay.Extract
