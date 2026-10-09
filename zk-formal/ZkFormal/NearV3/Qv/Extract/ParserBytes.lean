import ZkFormal.NearV3.Qv.Extract.ParserModes
import ZkFormal.NearV3.Qv.Extract.ParserRecord

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

def byteMessage (tr : Trace Fp) (tt r : Nat) : List Fp :=
  [tr.cell tt r vid,tr.cell tt r pos,tr.cell tt r byte]

theorem byte_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic interactions tr tt r pub B_VBYTES sd=
      if sd ∧ tr.cell tt r gb=1 then [byteMessage tr tt r] else [] := by
  cases sd <;> by_cases hg : tr.cell tt r gb=1 <;>
    simp [rowTraffic,interactions,send,recv,B_QVC,B_VBYTES,B_QSH,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,byteMessage,hg,eval_c]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

/-- A physical parser record emits bytes precisely when its logical length
is nonzero, including raw empty-value markers. -/
theorem record_byte_gate (r : Nat) (hr : s≤r) (hb : r<s+n) :
    tr.cell tt r gb=1 ↔ cv tr tt s len≠0 := by
  have hp := hs.1
  have ha : tr.cell tt r act=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have hg := byte_gate hL (show r<tr.height tt by omega) (hw r hr hb)
  rw [ha] at hg
  rcases isBool hL (show r<tr.height tt by omega) (hw r hr hb) (x:=vz) (by simp) with hz | hz
  · have hnz : cv tr tt s len≠0 := by
      intro he
      have hn := length_cases hL hfit hw hs
      have hn1 : n=1 := by rcases hn with hn | hn <;> omega
      have heq : s+n-1=r := by omega
      have hh := nonempty_length hL hfit hw hs (by simpa only [heq] using hz)
      omega
    rw [hz] at hg
    constructor
    · intro _; exact hnz
    · intro _; grind
  · have he := (empty_length hL hfit hw hs r hr hb hz).2
    rw [hz] at hg
    simp only [he,ne_eq,not_true_eq_false,iff_false]
    grind

theorem byte_segment_row (r : Nat) (hr : s≤r) (hb : r<s+n) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES sd=
      if sd ∧ cv tr tt s len≠0 then
        [[tr.cell tt s vid,((r-s:Nat):Fp),tr.cell tt r byte]] else [] := by
  rw [parser_traffic hL (show r<tr.height tt by omega) (hw r hr hb),byte_row]
  simp only [record_byte_gate hL hfit hw hs r hr hb]
  have hv := metadata hL hfit hw hs (x:=vid) (by simp) r hr hb
  have hpos := position hL hfit hw hs r hr hb
  simp only [byteMessage,hv,hpos]

theorem byte_segment (sd : Bool) :
    (List.range' s n).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES sd)=
    if sd ∧ cv tr tt s len≠0 then
      (List.range' s n).map (fun r => [tr.cell tt s vid,((r-s:Nat):Fp),tr.cell tt r byte])
    else [] := by
  have gen {α β : Type} (l : List α) (f : α → List β) (g : α → β)
      (p : Prop) [Decidable p] (h : ∀ x∈l, f x=if p then [g x] else []) :
      l.flatMap f=if p then l.map g else [] := by
    induction l with
    | nil => simp
    | cons a rest ih =>
      have ha := h a (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      rw [List.flatMap_cons,ha,ht]
      by_cases hp : p <;> simp [hp]
  apply gen
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hr
  simp only [Nat.one_mul] at he
  exact byte_segment_row hL hfit hw hs r (by omega) (by omega) sd

end ZkFormal.NearV3.Qv.Extract.Parser
