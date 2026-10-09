import ZkFormal.NearV3.Assembly.RcptEmittedTrace

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def BooleanValue (x : Fp) : Prop := x=0 ∨ x=1
/-- Concrete Boolean parameter normalization. Already-Boolean native flags are
preserved; this alone does not assert their gas/key/refund semantic meaning. -/
def boolInput (col : Nat) (x : Fp) : Fp :=
  if col∈boolCols then (if x=1 then 1 else 0) else x

theorem boolInput_boolean (col : Nat) (x : Fp) (hc : col∈boolCols) : BooleanValue (boolInput col x) := by
  simp only [boolInput,if_pos hc]
  split <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem boolInput_preserves (col : Nat) (x : Fp) (hx : BooleanValue x) : boolInput col x=x := by
  rcases hx with rfl|rfl <;> simp [boolInput]

def booleanConstants (f : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) (col : Nat) : Fp := boolInput col (f p col)
def booleanReceiptAux (f : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  boolInput col (f p row col)
def booleanHeaderAux (f : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  boolInput col (f p row col)

set_option maxRecDepth 4096 in
theorem boolCols_disjoint : ∀col∈boolCols,
    col≠j ∧ col≠nj ∧ col≠r ∧ col≠cj ∧ col≠o ∧ col≠oEnd ∧ col≠o2 ∧ col≠o2End ∧
    col≠Lp ∧ col≠Lv ∧ col≠Ls ∧ col≠idx ∧ col≠b ∧
    ¬(reg 0≤col ∧ col<reg 32) ∧ ¬(tok 0≤col ∧ col<tok 16) := by decide

theorem bitCell_boolean (x : Bool) : BooleanValue (bitCell x) := by
  cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem frameBit_boolean (x j : Nat) : BooleanValue (frameBit x j) := by
  have hb : (x/2^j)%2<2 := Nat.mod_lt _ (by decide)
  have he : (x/2^j)%2=0 ∨ (x/2^j)%2=1 := by omega
  rcases he with he|he <;> simp only [frameBit,he] <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem tokenAux_boolean (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (hb : ∀p row col,col∈boolCols→BooleanValue (fallback p row col))
    (p : ReceiptPlan) (row : Coord) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (tokenAux tokens fallback p row col) := by
  have hd := (boolCols_disjoint col hc).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [tokenAux,if_neg hd]
  split
  · exact frameBit_boolean _ _
  · exact hb p row col hc

theorem streamAux_boolean (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp)
    (hb : ∀p row col,col∈boolCols→BooleanValue (fallback p row col))
    (p : ReceiptPlan) (row : Coord) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (streamAux pub digests fallback p row col) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hne,hreg,_⟩ := boolCols_disjoint col hc
  simp only [streamAux,if_neg hreg,if_neg hne]
  exact hb p row col hc

theorem headerStreamAux_boolean (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp)
    (hb : ∀p row col,col∈boolCols→BooleanValue (fallback p row col))
    (p : ListPlan) (row : Coord) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (headerStreamAux own before fallback p row col) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hne,hreg,htok⟩ := boolCols_disjoint col hc
  simp only [headerStreamAux,if_neg hreg,if_neg hne,tokenHeaderAux,if_neg htok]
  exact hb p row col hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
