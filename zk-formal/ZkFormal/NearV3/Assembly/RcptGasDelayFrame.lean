import ZkFormal.NearV3.Assembly.RcptGasEffectiveNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The unchanged AIR's surplus stream. It is not asserted to be an actual
system refund, nor to satisfy the final convolution no-overflow bound. -/
def gasRawSurplusByte (ctx : ApplyCtx) (r : Receipt) (i : Nat) : Nat :=
  if ctx.gasPrice≤r.gasPrice then gasDifference ctx r i else 0

/-- A delay register contains an earlier native stream byte, or initial zero. -/
def byteDelay (bytes : Nat→Nat) (lag i : Nat) : Nat :=
  if lag<i then bytes (i-1-lag) else 0

def gasDelayByte (ctx : ApplyCtx) (r : Receipt) (j i : Nat) : Nat :=
  if j<4 then byteDelay (gasEffectiveByte ctx r) j i
  else byteDelay (gasRawSurplusByte ctx r) (j-4) i

def gasDelayAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP ∧ dl 0≤col ∧ col<dl 8 then
    Fp.ofNat (gasDelayByte ctx p.input.receipt (col-dl 0) row.index)
  else fallback p row col

theorem byteDelay_zero (bytes : Nat→Nat) (lag : Nat) : byteDelay bytes lag 0=0 := by simp [byteDelay]

theorem byteDelay_head (bytes : Nat→Nat) (i : Nat) : byteDelay bytes 0 (i+1)=bytes i := by simp [byteDelay]

theorem byteDelay_shift (bytes : Nat→Nat) (lag i : Nat) :
    byteDelay bytes (lag+1) (i+1)=byteDelay bytes lag i := by
  unfold byteDelay
  have hh : lag+1<i+1 ↔ lag<i := by omega
  simp only [hh]
  split
  · congr 1;omega
  · rfl

theorem gasDelay_zero (ctx : ApplyCtx) (r : Receipt) (j : Nat) : gasDelayByte ctx r j 0=0 := by
  simp only [gasDelayByte,byteDelay_zero,ite_self]

theorem gasDelay_heads (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    gasDelayByte ctx r 0 (i+1)=gasEffectiveByte ctx r i ∧
    gasDelayByte ctx r 4 (i+1)=gasRawSurplusByte ctx r i := by
  simp only [gasDelayByte,Nat.reduceLT,ite_true,ite_false,Nat.sub_self,byteDelay_head,and_self]

theorem gasDelay_shift (ctx : ApplyCtx) (r : Receipt) (j i : Nat)
    (hj : j∈[1,2,3,5,6,7]) : gasDelayByte ctx r j (i+1)=gasDelayByte ctx r (j-1) i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [gasDelayByte,Nat.reduceLT,Nat.reduceSub,ite_true,ite_false]
  all_goals exact byteDelay_shift _ _ _

theorem gasDelay_cell (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasDelayAux ctx fallback))) p ⟨sGP,i,len⟩ (dl j)=
      Fp.ofNat (gasDelayByte ctx p.input.receipt j i) := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
