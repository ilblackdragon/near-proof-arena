import ZkFormal.NearV3.Assembly.RcptCurrentInputFamily

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemLookup (r : Receipt) (i : Nat) : Bool :=
  systemEqual r || (systemMismatch r && i==firstMismatch r.signerId r.receiverId)

def systemLookupCount (r : Receipt) (i : Nat) : Nat :=
  if systemEqual r then i+1 else
    if systemMismatch r && decide (firstMismatch r.signerId r.receiverId≤i) then 1 else 0

def systemAux (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  let r := p.input.receipt
  if col=gV then bitCell (row.state==sV && systemLookup r row.index) else
  if col=gS then bitCell (row.state==sS && systemLookup r row.index) else
  if col=sx then Fp.ofNat ((r.receiverId.getD row.index 0).toNat) else
  if col=invD then (Fp.ofNat ((r.signerId.getD row.index 0).toNat)-
    Fp.ofNat ((r.receiverId.getD row.index 0).toNat))⁻¹ else
  if col=scnt then Fp.ofNat (systemLookupCount r row.index) else
  if col=invL then (Fp.ofNat r.signerId.length-Fp.ofNat r.receiverId.length)⁻¹ else fallback p row col

theorem systemIdentity_cells (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) :
    let cn := booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
    cn p ee=bitCell (systemEqual p.input.receipt) ∧
    cn p dm=bitCell (systemEqualLength p.input.receipt) ∧
    cn p dd=bitCell (systemMismatch p.input.receipt) ∧
    cn p sys=bitCell (p.input.receipt.predecessorId==AccountId.system) := by
  dsimp only
  refine ⟨?_,?_,?_,systemConstants_cell ctx (systemIdentityConstants constants) p⟩
  all_goals
    change boolInput _ (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)

theorem native_diff_nonzero (a b : Nat) (ha : a<ZkFormal.Algebra.P) (hb : b<ZkFormal.Algebra.P)
    (hne : a≠b) : Fp.ofNat a-Fp.ofNat b≠0 := by
  intro hh
  have he : Fp.ofNat a=Fp.ofNat b := by grind only
  have hn := congrArg Fp.toNat he
  simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hn
  exact hne hn

theorem systemMismatch_witness (r : Receipt) (h : systemMismatch r=true) :
    r.predecessorId=AccountId.system ∧ r.signerId.length=r.receiverId.length ∧
    firstMismatch r.signerId r.receiverId<r.signerId.length ∧
    r.signerId.getD (firstMismatch r.signerId r.receiverId) 0≠
      r.receiverId.getD (firstMismatch r.signerId r.receiverId) 0 := by
  simp only [systemMismatch,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq,systemEqualLength] at h
  have hn : r.signerId≠r.receiverId := by
    intro hh
    have he : systemEqual r=true := (systemEqual_iff r).mpr ⟨h.1.1,hh⟩
    rw [he] at h
    grind only
  have he : r.signerId.length=r.receiverId.length := by simpa only [beq_iff_eq] using h.2
  exact ⟨h.1.1,he,firstMismatch_witness _ _ he hn⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
