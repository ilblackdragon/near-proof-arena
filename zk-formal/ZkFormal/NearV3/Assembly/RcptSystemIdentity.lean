import ZkFormal.NearV3.Assembly.RcptCharacterComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemEqual (r : Receipt) : Bool :=
  r.predecessorId==AccountId.system && r.signerId==r.receiverId

def systemEqualLength (r : Receipt) : Bool := r.signerId.length==r.receiverId.length

def systemMismatch (r : Receipt) : Bool :=
  r.predecessorId==AccountId.system && !systemEqual r && systemEqualLength r

/-- Native system identity flags. This does not alter receipt inputs or impose
signer equality on ordinary receipts. -/
def systemIdentityConstants (fallback : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=ee then bitCell (systemEqual p.input.receipt) else
  if col=dm then bitCell (systemEqualLength p.input.receipt) else
  if col=dd then bitCell (systemMismatch p.input.receipt) else fallback p col

theorem systemEqual_iff (r : Receipt) : systemEqual r=true ↔
    r.predecessorId=AccountId.system ∧ r.signerId=r.receiverId := by
  simp only [systemEqual,Bool.and_eq_true,beq_iff_eq]

theorem systemEqual_length (r : Receipt) (h : systemEqual r=true) :
    r.signerId.length=r.receiverId.length := congrArg List.length ((systemEqual_iff r).mp h).2

theorem system_identity_arithmetic (r : Receipt) :
    bitCell (systemEqual r)*(1-bitCell (r.predecessorId==AccountId.system))=0 ∧
    bitCell (systemEqual r)*(Fp.ofNat r.signerId.length-Fp.ofNat r.receiverId.length)=0 ∧
    bitCell (systemMismatch r)=
      bitCell (r.predecessorId==AccountId.system)*(1-bitCell (systemEqual r))*bitCell (systemEqualLength r) := by
  constructor
  · by_cases he : systemEqual r=true
    · have hs := (systemEqual_iff r).mp he
      simp only [he,hs.1,beq_self_eq_true,bitCell,ite_true]
      grind only
    · simp only [bitCell,if_neg he]
      grind only
  · constructor
    · by_cases he : systemEqual r=true
      · rw [systemEqual_length r he]
        grind only
      · simp only [bitCell,if_neg he]
        grind only
    · unfold systemMismatch
      cases r.predecessorId==AccountId.system <;> cases systemEqual r <;>
        cases systemEqualLength r <;> simp only [Bool.not_true,Bool.not_false,Bool.true_and,Bool.false_and,
          bitCell,Bool.false_eq_true,ite_true,ite_false] <;> grind only

/-- The first unequal byte of equal-length strings. The zero value for missing
or unequal-length strings is never used as a mismatch witness. -/
def firstMismatch : Bytes→Bytes→Nat
  | a::as,b::bs=>if a=b then 1+firstMismatch as bs else 0
  | _,_=>0

theorem firstMismatch_witness (as bs : Bytes) (hlen : as.length=bs.length) (hne : as≠bs) :
    firstMismatch as bs<as.length ∧
    as.getD (firstMismatch as bs) 0≠bs.getD (firstMismatch as bs) 0 := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      by_cases he : a=b
      · subst b
        have htail : as≠bs := by intro hh;exact hne (hh ▸ rfl)
        obtain ⟨hi,hb⟩ := ih bs hlen htail
        simp only [firstMismatch,ite_true]
        constructor
        · simp only [List.length_cons];omega
        · simpa only [Nat.add_comm 1,List.getD_cons_succ] using hb
      · simp only [firstMismatch,if_neg he,List.length_cons,List.getD_cons_zero]
        exact ⟨by omega,he⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
