import ZkFormal.NearV3.Assembly.RcptSystemArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem systemLookupCount_start (r : Receipt) :
    systemLookupCount r 0=if systemLookup r 0 then 1 else 0 := by
  by_cases he : systemEqual r=true
  · simp [systemLookupCount,systemLookup,he]
  · by_cases hm : systemMismatch r=true
    · by_cases hi : firstMismatch r.signerId r.receiverId=0
      · simp [systemLookupCount,systemLookup,he,hm,hi]
      · have hn : ¬firstMismatch r.signerId r.receiverId≤0 := by omega
        simp [systemLookupCount,systemLookup,he,hm,hi,hn,Ne.symm hi]
    · simp [systemLookupCount,systemLookup,he,hm]

theorem systemLookupCount_step (r : Receipt) (i : Nat) :
    systemLookupCount r (i+1)=systemLookupCount r i+(if systemLookup r (i+1) then 1 else 0) := by
  by_cases he : systemEqual r=true
  · simp [systemLookupCount,systemLookup,he]
  · by_cases hm : systemMismatch r=true
    · by_cases hk : firstMismatch r.signerId r.receiverId≤i
      · have hk' : firstMismatch r.signerId r.receiverId≤i+1 := by omega
        have hne : i+1≠firstMismatch r.signerId r.receiverId := by omega
        simp [systemLookupCount,systemLookup,he,hm,hk,hk',hne]
      · by_cases hk' : firstMismatch r.signerId r.receiverId≤i+1
        · have hidx : firstMismatch r.signerId r.receiverId=i+1 := by omega
          simp [systemLookupCount,systemLookup,he,hm,hk,hk',hidx]
        · have hne : i+1≠firstMismatch r.signerId r.receiverId := by omega
          simp [systemLookupCount,systemLookup,he,hm,hk,hk',hne]
    · simp [systemLookupCount,systemLookup,he,hm]

theorem systemLookupCount_end (r : Receipt) (h : systemMismatch r=true) (i : Nat)
    (hi : i+1=r.signerId.length) : systemLookupCount r i=1 := by
  have hw := systemMismatch_witness r h
  have hn : systemEqual r=false := by
    have hh := h
    simp only [systemMismatch,Bool.and_eq_true,Bool.not_eq_true'] at hh
    exact hh.1.2
  have hk : firstMismatch r.signerId r.receiverId≤i := by omega
  simp only [systemLookupCount,hn,Bool.false_eq_true,ite_false,h,hk,decide_true,Bool.true_and,ite_true]

theorem systemLookup_mismatch_index (r : Receipt) (i : Nat)
    (hm : systemMismatch r=true) (hl : systemLookup r i=true) :
    i=firstMismatch r.signerId r.receiverId := by
  have hh := hm
  simp only [systemMismatch,Bool.and_eq_true,Bool.not_eq_true'] at hh
  simp only [systemLookup,hh.1.2,Bool.false_or,hm,Bool.true_and,beq_iff_eq] at hl
  exact hl

end ZkFormal.NearV3.Assembly.RcptSkeleton
