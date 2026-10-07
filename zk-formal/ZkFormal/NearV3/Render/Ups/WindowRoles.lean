import ZkFormal.NearV3.Render.Ups.Tac

/-! Integer identities for the window selectors generated from semantic flags. -/
set_option maxHeartbeats 1000000
namespace ZkFormal.NearV3.Render.UpsGen

theorem s15_formula (I : UpsInst) (Q : UpsPartI) :
    s15V I Q = ind (Q.kind = 0) * ind (Q.sd = 1) +
      ind (Q.kind = 5) * (1 - ind (I.ts = 1)) := by
  by_cases h0 : Q.kind = 0 <;> by_cases h5 : Q.kind = 5 <;>
    by_cases hd : Q.sd = 1 <;> by_cases ht : I.ts = 1 <;>
    simp [s15V,S15B,ind,h0,h5,hd,ht] <;> omega

theorem target_formula (I : UpsInst) (Q : UpsPartI) (wi : Nat) :
    tgtV I Q 7 wi = fwV 7 wi * (1 - s15V I Q) + lastwV Q 7 wi * s15V I Q := by
  cases hs : S15B I Q <;> by_cases hf : wi = 0 <;> by_cases hl : wi + 1 = nWin Q.shape <;>
    simp [tgtV,TgtB,fwV,FwB,lastwV,LastwB,s15V,ind,hs,hf,hl]

theorem wy_formula (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind = 10) :
    wyV I Q 7 wi = fwV 7 wi * spY1V I Q + (1 - fwV 7 wi) * spY2V I Q := by
  cases h1 : Spy1B I Q <;> cases h2 : Spy2B I Q <;> by_cases hf : wi = 0 <;>
    simp [wyV,WyB,fwV,FwB,spY1V,spY2V,ind,h1,h2,hf,hk]

theorem wn_formula (I : UpsInst) (Q : UpsPartI) (wi : Nat) :
    wnV I Q 7 wi = ind (Q.kind = 5) * tgtV I Q 7 wi + ind (Q.kind = 10) * wyV I Q 7 wi := by
  by_cases h5 : Q.kind = 5 <;> by_cases h10 : Q.kind = 10 <;>
    cases ht : TgtB I Q 7 wi <;> cases hy : WyB I Q 7 wi <;>
    simp [wnV,WnB,tgtV,wyV,ind,h5,h10,ht,hy] <;> omega

theorem wfr_target (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind = 0 ∨ Q.kind = 5) :
    wfrV I Q 7 wi = tgtV I Q 7 wi := by
  rcases hk with h | h <;> simp [wfrV,WfrB,tgtV,h]

theorem wfr_fresh (I : UpsInst) (Q : UpsPartI) (wi : Nat)
    (hk : Q.kind = 1 ∨ Q.kind = 9 ∨ Q.kind = 11) : wfrV I Q 7 wi = 1 := by
  rcases hk with h | h | h <;> simp [wfrV,WfrB,ind,h]

theorem wfr_copy (I : UpsInst) (Q : UpsPartI) (wi : Nat)
    (hk : Q.kind = 3 ∨ Q.kind = 4 ∨ Q.kind = 7) : wfrV I Q 7 wi = 0 := by
  rcases hk with h | h | h <;> simp [wfrV,WfrB,ind,h]

theorem wfr_split (I : UpsInst) (Q : UpsPartI) (wi : Nat) (hk : Q.kind = 10) :
    wfrV I Q 7 wi = 1 - (1 - wyV I Q 7 wi) * xcpV I Q := by
  cases hy : WyB I Q 7 wi <;> cases hx : XcpB I Q <;>
    simp [wfrV,WfrB,wyV,xcpV,ind,hy,hx,hk]

theorem rdc_formula (I : UpsInst) (Q : UpsPartI) (ix wi : Nat) :
    rdcV I Q 7 ix wi = ind (ix = 0) * tgtV I Q 7 wi * upV Q := by
  by_cases h0 : Q.kind = 0 <;> by_cases h1 : Q.kind = 1 <;> by_cases h11 : Q.kind = 11 <;>
    by_cases hi : ix = 0 <;> cases ht : TgtB I Q 7 wi <;>
    simp [rdcV,RdcB,upV,kin,tgtV,ind,h0,h1,h11,hi,ht] <;> omega

end ZkFormal.NearV3.Render.UpsGen
