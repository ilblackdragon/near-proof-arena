import ZkFormal.NearV3.Candidates.ProcActualMemoryChains
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem read (g : Gen.Seg) (t v w : Nat) :
    OpOk g v w ⟨t,OP_READ,v,v,w,w,0,false,false,false⟩ := by
  refine ⟨Or.inl rfl,rfl,rfl,?_,?_⟩
  · intro _;simp
  · intro h;cases h

theorem link (g : Gen.Seg) (t v w inc : Nat) (ok : Bool)
    (hl:g.isL=true) (hk:ok=true→g.al=true) :
    OpOk g v w ⟨t,OP_GRANT,v,(if ok then v-inc else v),w,
      (if ok then w+inc else w),inc,ok,g.al,decide (inc≤v)⟩ := by
  refine ⟨Or.inr rfl,rfl,rfl,?_,?_⟩
  · intro h;cases h
  · intro _
    refine ⟨rfl,by simp [hl],hk,?_,?_⟩
    · by_cases hi:inc≤v
      · cases ok <;> simp [hi]
      · cases ok <;> simp [hi,Nat.sub_eq_zero_of_le (by omega : v≤inc)]
    · cases ok <;> simp [hl]

theorem budget (g : Gen.Seg) (t v inc : Nat) (ok : Bool)
    (hl:g.isL=false) (hk:ok=true→inc≤v) :
    OpOk g v 0 ⟨t,OP_GRANT,v,(if ok then v-inc else v),0,0,inc,ok,
      decide (inc≤v),decide (inc≤v)⟩ := by
  refine ⟨Or.inr rfl,rfl,rfl,?_,?_⟩
  · intro h;cases h
  · intro _
    refine ⟨rfl,by simp [hl],?_,?_,by simp [hl]⟩
    · intro h;exact decide_eq_true (hk h)
    · cases ho:ok
      · rfl
      · simp [hk ho]
end ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics
