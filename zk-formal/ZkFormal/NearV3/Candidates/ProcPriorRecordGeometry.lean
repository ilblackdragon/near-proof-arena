import ZkFormal.NearV3.Candidates.ProcPriorRecordSound
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordGeometry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem words_bound (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1) :
    cv tr t r sender+cv tr t r receiver+cv tr t r amount≤cv tr t r act := by
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  have hsend:=ProcPriorRecordSound.flag hL hr hs sender (by simp)
  have hrecv:=ProcPriorRecordSound.flag hL hr hs receiver (by simp)
  have hamt:=ProcPriorRecordSound.flag hL hr hs amount (by simp)
  have he:=ProcPriorRecordSound.component_value hL hr hs
    (.mul (header false) (sub (header false) (k 1))) (by simp [constraints])
  change (Expr.mul (header false) (sub (header false) (k 1))).eval tr t r pub=0 at he
  rw [eval_eq] at he
  have hd:=(Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mp he
  rw [P_val] at hd
  have hdiv:∃q : Int,zev (tenv tr t r pub) (Expr.mul (header false) (sub (header false) (k 1)))=2013265921*q := ⟨zev (tenv tr t r pub) (Expr.mul (header false) (sub (header false) (k 1)))/2013265921,by omega⟩
  obtain ⟨q,hq⟩:=hdiv
  have cur (x : Nat) :zev (tenv tr t r pub) (.col x false)=(cv tr t r x : Int) := rfl
  simp only [header,words,zev_mul,zev_sub,zev_add,cur,zev_k] at hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha|ha <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsend with hsend|hsend <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrecv with hrecv|hrecv <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hamt with hamt|hamt <;>
    simp_all <;> omega

theorem limbs_eq (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1) :
    cv tr t r firstLimb+cv tr t r midLimb+cv tr t r topLimb=
      cv tr t r sender+cv tr t r receiver+cv tr t r amount := by
  have hf:=ProcPriorRecordSound.flag hL hr hs firstLimb (by simp)
  have hm:=ProcPriorRecordSound.flag hL hr hs midLimb (by simp)
  have ht:=ProcPriorRecordSound.flag hL hr hs topLimb (by simp)
  have hw:=words_bound hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  have he:=ProcPriorRecordSound.component_value hL hr hs (sub (limbs false) (words false)) (by simp [constraints])
  change (sub (limbs false) (words false)).eval tr t r pub=0 at he
  rw [eval_eq] at he
  have hd:=(Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mp he
  rw [P_val] at hd
  have hdiv:∃q : Int,zev (tenv tr t r pub) (sub (limbs false) (words false))=2013265921*q := ⟨zev (tenv tr t r pub) (sub (limbs false) (words false))/2013265921,by omega⟩
  obtain ⟨q,hq⟩:=hdiv
  have cur (x : Nat) :zev (tenv tr t r pub) (.col x false)=(cv tr t r x : Int) := rfl
  simp only [limbs,words,zev_sub,zev_add,cur] at hq
  omega

/-- A live write has exactly the amount/top selectors; the other word/limb
selectors are zero and the Record row is active. -/
theorem write_shape (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r writeGate=1) :
    cv tr t r act=1 ∧ cv tr t r sender=0 ∧ cv tr t r receiver=0 ∧
      cv tr t r amount=1 ∧ cv tr t r firstLimb=0 ∧ cv tr t r midLimb=0 ∧
      cv tr t r topLimb=1 ∧ cv tr t r senderFound=1 ∧ cv tr t r receiverFound=1 := by
  obtain ⟨ha,ht,hf,hrf⟩:=ProcPriorRecordSound.write_flags hL hr hs hw
  have hb:=words_bound hL hr hs
  have he:=limbs_eq hL hr hs
  have hac:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordGeometry
