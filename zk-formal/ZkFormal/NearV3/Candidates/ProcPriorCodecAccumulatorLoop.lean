import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulator
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLoop
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep
open ProcPriorCodecAccumulator

theorem bytes (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (gs : List Nat) (s out : State)
    (hk : k<R.n*R.n) (hg : ∀g∈gs,g<8)
    (h : forIn gs s (fun g st=>step I R present gb fwd inst k 2 g st)=.ok out) :
    out.2.2.1=s.2.2.1 ∧
    out.2.2.2.1=s.2.2.2.1+(gs.map (fun g=>256^g*postByte R k g)).sum ∧
    out.2.2.2.2.1=s.2.2.2.2.1 := by
  induction gs generalizing s with
  | nil =>
    simp [List.forIn_nil,pure,Except.pure] at h
    subst out
    simp
  | cons g gs ih =>
    have hg0 := hg g (by simp)
    cases he : step I R present gb fwd inst k 2 g s with
    | error e => simp [List.forIn_cons,he,bind,Except.bind] at h
    | ok result =>
      obtain ⟨mid,hr,_⟩ := ProcPriorCodecStepRows.successful I R present gb fwd inst k 2 g s result (by decide) hg0 he
      subst result
      have ht : forIn gs mid (fun g st=>step I R present gb fwd inst k 2 g st)=.ok out := by
        simpa [List.forIn_cons,he,bind,Except.bind] using h
      obtain ⟨ha,hp,hb⟩ := byte_native_accumulators I R present gb fwd inst k g s mid hg0 hk he
      obtain ⟨ha',hp',hb'⟩ := ih mid (fun j hj=>hg j (by simp [hj])) ht
      exact ⟨ha'.trans ha,by simpa [List.map_cons,List.sum_cons,hp,Nat.add_assoc] using hp',hb'.trans hb⟩
theorem low24_digits (v : Nat) :
    v%256+256*(v/256%256)+65536*(v/65536%256)=v%16777216 := by
  have h1 := Nat.mod_add_div v 256
  have h2 := Nat.mod_add_div (v/256) 256
  have h3 := Nat.mod_add_div (v/65536) 256
  have h4 := Nat.mod_add_div v 16777216
  have hd1 : v/256/256=v/65536 := by simp [Nat.div_div_eq_div_mul]
  have hd2 : v/65536/256=v/16777216 := by simp [Nat.div_div_eq_div_mul]
  rw [hd1] at h2
  rw [hd2] at h3
  omega

theorem eight_digit_sum (R : Run) (k : Nat) :
    ((List.range 8).map (fun g=>256^g*postByte R k g)).sum=
      (R.segs.getD k default).vfin%16777216 := by
  simpa [List.range_succ,postByte,Nat.add_assoc] using low24_digits (R.segs.getD k default).vfin

theorem allowance_complete (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (rows : Array (Array Nat))
    (cmps : List (Nat×Nat×Nat)) (out : State) (hk : k<R.n*R.n)
    (h : forIn (List.range 8) (rows,cmps,0,0,0,0)
      (fun g st=>step I R present gb fwd inst k 2 g st)=.ok out) :
    out.2.2.1=0 ∧ out.2.2.2.1=(R.segs.getD k default).vfin%16777216 ∧
      out.2.2.2.2.1=0 := by
  simpa [eight_digit_sum] using bytes I R present gb fwd inst k (List.range 8)
    (rows,cmps,0,0,0,0) out hk (by simpa using fun g (hg:g<8)=>hg) h
end ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLoop
