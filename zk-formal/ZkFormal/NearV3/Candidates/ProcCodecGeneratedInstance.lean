import ZkFormal.NearV3.Candidates.ProcPriorCodecSideCarry
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedInstance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecSideCarry ProcPriorCodecRecordReads ProcPriorCodecExtra ProcPriorCodecNativeHash
open ProcPriorCodecRecordStep ProcPriorCodecStepRows ZkFormal.NearV3.Assembly.CodecDigest

theorem record (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : ProcPriorCodecExtraColumns.Tail tail) :
    Instance I R present vidV (ProcPriorCodecAssignments.recordRow I present R.n k f g p bpo bpr
      (instanceCells I R present vidV) (baseExtra R.n k f g a b++tail)) := by
  intro c hc
  have hh : c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre] := by
    simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [native_projection _ _ _ _ _ _ _ _ _ _ _ _ _ ht c hh,SchedSetAll.append]
  unfold instanceValue
  simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [scalars,SchedSetAll.lookup,tau,pres,vid,nn,NN,base,fair,
    kR,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]

theorem generated (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) :
    ∀a∈out.rows.toList,Instance I R present vidV a := by
  apply ProcCodecGeneratedForall.generated_good I R present vidV gb fwd out h (Instance I R present vidV)
  · intro k f g hk hf hg s result hs
    obtain ⟨tail,ht,ha⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f g s result hf hg hs
    exact ⟨_,ha,record I R present vidV k f g _ _ _ _ _ tail ht⟩
  · intro a ha
    simp only [headerRows] at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact header_instance I R present vidV _ _ j
  · intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact hash_instance I R present vidV _ _ _ j
  · intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact ash_instance I R present vidV _ j

/-- Every adjacent pair within a generated block carries the same instance,
including every field, record, and digest boundary. -/
theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hr : r+1<out.rows.size) :
    ∀e∈carryGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hrr : r<out.rows.size := by omega
  have hc := generated I R present vidV gb fwd out h out.rows[r]! (by simp [hrr])
  have hn := generated I R present vidV gb fwd out h out.rows[r+1]! (by simp [hr])
  simpa only [ProcCodecPhysicalRows.rowEnvAt,if_pos hr] using
    same_instance I R present vidV out.rows[r]! out.rows[r+1]! hc hn (if r=0 then 1 else 0) 0 1

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn : R.n≤64)
    (t r : Nat) (hr : r+1<out.rows.size) (pub : List Fp) :
    ∀e∈carryGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈carryGroup,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r (by omega) pub e hp]
  exact active I R present vidV gb fwd out h r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedInstance
