import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolean
import ZkFormal.NearV3.Candidates.ProcCodecCarryPosition
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordBoolean
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecNativeHash

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈ProcPriorCodecSideKind.booleanGroup,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  obtain ⟨before,after,hs,hcb,_,hpush⟩:=ProcCodecCarryPosition.cell I R present vid gb fwd out h k f g hk hf hg
  obtain ⟨a,ha,hbool⟩:=ProcPriorCodecRecordBoolean.actual_group I R present gb fwd vid k f g before after hcb hk hf hg hs
  have heq:a=out.rows[5+24*k+8*f+g]! := Array.push_inj_right.mp (ha.symm.trans hpush)
  subst a
  unfold ProcCodecPhysicalRows.rowEnvAt
  exact hbool _ _ _ _

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) (t : Nat) (pub : List Fp) :
    ∀e∈ProcPriorCodecSideKind.booleanGroup,e.eval
      (SchedHeight.trace out.rows codecPad) t (5+24*k+8*f+g) pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  have hl:=generated_length I R present vid gb fwd out h
  intro e he
  have hb:e.pubBound=0 := (by decide +kernel : ∀e∈ProcPriorCodecSideKind.booleanGroup,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t _ (by omega) pub e hb]
  exact active I R present vid gb fwd out h k f g hk hf hg e he

theorem physical_record_range (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64)
    (t r : Nat) (hlo:5≤r) (hhi:r<5+24*(R.n*R.n)) (pub : List Fp) :
    ∀e∈ProcPriorCodecSideKind.booleanGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
  rw [he]
  exact physical I R present vid gb fwd out h hn ((r-5)/24) ((r-5)%24/8) ((r-5)%24%8)
    (by omega) (by omega) (by omega) t pub

end ZkFormal.NearV3.Candidates.ProcCodecRecordBoolean
