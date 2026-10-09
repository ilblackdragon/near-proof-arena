import ZkFormal.NearV3.Candidates.ProcCodecRecordBoolean
import ZkFormal.NearV3.Candidates.ProcCodecRecordKindPosition
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedZeroTests
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedInstance
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordBytePosition
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteGroup
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideFullKind
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordFullKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSideFullKind

theorem next_group (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈ProcPriorCodecSideNext.nextGroup,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hl : 5≤5+24*k+8*f+g := by omega
  have hr : 5+24*k+8*f+g<5+24*(R.n*R.n) := by omega
  have hsize := generated_length I R present vidV gb fwd out h
  have hnext : 5+24*k+8*f+g+1<out.rows.size := by omega
  have hA : out.rows[5+24*k+8*f+g]![kA]! =0 := by
    apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
      (fun a=>a[kA]! =0)
    intro before after hs
    obtain ⟨a,ha,_,_,_,_,hA,_⟩ := ProcPriorCodecRecordZeroRows.actual I R present gb fwd vidV k f g before after hf hg hs
    exact ⟨a,ha,hA⟩
  have hp := ProcCodecGeneratedRecordBytePosition.region I R present vidV gb fwd out h _ hl hr
  have hpn := ProcCodecGeneratedRecordBytePosition.next I R present vidV gb fwd out h _ hl hr
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hnext]
  apply ProcPriorCodecSideNext.encoded_next
  · change Fp.ofNat out.rows[5+24*k+8*f+g]![kA]! =0
    rw [hA]; rfl
  · change Fp.ofNat out.rows[5+24*k+8*f+g+1]![pos]! =Fp.ofNat out.rows[5+24*k+8*f+g]![pos]! +1
    rw [hp,hpn,ProcPriorCodecSideNext.cast_add]; rfl

/-- All retained kind constraints hold at every actual generated record row.
No local-validity or register-shape premise is supplied. -/
theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn:R.n≤64) (ht:R.tau<P)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hsize := generated_length I R present vidV gb fwd out h
  have hnext : 5+24*k+8*f+g+1<out.rows.size := by omega
  have hr : 5+24*k+8*f+g<out.rows.size := by omega
  have hb := ProcCodecRecordBoolean.active I R present vidV gb fwd out h k f g hk hf hg
  have hp := ProcCodecRecordKindPosition.phase I R present vidV gb fwd out h k f g hk hf hg
  have hpeq : ProcPriorCodecRecordPhase.phase=ProcPriorCodecSidePhase.phaseGroup := by decide +kernel
  rw [hpeq] at hp
  have hz := ProcCodecGeneratedZeroTests.active I R present vidV gb fwd out h hn ht _ hr
  have hc := ProcCodecGeneratedInstance.active I R present vidV gb fwd out h _ hnext
  have hnx := next_group I R present vidV gb fwd out h k f g hk hf hg
  have hbyte := ProcCodecGeneratedByteGroup.active I R present vidV gb fwd out h _ hr
  have hhdr := ProcCodecRecordKindPosition.header_inactive I R present vidV gb fwd out h k f g hk hf hg
  rw [decomposition]
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨hb,hp⟩,hz⟩,hc⟩,hnx⟩,hbyte⟩,hhdr⟩

theorem region (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn:R.n≤64) (ht:R.tau<P) (r : Nat) (hl:5≤r) (hr:r<5+24*(R.n*R.n)) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have he : r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
  rw [he]
  exact record I R present vidV gb fwd out h hn ht _ _ _ (by omega) (by omega) (by omega)
end ZkFormal.NearV3.Candidates.ProcCodecRecordFullKind
