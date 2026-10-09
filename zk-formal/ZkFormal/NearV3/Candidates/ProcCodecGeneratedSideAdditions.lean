import ZkFormal.NearV3.Candidates.ProcPriorCodecSideAdditions
import ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBase
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedSideAdditions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecNativeHash ProcPriorCodecRecordStep ProcPriorCodecStepRows ProcPriorCodecExtra
open ZkFormal.NearV3.Assembly.CodecDigest

theorem first_indices (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:0<R.n) :
    out.rows[5]![srcC]! =0 ∧ out.rows[5]![useC]! =0 := by
  have hp := ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h 0 0 0
    (Nat.mul_pos hn hn) (by decide) (by decide)
    (fun a=>a[srcC]! =0 ∧ a[useC]! =0)
  apply hp
  intro before after hs
  obtain ⟨tail,ht,ha⟩:=successful_row I R present gb fwd (instanceCells I R present vidV) 0 0 0 before after (by decide) (by decide) hs
  refine ⟨_,ha,?_⟩
  have hc:=ProcPriorCodecRecordBase.counters I present R.n 0 0 0 5 (idByte I.ids 0 0) (if ¬present then 0 else idByte I.ids 0 0) (b2n I.allowed[0]!) gb[0]! (instanceCells I R present vidV) tail ht
  exact ⟨by simpa [record] using hc.1,by simpa [record] using hc.2.1⟩

theorem header (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:0<R.n)
    (p : Nat) (hp:p<5) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows p)=0 := by
  have hs:=generated_length I R present vidV gb fwd out h
  have hnext:p+1<out.rows.size := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hnext,ProcCodecHeaderKind.header_cell I R present vidV gb fwd out h p hp]
  apply ProcPriorCodecSideAdditions.header
  · intro he
    subst p
    rw [(first_indices I R present vidV gb fwd out h hn).1]; rfl
  · intro he
    subst p
    rw [(first_indices I R present vidV gb fwd out h hn).2]; rfl

theorem suffix (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hr:r<out.rows.size) (hlo:5+24*(R.n*R.n)≤r) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hl:=generated_length I R present vidV gb fwd out h
  by_cases hh:r<5+24*(R.n*R.n)+32
  · have he:r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))) := by omega
    have hj:r-(5+24*(R.n*R.n))<32 := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [he,ProcCodecSuffixCells.hash_cell I R present vidV gb fwd out h _ hj]
    exact ProcPriorCodecSideAdditions.hash I R present vidV _ _ _ _ _ _ _ _
  · have he:r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)) := by omega
    have hj:r-(5+24*(R.n*R.n)+32)<32 := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [he,ProcCodecSuffixCells.ash_cell I R present vidV gb fwd out h _ hj]
    exact ProcPriorCodecSideAdditions.ash I R present vidV _ _ _ _ _ _
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedSideAdditions
