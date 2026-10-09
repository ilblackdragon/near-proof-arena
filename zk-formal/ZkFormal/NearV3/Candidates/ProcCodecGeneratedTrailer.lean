import ZkFormal.NearV3.Candidates.ProcCodecSuffixTrailer
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTrailer
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedTrailer
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest

def GoodRow (a : Array Nat) : Prop := ∀(nxt : Nat→Fp) (first last trans : Fp),
  ∀e∈cTrl,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0

theorem core_prefix (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out) :
    ∃lead,lead.length=5+24*(R.n*R.n) ∧ (∀a∈lead,GoodRow a) ∧
      out.rows.toList=lead++hashRows I R present vid++ashRows I R present vid := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  have hh : ProcCodecGeneratedForall.Good GoodRow (headerRows I R present vid).toArray := by
    intro a ha
    simp only [List.toList_toArray,headerRows] at ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    exact ProcPriorCodecSideTrailer.header_trailer I R present vid _ _ p
  have hp : ProcCodecGeneratedForall.Records I R present vid gb fwd GoodRow := by
    intro k f g hk hf hg s out hs
    obtain ⟨a,ha,hp⟩ := ProcPriorCodecRecordTrailer.actual I R present gb fwd vid k f g s out hk hf hg hs (fun _=>0) 0 0 0
    refine ⟨a,ha,?_⟩
    intro nxt first last trans
    obtain ⟨b,hb,hq⟩ := ProcPriorCodecRecordTrailer.actual I R present gb fwd vid k f g s out hk hf hg hs nxt first last trans
    have he : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
    subst b
    exact hq
  have hg := ProcCodecGeneratedForall.blocks_good I R present vid gb fwd GoodRow hp _ mid hh hm
  obtain ⟨added,ha,hcount,_⟩ := record_loop_quiet I R present vid gb fwd _ mid hm
  refine ⟨mid.1.toList,?_,hg,hr⟩
  rw [ha,List.length_append,hcount]
  simp [headerRows]

theorem generated_prefix (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) :
    ∃lead,lead.length=5+24*(R.n*R.n) ∧ (∀a∈lead,GoodRow a) ∧
      out.rows.toList=lead++hashRows I R present vid++ashRows I R present vid := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_prefix I R present vid gb fwd o hc

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈cTrl,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hlen := generated_length I R present vid gb fwd out h
  by_cases hpre : r<5+24*(R.n*R.n)
  · obtain ⟨lead,hl,hgood,he⟩ := generated_prefix I R present vid gb fwd out h
    have hrlead : r<lead.length := by omega
    have roweq : out.rows[r]! = lead[r]! := by
      rw [←Array.getElem!_toList,he]
      rw [_root_.getElem!_pos (lead++hashRows I R present vid++ashRows I R present vid) r (by simp [hashRows,ashRows]; omega),
        List.getElem_append_left (by simp; omega),List.getElem_append_left hrlead,
        _root_.getElem!_pos lead r hrlead]
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [roweq]
    exact hgood lead[r]! (by simp [hrlead]) _ _ _ _
  · by_cases hh : r<5+24*(R.n*R.n)+32
    · have he : r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))) := by omega
      rw [he]
      exact ProcCodecSuffixTrailer.hash_active I R present vid gb fwd out h _ (by omega)
    · have he : r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)) := by omega
      rw [he]
      exact ProcCodecSuffixTrailer.ash_active I R present vid gb fwd out h _ (by omega)
theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hn : R.n≤64) (t r : Nat) (hr : r<2^22) (pub : List Fp) :
    ∀e∈cTrl,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  obtain ⟨hne,hcap⟩ := ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  intro e he
  by_cases ha : r<out.rows.size
  · have hp : e.pubBound=0 := (by decide +kernel : ∀e∈cTrl,e.pubBound=0) e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    exact active I R present vid gb fwd out h r ha e he
  · apply (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).1 e
    unfold ProcPriorCodecActual.table ProcPriorCodecActual.constraints
    exact List.mem_append_left _ (List.mem_append_right _ he)
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedTrailer
