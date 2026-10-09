import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFullKind
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
namespace ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecNativeBytes ProcPriorCodecSideFullKind

theorem core_header_cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:coreLayout I R present vid gb fwd=.ok out) (p : Nat) (hp:p<5) :
    out.rows[p]! = headerRow (instanceCells I R present vid) (parameters I R)
      (ProcPriorCodecNativeBytes.header R) present p := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  obtain ⟨added,ha,_,_⟩ := record_loop_quiet I R present vid gb fwd _ mid hm
  have he : out.rows.toList=
      (List.range 5).map (headerRow (instanceCells I R present vid) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present)++
      (added++hashRows I R present vid++ashRows I R present vid) := by
    rw [hr,ha]
    simp only [List.toList_toArray,headerRows,parameters,ProcPriorCodecNativeBytes.header,List.append_assoc]
  rw [←Array.getElem!_toList,he]
  simpa only [List.nil_append,List.length_nil,Nat.zero_add] using
    ProcCodecSuffixCells.appended_map [] (added++hashRows I R present vid++ashRows I R present vid)
      (headerRow (instanceCells I R present vid) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present) 5 p hp

theorem header_cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (p : Nat) (hp:p<5) :
    out.rows[p]! = headerRow (instanceCells I R present vid) (parameters I R)
      (ProcPriorCodecNativeBytes.header R) present p := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e=>simp [hc,Except.map] at h
  | ok o=>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_header_cell I R present vid gb fwd o hc p hp

theorem first_record_cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:0<R.n) :
    out.rows[5]! = ProcPriorCodecPlainStep.row I R present gb (instanceCells I R present vid) 0 0 0 := by
  obtain ⟨before,after,hs,_,ha⟩ := ProcCodecGeneratedRecordPosition.cell I R present vid gb fwd out h
    0 0 0 (Nat.mul_pos hn hn) (by decide) (by decide)
  rw [ProcPriorCodecPlainStep.step_eq _ _ _ _ _ _ _ _ _ _ (by decide)] at hs
  simp only [Except.ok.injEq,ForInStep.yield.injEq] at hs
  subst after
  exact (Array.push_inj_right.mp ha).symm

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn1:0<R.n) (hn:R.n≤64) (ht:R.tau<P) (p : Nat) (hp:p<5) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows p)=0 := by
  have hl:=generated_length I R present vid gb fwd out h
  have hnext:p+1<out.rows.size := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hnext,header_cell I R present vid gb fwd out h p hp]
  by_cases h4:p=4
  · subst p
    rw [show 4+1=5 from rfl,first_record_cell I R present vid gb fwd out h hn1]
    exact ProcPriorCodecHeaderFullKind.to_first_record I R present vid gb hparam hn ht 1
  · rw [header_cell I R present vid gb fwd out h (p+1) (by omega)]
    exact ProcPriorCodecHeaderFullKind.inside I R present vid p (by omega) hparam hn ht 1

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hparam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn1:0<R.n) (hn:R.n≤64) (ht:R.tau<P) (t p : Nat) (hp:p<5) (pub : List Fp) :
    ∀e∈kindGroup,e.eval (SchedHeight.trace out.rows codecPad) t p pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  have hl:=generated_length I R present vid gb fwd out h
  intro e he
  have hb:e.pubBound=0 := (by decide +kernel : ∀e∈kindGroup,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t p (by omega) pub e hb]
  exact active I R present vid gb fwd out h hparam hn1 hn ht p hp e he

end ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
