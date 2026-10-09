import ZkFormal.NearV3.Candidates.ProcCodecExecutionPosition
import ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃before after a suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧ after.1=before.1.push a ∧
      out.rows.toList=after.1.toList++suffix := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  obtain ⟨bs,bo,_,bpost,hb,hbl,_,_,hbr⟩ := ProcCodecExecutionPosition.block I R present vid gb fwd _ mid hm k hk
  obtain ⟨fs,fo,_,fpost,hfstep,hfl,_,_,hfr⟩ := ProcCodecExecutionPosition.field I R present vid gb fwd k bs bo hb f hf
  obtain ⟨gs,go,_,gpost,hgstep,hgl,_,_,hgr⟩ := ProcCodecExecutionPosition.byte I R present vid gb fwd k f hf fs fo hfstep g hg
  obtain ⟨tail,ht,ha⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd (instanceCells I R present vid) k f g gs go hf hg hgstep
  refine ⟨gs,go,_,gpost++fpost++bpost++hashRows I R present vid++ashRows I R present vid,
    hgstep,?_,ha,?_⟩
  · rw [hgl,hfl,hbl]
    simp [headerRows]
  · rw [hr,hbr,hfr,hgr]
    simp only [List.append_assoc]

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃before after a suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧ after.1=before.1.push a ∧
      out.rows.toList=after.1.toList++suffix := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core I R present vid gb fwd o hc k f g hk hf hg

theorem cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃before after,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧
      after.1=before.1.push out.rows[5+24*k+8*f+g]! := by
  obtain ⟨before,after,a,suffix,he,hl,ha,ho⟩ := generated I R present vid gb fwd out h k f g hk hf hg
  have hc : out.rows[5+24*k+8*f+g]! = a := by
    rw [←Array.getElem!_toList,ho,ha,Array.toList_push,←hl]
    simpa only [List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
      Array.length_toList,Nat.add_zero] using
      ProcCodecSuffixCells.appended_map before.1.toList suffix (fun _=>a) 1 0 (by decide)
  exact ⟨before,after,he,hl,by rw [hc]; exact ha⟩
theorem property (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (P : Array Nat→Prop)
    (hp : ∀before after,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after)→
      ∃a,after.1=before.1.push a ∧ P a) : P out.rows[5+24*k+8*f+g]! := by
  obtain ⟨before,after,he,_,ha⟩ := cell I R present vid gb fwd out h k f g hk hf hg
  obtain ⟨a,ha',hp⟩ := hp before after he
  have heq : a=out.rows[5+24*k+8*f+g]! := Array.push_inj_right.mp (ha'.symm.trans ha)
  simpa only [heq] using hp
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
