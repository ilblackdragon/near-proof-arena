import ZkFormal.NearV3.Candidates.ProcCodecExecutionFieldPrefix
import ZkFormal.NearV3.Candidates.ProcCodecExecutionPosition
import ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPrefix
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃rows cmps before after a suffix,
      forIn (List.range g) (rows,cmps,0,0,0,0)
        (fun j st=>step I R present gb fwd (instanceCells I R present vid) k f j st)=.ok before ∧
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧ after.1=before.1.push a ∧
      out.rows.toList=after.1.toList++suffix := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  obtain ⟨bs,bo,_,bpost,hb,hbl,_,_,hbr⟩ := ProcCodecExecutionPosition.block I R present vid gb fwd _ mid hm k hk
  obtain ⟨fs,fo,_,fpost,hfstep,hfl,_,_,hfr⟩ := ProcCodecExecutionPosition.field I R present vid gb fwd k bs bo hb f hf
  obtain ⟨gs,go,gpost,hprefix,hgstep,hgl,hgr⟩ := ProcCodecExecutionFieldPrefix.field I R present vid gb fwd k f hf fs fo hfstep g hg
  obtain ⟨tail,ht,ha⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd (instanceCells I R present vid) k f g gs go hf hg hgstep
  refine ⟨fs.1,fs.2,gs,go,_,gpost++fpost++bpost++hashRows I R present vid++ashRows I R present vid,
    hprefix,hgstep,?_,ha,?_⟩
  · rw [hgl,hfl,hbl]
    simp [headerRows]
  · rw [hr,hbr,hfr,hgr]
    simp only [List.append_assoc]

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃rows cmps before after a suffix,
      forIn (List.range g) (rows,cmps,0,0,0,0)
        (fun j st=>step I R present gb fwd (instanceCells I R present vid) k f j st)=.ok before ∧
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
    ∃rows cmps before after,
      forIn (List.range g) (rows,cmps,0,0,0,0)
        (fun j st=>step I R present gb fwd (instanceCells I R present vid) k f j st)=.ok before ∧
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧
      after.1=before.1.push out.rows[5+24*k+8*f+g]! := by
  obtain ⟨rows,cmps,before,after,a,suffix,hprefix,he,hl,ha,ho⟩ := generated I R present vid gb fwd out h k f g hk hf hg
  have hc : out.rows[5+24*k+8*f+g]! = a := by
    rw [←Array.getElem!_toList,ho,ha,Array.toList_push,←hl]
    simpa only [List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
      Array.length_toList,Nat.add_zero] using
      ProcCodecSuffixCells.appended_map before.1.toList suffix (fun _=>a) 1 0 (by decide)
  exact ⟨rows,cmps,before,after,hprefix,he,hl,by rw [hc]; exact ha⟩
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPrefix
