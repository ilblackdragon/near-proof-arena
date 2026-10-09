import ZkFormal.NearV3.Candidates.ProcCodecExecutionAdjacentPosition
import ZkFormal.NearV3.Candidates.ProcCodecExecutionPosition
import ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAdjacent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<7) :
    ∃before mid after a b suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield mid) ∧
      step I R present gb fwd (instanceCells I R present vid) k f (g+1) mid=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧ mid.1=before.1.push a ∧ after.1=mid.1.push b ∧
      out.rows.toList=after.1.toList++suffix := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  obtain ⟨bs,bo,_,bpost,hb,hbl,_,_,hbr⟩ := ProcCodecExecutionPosition.block I R present vid gb fwd _ mid hm k hk
  obtain ⟨fs,fo,_,fpost,hfstep,hfl,_,_,hfr⟩ := ProcCodecExecutionPosition.field I R present vid gb fwd k bs bo hb f hf
  obtain ⟨gs,gm,go,gpost,hga,hgb,hgl,hgr⟩ := ProcCodecExecutionAdjacentPosition.field_pair I R present vid gb fwd k f hf fs fo hfstep g hg
  obtain ⟨tail,ht,ha⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd (instanceCells I R present vid) k f g gs gm hf (by omega) hga
  obtain ⟨tail',ht',hb'⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd (instanceCells I R present vid) k f (g+1) gm go hf (by omega) hgb
  refine ⟨gs,gm,go,_,_,gpost++fpost++bpost++hashRows I R present vid++ashRows I R present vid,
    hga,hgb,?_,ha,hb',?_⟩
  · rw [hgl,hfl,hbl]
    simp [headerRows]
  · rw [hr,hbr,hfr,hgr]
    simp only [List.append_assoc]

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<7) :
    ∃before mid after a b suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield mid) ∧
      step I R present gb fwd (instanceCells I R present vid) k f (g+1) mid=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧ mid.1=before.1.push a ∧ after.1=mid.1.push b ∧
      out.rows.toList=after.1.toList++suffix := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core I R present vid gb fwd o hc k f g hk hf hg

theorem pair_cells (rows before : Array (Array Nat)) (a b : Array Nat) (suffix : List (Array Nat))
    (h : rows.toList=before.toList++[a,b]++suffix) :
    rows[before.size]! =a ∧ rows[before.size+1]! =b := by
  have h0 := ProcCodecSuffixCells.appended_map before.toList suffix (fun j=>if j=0 then a else b) 2 0 (by decide)
  have h1 := ProcCodecSuffixCells.appended_map before.toList suffix (fun j=>if j=0 then a else b) 2 1 (by decide)
  simp only [List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
    List.map_append,List.singleton_append,Array.length_toList,Nat.add_zero,ite_true,
    show (1:Nat)≠0 by decide,ite_false] at h0 h1
  constructor
  · rw [←Array.getElem!_toList,h]; exact h0
  · rw [←Array.getElem!_toList,h]; exact h1

theorem cells (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<7) :
    ∃before mid after,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield mid) ∧
      step I R present gb fwd (instanceCells I R present vid) k f (g+1) mid=.ok (.yield after) ∧
      before.1.size=5+24*k+8*f+g ∧
      mid.1=before.1.push out.rows[5+24*k+8*f+g]! ∧
      after.1=mid.1.push out.rows[5+24*k+8*f+g+1]! := by
  obtain ⟨before,mid,after,a,b,suffix,he,hf',hl,ha,hb,ho⟩ := generated I R present vid gb fwd out h k f g hk hf hg
  have hr : out.rows.toList=before.1.toList++[a,b]++suffix := by
    rw [ho,hb,ha,Array.toList_push,Array.toList_push]
    simp only [List.append_assoc,List.singleton_append]
  obtain ⟨hca,hcb⟩ := pair_cells out.rows before.1 a b suffix hr
  rw [hl] at hca hcb
  exact ⟨before,mid,after,he,hf',hl,by rw [hca]; exact ha,by rw [hcb]; exact hb⟩
theorem property (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<7)
    (P : Array Nat→Array Nat→Prop)
    (hp : ∀before mid after,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield mid)→
      step I R present gb fwd (instanceCells I R present vid) k f (g+1) mid=.ok (.yield after)→
      ∃a b,mid.1=before.1.push a ∧ after.1=mid.1.push b ∧ P a b) :
    P out.rows[5+24*k+8*f+g]! out.rows[5+24*k+8*f+g+1]! := by
  obtain ⟨before,mid,after,he,hf',_,ha,hb⟩ := cells I R present vid gb fwd out h k f g hk hf hg
  obtain ⟨a,b,ha',hb',hp⟩ := hp before mid after he hf'
  have hca : a=out.rows[5+24*k+8*f+g]! := Array.push_inj_right.mp (ha'.symm.trans ha)
  have hcb : b=out.rows[5+24*k+8*f+g+1]! := Array.push_inj_right.mp (hb'.symm.trans hb)
  simpa only [hca,hcb] using hp
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAdjacent
