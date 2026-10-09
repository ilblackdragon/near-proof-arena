import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryBit
import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainStep
namespace ZkFormal.NearV3.Candidates.ProcCodecCarryPosition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecExecutionTrace ProcCodecExecutionIndex
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem step_bound (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f g : Nat) (s out : State) (hf:f<3) (hg:g<8)
    (hs:s.2.2.2.2.2≤1) (h:step I R present gb fwd inst k f g s=.ok (.yield out)) :
    out.2.2.2.2.2≤1 := by
  by_cases hf2:f<2
  · rw [ProcPriorCodecPlainStep.step_eq _ _ _ _ _ _ _ _ _ _ hf2] at h
    simp only [Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    exact hs
  · have he:f=2 := by omega
    subst f
    rw [ProcPriorCodecCarryTotal.byte_carry I R present gb fwd inst k g s out hg h]
    split
    · unfold ProcPriorCodecCarryTotal.bit
      split <;> split <;> omega
    · exact hs

theorem steps_bound (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f : Nat) (hf:f<3)
    (gs : List Nat) (s out : State) (hg:∀g∈gs,g<8)
    (hs:s.2.2.2.2.2≤1)
    (h:Steps (fun g st=>step I R present gb fwd inst k f g st) gs s out) :
    out.2.2.2.2.2≤1 := by
  induction h with
  | nil => exact hs
  | @cons g gs s mid out hh ht ih =>
    apply ih (fun g hg0=>hg g (by simp [hg0]))
    exact step_bound I R present gb fwd inst k f g s mid hf (hg g (by simp)) hs hh

theorem byte (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hf:f<3)
    (s out : RecordState) (h:fieldStep I R present vid gb fwd k f s=.ok (.yield out))
    (g : Nat) (hg:g<8) :
    ∃before after a suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.2.2.2.2.2≤1 ∧ before.1.size=s.1.size+g ∧ after.1=before.1.push a ∧
      out.1.toList=after.1.toList++suffix := by
  unfold fieldStep at h
  cases he:forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun g st=>step I R present gb fwd (instanceCells I R present vid) k f g st) with
  | error e=>simp only [he,bind,Except.bind] at h; cases h
  | ok st=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    have hs:=field_execution I R present vid gb fwd k f hf _ st he
    obtain ⟨before,after,hpre,hstep,hpost⟩:=at_index (List.range 8) _ st hs g (by simpa using hg)
    simp only [List.getElem_range] at hstep
    have hcb:=steps_bound I R present gb fwd (instanceCells I R present vid) k f hf _ _ before
      (fun x hx=>List.mem_range.mp (List.mem_of_mem_take hx)) (by change 0≤1; decide) hpre
    have hwrite : ∀x∈List.range 8,∀a b,step I R present gb fwd (instanceCells I R present vid) k f x a=.ok (.yield b)→
        ∃added,b.1.toList=a.1.toList++added ∧ added.length=1 := by
      intro x hx a b hh
      obtain ⟨result,added,hy,hr,hl,_⟩:=byte_step_quiet I R present vid gb fwd k f x hf (List.mem_range.mp hx) a (.yield b) hh
      cases hy
      exact ⟨added,hr,hl⟩
    obtain ⟨pre,hpr,hpl⟩:=span (fun s:State=>s.1.toList) 1 _ _ before hpre
      (fun a ha=>hwrite a (List.mem_of_mem_take ha))
    obtain ⟨post,hpo,_⟩:=span (fun s:State=>s.1.toList) 1 _ after st hpost
      (fun a ha=>hwrite a (List.mem_of_mem_drop ha))
    obtain ⟨tail,ht,ha⟩:=ProcPriorCodecStepRows.successful_row I R present gb fwd (instanceCells I R present vid) k f g before after hf hg hstep
    refine ⟨before,after,_,post,hstep,hcb,?_,ha,hpo⟩
    have hlen:=congrArg List.length hpr
    simp only [Array.length_toList,List.length_append] at hlen
    rw [hpl,List.length_take,List.length_range,Nat.min_eq_left (by omega),Nat.one_mul] at hlen
    exact hlen

theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∃before after a suffix,
      step I R present gb fwd (instanceCells I R present vid) k f g before=.ok (.yield after) ∧
      before.2.2.2.2.2≤1 ∧
      before.1.size=5+24*k+8*f+g ∧ after.1=before.1.push a ∧
      out.rows.toList=after.1.toList++suffix := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  obtain ⟨bs,bo,_,bpost,hb,hbl,_,_,hbr⟩ := ProcCodecExecutionPosition.block I R present vid gb fwd _ mid hm k hk
  obtain ⟨fs,fo,_,fpost,hfstep,hfl,_,_,hfr⟩ := ProcCodecExecutionPosition.field I R present vid gb fwd k bs bo hb f hf
  obtain ⟨gs,go,a,gpost,hgstep,hcb,hgl,ha,hgr⟩ := byte I R present vid gb fwd k f hf fs fo hfstep g hg
  refine ⟨gs,go,_,gpost++fpost++bpost++hashRows I R present vid++ashRows I R present vid,
    hgstep,hcb,?_,ha,?_⟩
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
      before.2.2.2.2.2≤1 ∧
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
      before.2.2.2.2.2≤1 ∧
      before.1.size=5+24*k+8*f+g ∧
      after.1=before.1.push out.rows[5+24*k+8*f+g]! := by
  obtain ⟨before,after,a,suffix,he,hcb,hl,ha,ho⟩ := generated I R present vid gb fwd out h k f g hk hf hg
  have hc : out.rows[5+24*k+8*f+g]! = a := by
    rw [←Array.getElem!_toList,ho,ha,Array.toList_push,←hl]
    simpa only [List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
      Array.length_toList,Nat.add_zero] using
      ProcCodecSuffixCells.appended_map before.1.toList suffix (fun _=>a) 1 0 (by decide)
  exact ⟨before,after,he,hcb,hl,by rw [hc]; exact ha⟩
end ZkFormal.NearV3.Candidates.ProcCodecCarryPosition
