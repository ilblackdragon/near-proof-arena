import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedExecution
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRows
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSideMultiplicity

def Good (P : Array Nat→Prop) (rows : Array (Array Nat)) : Prop :=
  ∀a∈rows.toList,P a

def Records (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (P : Array Nat→Prop) : Prop :=
  ∀k f g, k<R.n*R.n→f<3→g<8→∀s out,
    ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s=.ok (.yield out)→
    ∃a,out.1=s.1.push a ∧ P a

theorem byte_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f g : Nat)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P)
    (s : ProcPriorCodecRecordStep.State) (hs : Good P s.1)
    (v : ForInStep ProcPriorCodecRecordStep.State)
    (h : ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s=.ok v) :
    ExceptLoop.StepInv (fun s : ProcPriorCodecRecordStep.State=>Good P s.1) v := by
  obtain ⟨out,_,rfl,_,_,_⟩ := byte_step_quiet I R present vid gb fwd k f g hf hg s v h
  obtain ⟨a,ha,hbits⟩ := hp k f g hk hf hg s out h
  change Good P out.1
  rw [ha]
  intro b hb
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hb
  rcases hb with hb|rfl
  · exact hs b hb
  · exact hbits

theorem field_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hk : k<R.n*R.n) (hf : f<3)
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P)
    (s : RecordState) (hs : Good P s.1) (v : ForInStep RecordState)
    (h : fieldStep I R present vid gb fwd k f s=.ok v) :
    ExceptLoop.StepInv (fun s : RecordState=>Good P s.1) v := by
  unfold fieldStep at h
  cases he : forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst v
    exact ExceptLoop.invariant (List.range 8) _
      (fun s : ProcPriorCodecRecordStep.State=>Good P s.1)
      (fun g hg s hs v h=>byte_good I R present vid gb fwd k f g hk hf (List.mem_range.mp hg) P hp s hs v h)
      _ st hs he

theorem block_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (hk : k<R.n*R.n)
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P)
    (s : RecordState) (hs : Good P s.1) (v : ForInStep RecordState)
    (h : blockStep I R present vid gb fwd k s=.ok v) :
    ExceptLoop.StepInv (fun s : RecordState=>Good P s.1) v := by
  unfold blockStep at h
  cases he : forIn (List.range 3) s (fieldStep I R present vid gb fwd k) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst v
    exact ExceptLoop.invariant (List.range 3) _
      (fun s : RecordState=>Good P s.1)
      (fun f hf s hs v h=>field_good I R present vid gb fwd k f hk (List.mem_range.mp hf) P hp s hs v h)
      s st hs he

theorem blocks_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat))
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P)
    (s out : RecordState) (hs : Good P s.1)
    (h : forIn (List.range (R.n*R.n)) s (blockStep I R present vid gb fwd)=.ok out) :
    Good P out.1 :=
  ExceptLoop.invariant (List.range (R.n*R.n)) _
    (fun s : RecordState=>Good P s.1)
    (fun k hk s hs v h=>block_good I R present vid gb fwd k (List.mem_range.mp hk) P hp s hs v h)
    s out hs h
theorem core_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P) (hhdr : ∀a∈headerRows I R present vid,P a)
    (hhash : ∀a∈hashRows I R present vid,P a)
    (hash : ∀a∈ashRows I R present vid,P a) : Good P out.rows := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  have hh : Good P (headerRows I R present vid).toArray := by
    simpa only [Good,List.toList_toArray] using hhdr
  have hb := blocks_good I R present vid gb fwd P hp _ mid hh hm
  intro a ha
  rw [hr] at ha
  simp only [List.mem_append] at ha
  rcases ha with (ha|ha)|ha
  · exact hb a ha
  · exact hhash a ha
  · exact hash a ha

/-- Lift any proved row property through the exact successful public generator. -/
theorem generated_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (P : Array Nat→Prop) (hp : Records I R present vid gb fwd P) (hhdr : ∀a∈headerRows I R present vid,P a)
    (hhash : ∀a∈hashRows I R present vid,P a)
    (hash : ∀a∈ashRows I R present vid,P a) : Good P out.rows := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_good I R present vid gb fwd o hc P hp hhdr hhash hash

end ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
