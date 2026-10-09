import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedExecution
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRows
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSideMultiplicity

def Good (nxt : Nat→Fp) (first last trans : Fp) (rows : Array (Array Nat)) : Prop :=
  ∀a∈rows.toList,∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,
    Bit (e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans))

theorem byte_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f g : Nat)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (nxt : Nat→Fp) (first last trans : Fp)
    (s : ProcPriorCodecRecordStep.State) (hs : Good nxt first last trans s.1)
    (v : ForInStep ProcPriorCodecRecordStep.State)
    (h : ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s=.ok v) :
    ExceptLoop.StepInv (fun s : ProcPriorCodecRecordStep.State=>Good nxt first last trans s.1) v := by
  obtain ⟨out,_,rfl,_,_,_⟩ := byte_step_quiet I R present vid gb fwd k f g hf hg s v h
  obtain ⟨a,ha,hbits⟩ := ProcPriorCodecNativeMultiplicity.actual I R present gb fwd vid k f g s out hk hf hg h nxt first last trans
  change Good nxt first last trans out.1
  rw [ha]
  intro b hb
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hb
  rcases hb with hb|rfl
  · exact hs b hb
  · exact hbits

theorem field_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hk : k<R.n*R.n) (hf : f<3)
    (nxt : Nat→Fp) (first last trans : Fp)
    (s : RecordState) (hs : Good nxt first last trans s.1) (v : ForInStep RecordState)
    (h : fieldStep I R present vid gb fwd k f s=.ok v) :
    ExceptLoop.StepInv (fun s : RecordState=>Good nxt first last trans s.1) v := by
  unfold fieldStep at h
  cases he : forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst v
    exact ExceptLoop.invariant (List.range 8) _
      (fun s : ProcPriorCodecRecordStep.State=>Good nxt first last trans s.1)
      (fun g hg s hs v h=>byte_good I R present vid gb fwd k f g hk hf (List.mem_range.mp hg) nxt first last trans s hs v h)
      _ st hs he

theorem block_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (hk : k<R.n*R.n)
    (nxt : Nat→Fp) (first last trans : Fp)
    (s : RecordState) (hs : Good nxt first last trans s.1) (v : ForInStep RecordState)
    (h : blockStep I R present vid gb fwd k s=.ok v) :
    ExceptLoop.StepInv (fun s : RecordState=>Good nxt first last trans s.1) v := by
  unfold blockStep at h
  cases he : forIn (List.range 3) s (fieldStep I R present vid gb fwd k) with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok st =>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst v
    exact ExceptLoop.invariant (List.range 3) _
      (fun s : RecordState=>Good nxt first last trans s.1)
      (fun f hf s hs v h=>field_good I R present vid gb fwd k f hk (List.mem_range.mp hf) nxt first last trans s hs v h)
      s st hs he

theorem blocks_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat))
    (nxt : Nat→Fp) (first last trans : Fp)
    (s out : RecordState) (hs : Good nxt first last trans s.1)
    (h : forIn (List.range (R.n*R.n)) s (blockStep I R present vid gb fwd)=.ok out) :
    Good nxt first last trans out.1 :=
  ExceptLoop.invariant (List.range (R.n*R.n)) _
    (fun s : RecordState=>Good nxt first last trans s.1)
    (fun k hk s hs v h=>block_good I R present vid gb fwd k (List.mem_range.mp hk) nxt first last trans s hs v h)
    s out hs h
theorem core_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out)
    (nxt : Nat→Fp) (first last trans : Fp) : Good nxt first last trans out.rows := by
  obtain ⟨mid,hm,hr⟩ := ProcCodecGeneratedExecution.core_execution I R present vid gb fwd out h
  have hh : Good nxt first last trans (headerRows I R present vid).toArray := by
    intro a ha
    simp only [List.toList_toArray,headerRows] at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact header_mult I R present vid _ _ j nxt first last trans
  have hb := blocks_good I R present vid gb fwd nxt first last trans _ mid hh hm
  intro a ha
  rw [hr] at ha
  simp only [List.mem_append] at ha
  rcases ha with (ha|ha)|ha
  · exact hb a ha
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact hash_mult I R present vid _ _ _ j nxt first last trans
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact ash_mult I R present vid _ j nxt first last trans

/-- All multiplicity-bit obligations follow from public corrected generator
success, across header, all record loops, hash and action-hash rows. -/
theorem generated_good (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (nxt : Nat→Fp) (first last trans : Fp) : Good nxt first last trans out.rows := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_good I R present vid gb fwd o hc nxt first last trans

/-- Every actual physical multiplicity bit of a successfully generated codec
is Boolean, including padding and the wrap row. -/
theorem physical_bits (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hne : 0<out.rows.size) (hcap : out.rows.size<2^22) (t r : Nat)
    (hr : r<2^22) (pub : List Fp) :
    ∀i∈ProcPriorCodecActual.table.interactions,∀e∈i.mult,
      e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 ∨
      e.eval (SchedHeight.trace out.rows codecPad) t r pub=1 := by
  by_cases ha : r<out.rows.size
  · intro i hi e he
    have hp : e.pubBound=0 :=
      (by decide +kernel : ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,e.pubBound=0) i hi e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    have hb := generated_good I R present vid gb fwd out h
      (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
      (if r=0 then 1 else 0) 0 1
    exact hb out.rows[r]! (by simp [ha]) i hi e he
  · exact (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).2
theorem capacity (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn : R.n≤64) :
    0<out.rows.size ∧ out.rows.size<2^22 := by
  rw [generated_length I R present vid gb fwd out h]
  have hm := Nat.mul_le_mul hn hn
  omega

/-- For an actually generated64-shard codec block, only the active constraints
remain: all bit, height, capacity and padding obligations are constructed. -/
theorem table_of_constraints (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn : R.n≤64)
    (t : Nat) (pub : List Fp)
    (hc : ∀r,r<out.rows.size→∀e∈ProcPriorCodecActual.constraints,
      e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out.rows codecPad) t pub := by
  obtain ⟨hne,hcap⟩ := capacity I R present vid gb fwd out h hn
  apply ProcCodecPhysicalRows.table_of_rows out.rows hne hcap t pub hc
  intro r hr i hi e he
  have hb := generated_good I R present vid gb fwd out h
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1
  exact hb out.rows[r]! (by simp [hr]) i hi e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
