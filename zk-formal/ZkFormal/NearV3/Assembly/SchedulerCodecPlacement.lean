import ZkFormal.NearV3.Assembly.SchedulerCodecLayout
import ZkFormal.NearV3.Assembly.SchedulerCodecRecordLoops

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Sched Sched.Gen Sched.Codec Candidates

def hashRows (I : Input) (R : Run) (present : Bool) (vidV : Nat) : List (Array Nat) :=
  let inst:=ProcPriorCodecNativeHash.instanceCells I R present vidV
  let hpre:=if present then I.prev.sanityHash.map UInt8.toNat else List.replicate 32 0
  let digest:=(NearSpec.sha256 ((hpre++I.ash.map UInt8.toNat).map UInt8.ofNat)).map UInt8.toNat
  (List.range 32).map (ProcPriorCodecAssignments.hashRow inst digest hpre present (5+24*(R.n*R.n)))
def ashRows (I : Input) (R : Run) (present : Bool) (vidV : Nat) : List (Array Nat) :=
  (List.range 32).map (ProcPriorCodecAssignments.ashRow
    (ProcPriorCodecNativeHash.instanceCells I R present vidV) I (5+24*(R.n*R.n)))

def headerRows (I : Input) (R : Run) (present : Bool) (vidV : Nat) : List (Array Nat) :=
  let N:=R.n*R.n
  let hdr:=[0,N%256,N/256%256,0,0]
  let params:=hdr++bytesLE I.p.base 3++bytesLE (I.p.maxShardBandwidth/R.n) 3
  (List.range 5).map (ProcPriorCodecAssignments.headerRow
    (ProcPriorCodecNativeHash.instanceCells I R present vidV) params hdr present)

private theorem headers_quiet (I : Input) (R : Run) (present : Bool) (vidV : Nat) :
    Quiet (headerRows I R present vidV) := by
  intro row hm
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  exact header_digest_gate I R present vidV _ _ p

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h : x >>= f = .ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem core_suffix (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vidV gbA fwd=.ok out) :
    ∃lead,out.rows.toList=lead++hashRows I R present vidV++ashRows I R present vidV := by
  unfold coreLayout at h
  dsimp only at h
  simp only [pure,Except.pure] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  obtain ⟨v,hloop,h⟩:=bind_ok h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  cases h
  refine ⟨v.1.toList,?_⟩
  simp [hashRows,ashRows,ProcPriorCodecNativeHash.instanceCells]

/-- Exact successful imperative layout: a quiet prefix of5+24*n² rows,
followed by32 hash rows and32 action-hash rows. No local AIR premise. -/
theorem core_placement (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vidV gbA fwd=.ok out) :
    ∃lead,Quiet lead ∧ lead.length=5+24*(R.n*R.n) ∧
      out.rows.toList=lead++hashRows I R present vidV++ashRows I R present vidV := by
  unfold coreLayout at h
  dsimp only at h
  simp only [pure,Except.pure] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  obtain ⟨v,hloop,h⟩:=bind_ok h
  change forIn (List.range (R.n*R.n)) ((headerRows I R present vidV).toArray,[])
    (blockStep I R present vidV gbA fwd)=.ok v at hloop
  obtain ⟨added,hr,hcount,hquiet⟩:=record_loop_quiet I R present vidV gbA fwd _ _ hloop
  have hq:Quiet v.1.toList:=by
    rw [hr]
    intro row hm
    rcases List.mem_append.mp hm with hm|hm
    · exact headers_quiet I R present vidV row (by simpa using hm)
    · exact hquiet row hm
  have hl:v.1.toList.length=5+24*(R.n*R.n):=by
    rw [hr,List.length_append,hcount]
    simp [headerRows]
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  cases h
  refine ⟨v.1.toList,hq,hl,?_⟩
  simp [hashRows,ashRows,ProcPriorCodecNativeHash.instanceCells]

/-- Public corrected generator inherits the exact physical layout; metadata
installation cannot alter the rows. -/
theorem generated_placement (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out) :
    ∃lead,Quiet lead ∧ lead.length=5+24*(R.n*R.n) ∧
      out.rows.toList=lead++hashRows I R present vidV++ashRows I R present vidV := by
  rw [←coreLayout_eq] at h
  cases hc:coreLayout I R present vidV gbA fwd with
  | error e=>simp [hc,Except.map] at h
  | ok o=>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_placement I R present vidV gbA fwd o hc

end ZkFormal.NearV3.Assembly.CodecDigest
