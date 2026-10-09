import ZkFormal.NearV3.Candidates.ProcCodecPublicIdInventory
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
import ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
import ZkFormal.NearV3.Sched.Link.SoundPrep
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
import ZkFormal.NearV3.Candidates.ProcPreparedSequence
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdPacked
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPriorCodecEndArithmetic

theorem limbs (id : Nat) (h : id<2^64) :
    id%256+(256*(id/256%256)+65536*(id/65536%256))=ProcPriorIdLimbs.lo id ∧
    id/16777216%256+(256*(id/4294967296%256)+65536*(id/1099511627776%256))=ProcPriorIdLimbs.mid id ∧
    id/281474976710656%256+256*(id/72057594037927936%256)=ProcPriorIdLimbs.hi id := by
  unfold ProcPriorIdLimbs.lo ProcPriorIdLimbs.mid ProcPriorIdLimbs.hi
  omega

/-- Honest packed byte registers are precisely the ID table's canonical
24/24/16-bit limbs, including repeated layout IDs. -/
theorem message (tau sender id : Nat) (h : id<2^64) :
    ProcCodecPublicIdRecord.idMessage tau sender id=
      [Fp.ofNat tau,Fp.ofNat sender,Fp.ofNat (ProcPriorIdLimbs.lo id),
        Fp.ofNat (ProcPriorIdLimbs.mid id),Fp.ofNat (ProcPriorIdLimbs.hi id)] := by
  have hl:=limbs id h
  simp only [ProcCodecPublicIdRecord.idMessage,ProcCodecPublicIdTraffic.message]
  simp [bytesLE,List.getD_eq_getElem?_getD]
  have h256 : (256:Fp)=Fp.ofNat 256 := rfl
  have h65536 : (65536:Fp)=Fp.ofNat 65536 := rfl
  rw [h256,h65536,←cast_mul,←cast_mul,←cast_add,←cast_add,
    ←cast_mul,←cast_mul,←cast_add,←cast_add,←cast_mul,←cast_add,hl.1,hl.2.1,hl.2.2]
  exact ⟨rfl,rfl,rfl⟩

/-- The actual prepared scheduler run emits every current-layout sender ID
once, packed exactly as expected by prior-ID lookup. This is honest traffic
completeness, not an arbitrary-local authentication assertion. -/
theorem prepared_count {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint=.ok p) (sp : NearSpecV3.Scheduler.SchedPub)
    (hsp : sp∈p.sched) (prev : NearSpec.Bandwidth.State) (tauV : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (present : Bool) (vidV : Nat) (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R present vidV gb fwd=.ok out)
    (t : Nat) (pub msg : List Fp) :
    ZkFormal.Air.tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub 70 true msg=
      ((List.range sp.ids.length).map (fun s=>[Fp.ofNat tauV,Fp.ofNat s,
        Fp.ofNat (ProcPriorIdLimbs.lo (sp.ids.getD s 0)),Fp.ofNat (ProcPriorIdLimbs.mid (sp.ids.getD s 0)),
        Fp.ofNat (ProcPriorIdLimbs.hi (sp.ids.getD s 0))])).count msg := by
  have hf:=ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tauV R hr
  have hn : R.n=sp.ids.length := hf.2.1
  have hs:=prepD0_sched hp sp hsp
  rw [ProcCodecPublicIdInventory.count _ _ _ _ _ _ _ h (by have hh:=hs.n1; omega) (by have hh:=hs.n64; omega),hn,hf.1]
  apply congrArg (fun xs : List (List Fp)=>xs.count msg)
  apply List.map_congr_left
  intro s hmem
  have hi:=List.mem_range.mp hmem
  apply message
  have hm : sp.ids.getD s 0∈sp.ids := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact List.getElem_mem hi
  exact prepD0_ids64 hp sp hsp _ hm
end ZkFormal.NearV3.Candidates.ProcCodecPublicIdPacked
