import ZkFormal.NearV3.Candidates.UniqueSourceSoundShadow
import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractChainTraffic
namespace ZkFormal.NearV3.Candidates.UniqueSourceSoundSemantic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates
open UniqueSourceSoundShadow

theorem registers (tr : Trace Fp) (tt r : Nat) :
    SrcpProof.regsF (shadow tr) tt r=SrcpProof.regsF tr tt r := by
  apply List.map_congr_left
  intro i hi
  have hh:=List.mem_range.mp hi
  have hx : SrcpV3.reg i≠SrcpV3.sz := by simp only [SrcpV3.reg,SrcpV3.sz];omega
  simp only [shadow,hx,ite_false]

theorem row_traffic (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (b : Nat) (sd : Bool) (hb : b≠B_SIZE) :
    rowTraffic DedupTable.interactions (shadow tr) tt r pub b sd=
      rowTraffic DedupTable.interactions tr tt r pub b sd := by
  rw [DedupRender.candidate_rowT,DedupRender.candidate_rowT,registers]
  simp only [hb,false_and,ite_false]
  simp [shadow,SrcpV3.sz,SrcpV3.sg,SrcpV3.q,SrcpV3.wn,SrcpV3.pw,SrcpV3.b,
    SrcpV3.gD,SrcpV3.cId,SrcpV3.cLen,SrcpV3.rt,SrcpV3.j,SrcpV3.L,SrcpV3.dup,DedupTable.repeated]
  rfl

theorem messages (tr : Trace Fp) (tt : Nat) (pub : List Fp) (b : Nat) (sd : Bool) (hb : b≠B_SIZE) :
    (List.range ((shadow tr).height tt)).flatMap (fun r=>rowTraffic DedupTable.interactions (shadow tr) tt r pub b sd)=
      (List.range (tr.height tt)).flatMap (fun r=>rowTraffic DedupTable.interactions tr tt r pub b sd) := by
  simp only [row_traffic tr tt _ pub b sd hb]
  rfl

/-- Every accepting corrected logical table yields a nonempty source block
chain whose non-SIZE traffic is exactly the submitted trace's traffic. -/
theorem extracted {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table 24) tr tt pub) :
    ∃bs stop,DedupProof.BlockChain (shadow tr) tt 0 bs stop ∧ bs≠[] ∧
      DedupRender.R bs≤tr.height tt ∧
      ∀b,b≠B_SIZE→∀sd,
        (List.range (tr.height tt)).flatMap (fun r=>rowTraffic DedupTable.interactions tr tt r pub b sd)=
          (DedupProof.chainMsgs (shadow tr) tt 0 bs b sd).map Msg.toFp := by
  have hl:=old_local h
  obtain ⟨bs,stop,hbs⟩:=DedupProof.extract_blocks hl
  refine ⟨bs,stop,hbs,hbs.nonempty,?_,?_⟩
  · have hh:=hbs.rows
    have hb:=hbs.bound
    change 0<stop ∧ stop≤tr.height tt at hb
    omega
  · intro b hb sd
    rw [←messages tr tt pub b sd hb]
    exact hbs.full_traffic hl b hb sd
end ZkFormal.NearV3.Candidates.UniqueSourceSoundSemantic
