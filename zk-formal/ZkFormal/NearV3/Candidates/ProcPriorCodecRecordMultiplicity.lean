import ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordMultiplicity
open ZkFormal.Air ZkFormal.Algebra Lean.Grind
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSideMultiplicity

theorem bit_mul {a b : Fp} (ha : Bit a) (hb : Bit b) : Bit (a*b) := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> unfold Bit <;> decide +kernel

/-- Boolean obligations for all18 corrected interactions on a record row,
including both product gates introduced by the prior-state repair. -/
theorem record_mult (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz : ∀c∈[kH,kZ,kA,kF,dgg],cur c=0) (hR : cur kR=1)
    (hSR : Bit (cur fS+cur fR))
    (hb : ∀c∈[fwg,rend,cg,rs,nzb,fA,e2],Bit (cur c)) :
    ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env cur nxt first last trans)) := by
  have hH:=hz kH (by simp)
  have hZ:=hz kZ (by simp)
  have hA:=hz kA (by simp)
  have hF:=hz kF (by simp)
  have hD:=hz dgg (by simp)
  have hFw:=hb fwg (by simp)
  have hEnd:=hb rend (by simp)
  have hCg:=hb cg (by simp)
  have hRs:=hb rs (by simp)
  have hPub:=bit_mul (hb rs (by simp)) (hb nzb (by simp))
  have hPrior:=bit_mul (hb fA (by simp)) (hb e2 (by simp))
  simp only [ProcPriorCodecActual.interactions,ProcPriorCodecParameter.table,
    ZkFormal.NearV3.Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    List.set,List.cons_append,List.nil_append,List.forall_mem_cons,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    ZkFormal.NearV3.Render.UpsRelay.relay]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,encG,hH,hZ,hA,hF,hD,hR,
    Bit]
  refine ⟨by decide +kernel,by decide +kernel,hSR,?_,hEnd,hRs,hPub,hPrior,hCg⟩
  rcases hFw with h|h <;> rw [h] <;> decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordMultiplicity
