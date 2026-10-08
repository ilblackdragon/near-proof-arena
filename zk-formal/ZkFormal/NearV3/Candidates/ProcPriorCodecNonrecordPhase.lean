import ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecord
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecordPhase
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched Codec

/-- In hash/ash/padding and nonfinal header phases, digest overlay counters
may be arbitrary. The zero header-end flag makes both next counters irrelevant. -/
theorem inactive_header (cur nxt : Nat→Fp) (first last trans : Fp)
    (hrs:cur rs=0) (hkR:cur kR=0) (hrend:cur rend=0)
    (hfA:cur fA=0) (hfS:cur fS=0) (hh:cur ehp=0) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [ProcPriorCodecActual.additions,isZ,List.take,List.forall_mem_append,
    List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,and_true]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hrs,hkR,hrend,hfA,hfS,hh,mul3]
  grind

theorem additions (cur nxt : Nat→Fp) (first last trans : Fp)
    (hrs:cur rs=0) (hkR:cur kR=0) (hrend:cur rend=0)
    (hfA:cur fA=0) (hfS:cur fS=0)
    (hh:cur ehp=0 ∨ (nxt srcC=0 ∧ nxt useC=0)) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  rcases hh with hh|⟨hs,hu⟩
  · exact inactive_header cur nxt first last trans hrs hkR hrend hfA hfS hh
  · exact ProcPriorCodecNonrecord.additions cur nxt first last trans hrs hkR hrend hfA hfS hs hu

end ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecordPhase
