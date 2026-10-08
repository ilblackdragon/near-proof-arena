import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched Codec

/-- Header/hash/padding rows have no record phase. The header's final row
initializes both grid counters to zero in the following first record. Unlike
the retired pre-byte test, this lemma permits arbitrary overlay digest bytes. -/
theorem additions (cur nxt : Nat→Fp) (first last trans : Fp)
    (hrs:cur rs=0) (hkR:cur kR=0) (hrend:cur rend=0)
    (hfA:cur fA=0) (hfS:cur fS=0) (hs:nxt srcC=0) (hu:nxt useC=0) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [ProcPriorCodecActual.additions,isZ,List.take,List.forall_mem_append,
    List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map,and_true]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hrs,hkR,hrend,hfA,hfS,hs,hu,mul3]
  grind

end ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecord
