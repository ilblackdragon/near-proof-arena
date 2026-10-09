import ZkFormal.NearV3.Candidates.ProcCodecGeneratedSideAdditions
namespace ZkFormal.NearV3.Candidates.ProcCodecPhysicalAdditionGroups
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

theorem active_of_records (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:0<R.n)
    (es : List Expr) (hsub:∀e∈es,e∈ProcPriorCodecActual.additions)
    (hp:∀k f g,k<R.n*R.n→f<3→g<8→∀e∈es,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0)
    (r : Nat) (hr:r<out.rows.size) :
    ∀e∈es,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  by_cases hh:r<5
  · intro e he
    exact ProcCodecGeneratedSideAdditions.header I R present vidV gb fwd out h hn r hh e (hsub e he)
  · by_cases hrec:r<5+24*(R.n*R.n)
    · have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
      rw [he]
      exact hp _ _ _ (by omega) (by omega) (by omega)
    · intro e he
      exact ProcCodecGeneratedSideAdditions.suffix I R present vidV gb fwd out h r hr (by omega) e (hsub e he)
end ZkFormal.NearV3.Candidates.ProcCodecPhysicalAdditionGroups
