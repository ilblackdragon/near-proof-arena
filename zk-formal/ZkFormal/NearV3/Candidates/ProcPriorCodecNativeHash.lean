import ZkFormal.NearV3.Candidates.ProcPriorCodecHashReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecNonrecordPhase
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments

/-- Exactly the instanceCells assignments used by the corrected native core. -/
def instanceCells (I : Input) (R : Run) (present : Bool) (vidV : Nat) : List (Nat×Nat) :=
  [(act,1),(tau,R.tau),(pres,b2n present),(vid,vidV),(nn,R.n),(NN,R.n*R.n),
   (base,I.p.base),(fair,I.p.maxShardBandwidth/R.n),(itz,finv R.tau),(zt,if R.tau=0 then 1 else 0)]

theorem instance_columns (I : Input) (R : Run) (present : Bool) (vidV : Nat) :
    (instanceCells I R present vidV).map Prod.fst=[act,tau,pres,vid,nn,NN,base,fair,itz,zt] := rfl

theorem instance_avoids (I : Input) (R : Run) (present : Bool) (vidV c : Nat)
    (hc:c∈[kR,rs,rend,fS,fA,ehp]) :
    ∀a∈instanceCells I R present vidV,a.1≠c := by
  have hd : ∀c∈[kR,rs,rend,fS,fA,ehp],c∉[act,tau,pres,vid,nn,NN,base,fair,itz,zt] := by
    decide +kernel
  intro a ha he
  have hm:=List.mem_map_of_mem (f:=Prod.fst) ha
  rw [instance_columns,he] at hm
  exact hd c hc hm

/-- All corrected constraints hold on every actual hash-row helper, even when
its digest overlay contains nonzero sender-counter register bytes. -/
theorem additions (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecActual.additions,
      e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!))
        nxt first last trans)=0 := by
  have hz : ∀c∈[kR,rs,rend,fS,fA,ehp],
      Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!)=0 := by
    intro c hc
    rw [ProcPriorCodecHashReads.phase_flags_zero _ _ _ _ _ _ c hc
      (instance_avoids I R present vidV c hc)]
    rfl
  exact ProcPriorCodecNonrecordPhase.inactive_header _ nxt first last trans
    (hz rs (by simp)) (hz kR (by simp)) (hz rend (by simp))
    (hz fA (by simp)) (hz fS (by simp)) (hz ehp (by simp))

end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
