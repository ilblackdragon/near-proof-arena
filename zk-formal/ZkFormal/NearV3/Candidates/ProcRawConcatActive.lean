import ZkFormal.NearV3.Candidates.ProcRawConcatGeometry
namespace ZkFormal.NearV3.Candidates.ProcRawConcatActive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly.CodecDigest
open ProcRawConcatGeometry ProcRawConcatBoundary ProcPriorCells

def Good (b : NativeBlock) : Prop :=
  b.old.links.length<16777216 ∧ (b.prior.isSome=false→b.old=NearSpec.Bandwidth.State.initial)

theorem stamp_zero (row : Nat→Fp) (h:row ProcPriorRawFrame.tau=0) : stamp 0 row=row := by
  funext c
  unfold stamp
  split
  · next hc=>subst c; exact h.symm
  · rfl

theorem block_first (b : NativeBlock) (hb:Good b) (ht:b.run.tau=0)
    (e : Expr) (he:e∈ProcPriorRawFrame.constraints) :
    e.evalWith (env (blockCell b 0) (blockCell b 1) 1 0 1)=0 := by
  unfold blockCell
  rw [ht,show Fp.ofNat 0=(0:Fp) from rfl,
    stamp_zero _ (ProcRawConcatInterior.tau_zero _ _ _ _),
    stamp_zero _ (ProcRawConcatInterior.tau_zero _ _ _ _)]
  have h:=ProcPriorRawActive.active_constraints b.old b.vid 0 b.prior.isSome hb.1 hb.2
    (by unfold ProcPriorRawSlots.length; omega) e he
  simpa [bit] using h

theorem start_pos (pre : List NativeBlock) (h:pre≠[]) : 0<start pre := by
  cases pre with
  | nil=>contradiction
  | cons b bs=>simp [start,rows,List.flatMap_cons,block_length]; have:=block_pos b; omega

theorem active (bs : List NativeBlock) (hb:∀b∈bs,Good b)
    (hfirst:∀b rest,bs=b::rest→b.run.tau=0)
    (hnext:∀pre b c rest,bs=pre++b::c::rest→c.run.tau=b.run.tau+1)
    (r : Nat) (hr:r<(rows bs).length) (e : Expr) (he:e∈ProcPriorRawFrame.constraints) :
    e.evalWith (env (cell bs r) (cell bs (r+1)) (if r=0 then 1 else 0) 0 1)=0 := by
  obtain ⟨pre,b,post,i,hbs,hi,hr⟩:=active_cases bs r hr
  have hbg:=hb b (by simp [hbs])
  rw [hr,block_lookup bs pre post b hbs i hi]
  by_cases hin:i+1<blockLength b
  · rw [show start pre+i+1=start pre+(i+1) by omega,block_lookup bs pre post b hbs (i+1) hin]
    by_cases hz:start pre+i=0
    · have hip:i=0 := by omega
      have hp:pre=[] := by
        by_cases hh:pre=[]
        · exact hh
        · have:=start_pos pre hh; omega
      subst pre
      subst i
      simp only [hz,ite_true]
      exact block_first b hbg (hfirst b post (by simpa using hbs)) e he
    · rw [if_neg hz]
      exact ProcRawConcatInterior.inside b.old b.vid i b.prior.isSome _ hbg.1 hbg.2 hin e he
  · have hiend:i+1=blockLength b := by omega
    have hi':i=5+24*b.old.links.length+31 := by unfold blockLength ProcPriorRawSlots.length at hiend; omega
    have hz:start pre+i≠0 := by omega
    rw [if_neg hz,show start pre+i+1=start pre+blockLength b by omega,after_block bs pre post b hbs]
    have hcell:blockCell b i=stamp (Fp.ofNat b.run.tau)
        (ProcPriorRawGen.cells b.old b.vid b.prior.isSome (5+24*b.old.links.length+31) (.hash 31)) := by
      simp only [blockCell,hi',ProcPriorRawGen.trace,ProcPriorRawSlots.hash _ 31 (by decide +kernel)]
    rw [hcell]
    cases post with
    | nil=>exact ProcRawConcatBoundary.padding_constraints b.old b.vid b.prior.isSome _ hbg.1 hbg.2 e he
    | cons c rest=>
      have ht:=hnext pre b c rest hbs
      have hcast:Fp.ofNat c.run.tau=Fp.ofNat b.run.tau+1 := by
        rw [ht]
        change ((b.run.tau+1:Nat):Fp)=(b.run.tau: Fp)+1
        grind
      have hcell':blockCell c 0=stamp (Fp.ofNat b.run.tau+1)
          (ProcPriorRawGen.cells c.old c.vid c.prior.isSome 0 (.header 0)) := by
        simp only [blockCell,hcast,ProcPriorRawGen.trace,ProcPriorRawSlots.header _ 0 (by decide +kernel)]
      dsimp only
      rw [hcell']
      exact ProcRawConcatBoundary.next_constraints b.old c.old b.vid c.vid b.prior.isSome c.prior.isSome
        _ hbg.1 hbg.2 e he
end ZkFormal.NearV3.Candidates.ProcRawConcatActive
