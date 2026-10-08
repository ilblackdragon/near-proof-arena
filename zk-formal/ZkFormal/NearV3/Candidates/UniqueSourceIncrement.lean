import ZkFormal.NearV3.Candidates.UniqueSourceBoundary
namespace ZkFormal.NearV3.Candidates.UniqueSourceIncrement
open ZkFormal.Near Rcpt.Candidates Render.SrcpGen

/-- The corrected increment is exactly the polynomial in the actual row cells. -/
theorem cells (bs : List SrcpB) (rep : Nat→Bool) (r : Nat) :
    (UniqueSourceBoundary.delta bs r : Int)=
      ((UniqueSourceRender.cell bs rep r SrcpV3.rt : Int)-
        (UniqueSourceRender.cell bs rep r SrcpV3.dup : Int))*
        ((UniqueSourceRender.cell bs rep r SrcpV3.L : Int)+44)+
      33*(UniqueSourceRender.cell bs rep r SrcpV3.sf : Int)*
        (UniqueSourceRender.cell bs rep r SrcpV3.sg : Int)*
        (1-(UniqueSourceRender.cell bs rep r SrcpV3.lf : Int)) := by
  by_cases hr : r<DedupRender.R bs
  · simp only [UniqueSourceBoundary.delta,hr,ite_true]
    generalize hp : (DedupRender.recs bs).getD r default=p
    rcases p with ⟨i,k⟩
    simp only [UniqueSourceRender.cell,DedupRender.cell,hr,ite_true,
      SrcpV3.rt,SrcpV3.dup,SrcpV3.L,SrcpV3.sf,SrcpV3.sg,SrcpV3.lf,SrcpV3.sz,
      show ¬(0=54) by decide,show ¬(14=54) by decide,show ¬(11=54) by decide,
      show ¬(6=54) by decide,show ¬(1=54) by decide,show ¬(2=54) by decide,
      show ¬(0=56) by decide,show ¬(14=56) by decide,show ¬(11=56) by decide,
      show ¬(6=56) by decide,show ¬(1=56) by decide,show ¬(2=56) by decide,ite_false,hp]
    cases k with
    | root =>
      cases hd : (bs.getD i default).dup <;>
        simp only [DedupRender.rowFrame,
          DedupRender.frame,hd,rootFrame,Frame.cell,UniqueSourceCounter.increment,
          Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true] <;> simp
    | leaf p =>
      simp only [DedupRender.rowFrame,
        DedupRender.frame,leafFrame,Frame.cell,UniqueSourceCounter.increment,
        Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true] <;> simp
    | path i o =>
      by_cases ho : o=0 <;>
        simp only [DedupRender.rowFrame,
          DedupRender.frame,pathFrame,Frame.cell,UniqueSourceCounter.increment,ho,
          Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true] <;> simp [ho]
  · simp [UniqueSourceBoundary.delta,UniqueSourceRender.cell,DedupRender.cell,hr,
      SrcpV3.rt,SrcpV3.dup,SrcpV3.L,SrcpV3.sf,SrcpV3.sg,SrcpV3.lf,SrcpV3.sz]

end ZkFormal.NearV3.Candidates.UniqueSourceIncrement
