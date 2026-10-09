import ZkFormal.NearV3.Assembly.CompactWalkNativeRoot

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem fresh_reg (I : Render.UpsInst) (Q : Render.UpsPartI)
    (k p st fl wi u i : Nat) (hi : i<32) (hw : WinFrB I Q st wi=true) :
    qRow I Q k p st 0 fl wi u (reg i)=(Q.q.getD (p+i) 0 : Int) := by
  change qRow I Q k p st 0 fl wi u (129+i)=_
  unfold qRow
  split <;> (try omega)
  simp only [show ¬(106≤129+i ∧ 129+i<115) by omega,ite_false,
    show 129≤129+i ∧ 129+i<161 by omega,ite_true,Nat.add_sub_cancel_left,
    winFrV,hw,ind,ite_true,Nat.sub_zero,hi,and_self]

/-- Every node DIGEST row consumes the actual 32 output bytes at that window.
The request is retained once per physical window, without deduplicating jobs. -/
theorem node_row_digest (I : Render.UpsInst) (Q : Render.UpsPartI)
    (k p st ix fl wi u : Nat) (D : URow) :
    compactMsgs (fun x=>((qRow I Q k p st ix fl wi u x : Int):Fp).toNat) D B_DIGEST false=
      if GdB I Q st ix wi=true then
        [digMsg ((dIV I Q st ix wi k : Fp).toNat) ((dLV I Q st ix wi : Fp).toNat)
          ((List.range 32).map fun i=>(Fp.ofNat (Q.q.getD (p+i) 0)).toNat)] else [] := by
  rw [row_digest _ D (by intro x;exact Fp.toNat_lt _)]
  by_cases hg : GdB I Q st ix wi=true
  · have hh : ix=0 ∧ WinFrB I Q st wi=true := by simpa only [GdB,Bool.and_eq_true,beq_iff_eq] using hg
    rcases hh with ⟨rfl,hw⟩
    have hr : regN (fun x=>((qRow I Q k p st 0 fl wi u x : Int):Fp).toNat)=
        (List.range 32).map (fun i=>(Fp.ofNat (Q.q.getD (p+i) 0)).toNat) := by
      unfold regN
      apply List.map_congr_left
      intro i hi
      dsimp only
      rw [fresh_reg I Q k p st fl wi u i (List.mem_range.mp hi) hw]
      rfl
    rw [hr]
    simp only [qRow,gD,dI,dL,gDV,ind,hg,ite_true,show ((1:Int):Fp).toNat=1 by decide]
    rfl
  · have hz : GdB I Q st ix wi=false := Bool.eq_false_iff.mpr hg
    simp only [qRow,gD,gDV,ind,hz,Bool.false_eq_true,ite_false,show ((0:Int):Fp).toNat=0 by decide,
      show ¬(0:Nat)=1 by decide]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
