import ZkFormal.NearV3.Assembly.CompactDigestRows
import ZkFormal.NearV3.Assembly.SchedulerRootDigest

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem walk_reg (I : Render.UpsInst) (t i : Nat) (hi : i<32) :
    wCell I t (reg i)=wReg I t i := by
  change wCell I t (129+i)=_
  unfold wCell
  split <;> (try omega)
  simp only [show 129≤129+i ∧ 129+i<161 by omega,ite_true,true_and,Nat.add_sub_cancel_left]

/-- W3 is the unique walk-row DIGEST consumer; the exact physical field tuple
uses the declared native root job id, length and post-root bytes. -/
theorem walk_digest (I : Render.UpsInst) (t : Nat) (D : URow) :
    compactMsgs (fun x=>((wCell I t x : Int):Fp).toNat) D B_DIGEST false=
      if t=3 then [digMsg (Fp.ofNat (upsertJobId I.tau (nQ I))).toNat
        (Fp.ofNat (rlen I)).toNat
        ((List.range 32).map fun i=>(Fp.ofNat (I.post.getD i 0)).toNat)] else [] := by
  rw [row_digest _ D (by intro x; exact Fp.toNat_lt _)]
  by_cases ht : t=3
  · subst t
    have hr : regN (fun x=>((wCell I 3 x : Int):Fp).toNat)=
        (List.range 32).map (fun i=>(Fp.ofNat (I.post.getD i 0)).toNat) := by
      unfold regN
      apply List.map_congr_left
      intro i hi
      dsimp only
      rw [walk_reg I 3 i (List.mem_range.mp hi)]
      simp only [wReg,ite_false,ite_true,show ¬(3:Nat)=0 by decide]
      change (Fp.ofNat (I.post.getD i 0)).toNat=(Fp.ofNat (I.post.getD i 0)).toNat
      rfl
    rw [hr]
    simp only [wCell,gD,dI,dL,ind,ite_true,show ((1:Int):Fp).toNat=1 by decide]
    rw [←upsertJobId_renderer]
    rfl
  · simp [wCell,gD,ind,ht,show ((0:Int):Fp).toNat=0 by decide]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
