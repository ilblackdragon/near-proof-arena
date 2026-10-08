import ZkFormal.NearV3.Assembly.CompactNodeDigestRows

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- DIGEST traffic depends only on its gate, id, length and 32 registers.
All UPB counters and all segment metadata are irrelevant to this bus. -/
theorem digest_projection (C C' D D' : URow) (hC : ∀x,C x<P) (hC' : ∀x,C' x<P)
    (hg : C gD=C' gD) (hi : C dI=C' dI) (hl : C dL=C' dL)
    (hr : ∀i,i<32→C (reg i)=C' (reg i)) :
    compactMsgs C D B_DIGEST false=compactMsgs C' D' B_DIGEST false := by
  rw [row_digest C D hC,row_digest C' D' hC',hg,hi,hl]
  have hh : regN C=regN C' := by
    unfold regN
    exact List.map_congr_left (fun i hi=>hr i (List.mem_range.mp hi))
  rw [hh]

private theorem qcell_reg (I : Render.UpsInst) (k p u i : Nat) (hi : i<32) :
    qCell I k p u (reg i)=qRowCell I k p u (reg i) := by
  unfold qCell isPC reg
  have h1 : ¬129+i<100 := by omega
  have h2 : ¬179≤129+i := by omega
  simp [h1,h2]

private theorem qrow_reg_counter (I : Render.UpsInst) (k p u i : Nat) (hi : i<32) :
    qRowCell I k p u (reg i)=qRowCell I k p 0 (reg i) := by
  unfold qRowCell reg qRow
  split <;> (try omega)

/-- The complete node lookup inventory is independent of UPB reuse counters. -/
theorem qcell_digest (I : Render.UpsInst) (k p u : Nat) (D : URow) :
    compactMsgs (fun x=>((qCell I k p u x : Int):Fp).toNat) D B_DIGEST false=
      compactMsgs (fun x=>((qRowCell I k p 0 x : Int):Fp).toNat) (fun _=>0) B_DIGEST false := by
  apply digest_projection _ _ _ _ (fun _=>Fp.toNat_lt _) (fun _=>Fp.toNat_lt _)
  · rfl
  · rfl
  · rfl
  · intro i hi
    rw [qcell_reg I k p u i hi,qrow_reg_counter I k p u i hi]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
