import ZkFormal.NearV3.Assembly.CompactDigestProjection

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- Exact per-record requests, without segment metadata or UPB counters. -/
def digestRowCell (I : Render.UpsInst) : RK→Nat→Int
  | .w t=>wCell I t
  | .v p=>vCell I p
  | .q k p=>qRowCell I k p 0

def digestRowMsgs (I : Render.UpsInst) (r : RK) : List Msg :=
  compactMsgs (fun x=>((digestRowCell I r x : Int):Fp).toNat) (fun _=>0) B_DIGEST false

private theorem not_seg_reg (i : Nat) (hi : i<32) : isSeg (reg i)=false := by
  unfold isSeg reg
  have h1 : ¬129+i<49 := by omega
  have h2 : ¬176≤129+i := by omega
  have h3 : ¬129+i=186 := by omega
  simp [h1,h2,h3]

private theorem qcell_reg_counter (I : Render.UpsInst) (k p u i : Nat) (hi : i<32) :
    qCell I k p u (reg i)=qRowCell I k p 0 (reg i) := by
  unfold qCell isPC reg
  have h1 : ¬129+i<100 := by omega
  have h2 : ¬179≤129+i := by omega
  simp only [show (decide (49≤129+i) && decide (129+i<100) ||
    decide (179≤129+i) && decide (129+i<184))=false by simp [h1,h2],Bool.false_eq_true,ite_false]
  unfold qRowCell qRow
  split <;> (try omega)

/-- Segment columns and read counters cannot alter any DIGEST row. -/
theorem compactRowCell_digests (insts : List Render.UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    compactMsgs (fun x=>((compactRowCell insts q (i,rk) x : Int):Fp).toNat) D B_DIGEST false=
      digestRowMsgs (inst insts i) rk := by
  unfold digestRowMsgs
  apply digest_projection _ _ _ _ (fun _=>Fp.toNat_lt _) (fun _=>Fp.toNat_lt _)
  · cases rk <;> rfl
  · cases rk <;> rfl
  · cases rk <;> rfl
  · intro j hj
    simp only [compactRowCell,not_seg_reg j hj,Bool.false_eq_true,ite_false]
    cases rk with
    | w t=>rfl
    | v p=>rfl
    | q k p=>
      dsimp only [digestRowCell]
      rw [qcell_reg_counter _ k p _ j hj]

private theorem range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun k=>xs.getD k d)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range]
  rw [←List.getElem_eq_getD (h:=hj) d]

private theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

/-- All physical DIGEST demands in exact instance/record order. This retains
all fresh-value and child windows, including repeated message identifiers. -/
theorem compactGeneratedDigests_recs (insts : List Render.UpsInst) :
    compactGeneratedDigests insts=(compactRecs insts).flatMap
      (fun r=>digestRowMsgs (inst insts r.1) r.2) := by
  unfold compactGeneratedDigests
  apply Eq.trans (b := (List.range (compactR insts)).flatMap fun q=>
    digestRowMsgs (inst insts ((compactRecs insts).getD q default).1)
      ((compactRecs insts).getD q default).2)
  · apply flatMap_congr_mem
    intro q hq
    have hq:=List.mem_range.mp hq
    simp only [compactCell,hq,ite_true]
    exact compactRowCell_digests insts q _ _ _
  · conv=>rhs;rw [←range_getD (compactRecs insts) default]
    rw [List.flatMap_map,compactRecs_length]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
