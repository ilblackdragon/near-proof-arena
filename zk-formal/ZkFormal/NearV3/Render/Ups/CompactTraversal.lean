import ZkFormal.NearV3.Render.Ups.CompactTableCandidate

namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near.Render UpsGen

def compactNext (I : UpsInst) : RK→Option RK
  | .w t => if t+1<4 then some (.w (t+1)) else some (.q 0 0)
  | .v _ => none
  | .q k p => nextRK I (.q k p)

def compactRecs (insts : List UpsInst) : List (Nat×RK) :=
  (List.range insts.length).flatMap fun i=>(compactRecsI (inst insts i)).map ((i,·))

def CompactAdj (insts : List UpsInst) (a b : Nat×RK) : Prop :=
  (compactNext (inst insts a.1) a.2=some b.2 ∧ b.1=a.1) ∨
  (compactNext (inst insts a.1) a.2=none ∧ b=(a.1+1,.w 0))

theorem compactRecsI_adj {I : UpsInst} (ok : InstOk I) :
    Adj2 (fun a b=>compactNext I a=some b) (compactRecsI I) := by
  unfold compactRecsI
  apply Adj2.append
  · exact range_adj _ _ 4 (fun i hi=>by simp only [compactNext]; rw [ite_eq_left (by omega)])
  · apply Adj2.flatMap
    · intro k hk
      exact range_adj _ _ _ (fun p hp=>by simp only [compactNext,nextRK]; rw [ite_eq_left hp])
    · apply range_adj'
      intro k hk a b ha hb
      rw [range_last _ _ (ok.q1 k (by omega))] at ha
      rw [range_head _ _ (ok.q1 (k+1) hk)] at hb
      cases ha; cases hb
      simp only [compactNext,nextRK]
      rw [ite_eq_right (by omega),ite_eq_left hk]
    · intro k hk
      exact range_ne _ _ (ok.q1 k (List.mem_range.mp hk))
  · intro a b ha hb
    rw [range_last _ 4 (by omega)] at ha
    rw [parts_head ok.L1 ok.nQ1 ok.q1] at hb
    cases ha; cases hb
    rfl

theorem compactRecsI_head (I : UpsInst) : (compactRecsI I).head?=some (.w 0) := by
  simp [compactRecsI,List.range_succ_eq_map]

theorem compactRecsI_last {I : UpsInst} (ok : InstOk I) :
    (compactRecsI I).getLast?=some (lastRK I) := by
  unfold compactRecsI
  rw [List.getLast?_append,parts_last ok.L1 ok.nQ1 ok.q1]
  rfl

theorem compactRecsI_ne (I : UpsInst) : compactRecsI I≠[] := by
  simp [compactRecsI,List.range_succ_eq_map]

theorem compactNext_last {I : UpsInst} (ok : InstOk I) : compactNext I (lastRK I)=none :=
  next_last ok.L1 ok.nQ1 ok.q1

theorem compactRecs_adj {insts : List UpsInst} (hi : ∀I∈insts,InstOk I) :
    Adj2 (CompactAdj insts) (compactRecs insts) := by
  unfold compactRecs
  apply Adj2.flatMap
  · intro i hi'
    apply Adj2.map
    exact Adj2.mono (fun a b h=>.inl ⟨h,rfl⟩) (compactRecsI_adj (hi _ (inst_mem (List.mem_range.mp hi'))))
  · apply range_adj'
    intro i hi' a b ha hb
    have hi0 := hi _ (inst_mem (by omega : i<insts.length))
    have hi1 := hi _ (inst_mem hi')
    rw [List.getLast?_map,compactRecsI_last hi0] at ha
    rw [List.head?_map,compactRecsI_head] at hb
    cases ha; cases hb
    exact .inr ⟨compactNext_last hi0,rfl⟩
  · intro i hi'
    simp only [ne_eq,List.map_eq_nil_iff]
    exact compactRecsI_ne _
end ZkFormal.NearV3.Render.UpsRelay
