import ZkFormal.NearV3.Assembly.RcptEntityFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem ofNat_add_one (n : Nat) : Fp.ofNat (n+1)=Fp.ofNat n+1 := by
  change ((n+1:Nat):Fp)=(n:Fp)+1
  grind only

theorem entityBoundary_local (tr : Trace Fp) (pos : Nat) (pub : List Fp) (a b : EntityPlan)
    (ha : EntityCells tr pos a) (hb : EntityCells tr ((pos+1)%tr.height 0) b)
    (hfa : EntityEndFlags tr pos pub a) (hfb : EntityStartFlags tr ((pos+1)%tr.height 0) b)
    (hbound : EntityBoundary a b)
    (hcount : a.lastInList=true→a.withinList=a.listCount) :
    ∀e∈listBoundaryConstraints,e.eval tr 0 pos pub=0 := by
  obtain ⟨hj,hr,hbody,hlast,hfinal,hreceipt,hcounts⟩ := hbound
  intro e he
  simp only [listBoundaryConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|he
  · simp only [eval_mul3,eval_n,eval_not,eval_add,hfa.boundary,hfb.active,hfb.predecessor,hfb.header]
    cases hp : b.isHeader <;> simp [bitCell] <;> grind only
  · simp only [eval_sub,eval_mul,eval_c,eval_not,eval_n,hfa.listEnd,hfa.boundary,hfb.firstReceipt,hlast]
    cases hp : b.isHeader <;> simp [bitCell] <;> grind only
  · simp only [eval_sub,eval_mul,eval_c,eval_not,eval_n,hfa.activeEnd,hfinal,hfb.active]
    change (0:Fp)-_* (1-1)=0
    grind only
  · simp only [eval_mul3,eval_sub,eval_add,eval_c,eval_n,eval_k,hfa.listEnd,hfb.active,ha.listIndex,hb.listIndex]
    cases hp : a.lastInList
    · simp [bitCell];grind only
    · simp only [hp,ite_true] at hj
      rw [hj,ofNat_add_one]
      grind only
  · simp only [eval_mul,eval_sub,eval_add,eval_c,eval_n,hfb.active,hfa.boundary,hfa.lastReceipt,ha.receiptIndex,hb.receiptIndex]
    rw [hr]
    cases hp : a.isHeader
    · simp only [hp,Bool.false_eq_true,ite_false,Bool.not_false,bitCell,ite_true]
      rw [ofNat_add_one];grind only
    · simp only [hp,ite_true,Nat.add_zero,Bool.not_true,bitCell,ite_false]
      grind only
  · simp only [eval_mul,eval_sub,eval_add,eval_c,eval_n,eval_k,hfb.firstReceipt,hfa.boundary,ha.withinList,hb.withinList]
    cases hp : b.isHeader
    · have hh := (hreceipt hp).1
      rw [hh,ofNat_add_one];grind only
    · simp only [hp,Bool.not_true,bitCell,ite_false];grind only
  · simp only [eval_mul,eval_sub,eval_c,hfa.listEnd,ha.withinList,ha.listCount]
    cases hp : a.lastInList
    · simp [bitCell];grind only
    · rw [hcount hp];grind only
  · simp only [eval_mul,eval_sub,eval_c,eval_n,hfb.firstReceipt,hfa.boundary,ha.rcEnd]
    cases hp : b.isHeader
    · rw [hb.rcStart hp,(hreceipt hp).2];grind only
    · simp only [hp,Bool.not_true,bitCell,ite_false];grind only
  · simp only [eval_mul,eval_sub,eval_c,eval_n,ha.bodyEnd,hb.bodyStart,hbody]
    grind only
  · obtain ⟨col,hcol,rfl⟩ := List.mem_map.mp he
    have hcols : col=j ∨ col=nj := by simpa only [lconsts,List.mem_cons,List.not_mem_nil,or_false] using hcol
    simp only [eval_mul3,eval_sub,eval_c,eval_n,eval_not,hfa.active,hfa.listEnd]
    cases hp : a.lastInList
    · simp only [hp,ite_false,Nat.add_zero] at hj
      have hn := hcounts hp
      rcases hcols with rfl|rfl
      · rw [ha.listIndex,hb.listIndex,hj];grind only
      · rw [ha.listCount,hb.listCount,hn];grind only
    · simp only [hp,bitCell,ite_true];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
