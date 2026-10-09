import ZkFormal.NearV3.Candidates.MemHeight
namespace ZkFormal.NearV3.Candidates.MemNativeCells
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
section
open Mem in
theorem initArr_rel (g : Seg)  : RowRel (initArr g) (initV g) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨
      c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [initArr, initV, MV.cell, gd_set, gd_setIf, gd_zrow, size_set, size_zrow, Mem.width, Mem.act,
      Mem.fst, Mem.lst, Mem.isRd, Mem.isGr, Mem.addr, Mem.t, Mem.tp, Mem.vin, Mem.v, Mem.wp, Mem.w,
      Mem.al, Mem.isL, Mem.inc, Mem.ok, Mem.cc, Mem.sf, ↓reduceIte, and_self, and_true, true_and,
      and_false, false_and]
  · simp [initArr, size_set, size_zrow, Mem.width]

theorem opArr_rel (g : Seg) (i tp : Nat) (o : MOp)  :
    RowRel (opArr g i tp o) (opV g i tp o) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨
      c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [opArr, opV, MV.cell, gd_set, gd_setIf, gd_zrow, size_set, size_zrow, Mem.width, Mem.act,
      Mem.fst, Mem.lst, Mem.isRd, Mem.isGr, Mem.addr, Mem.t, Mem.tp, Mem.vin, Mem.v, Mem.wp, Mem.w,
      Mem.al, Mem.isL, Mem.inc, Mem.ok, Mem.cc, Mem.sf, ↓reduceIte, and_self, and_true, true_and,
      and_false, false_and]
  · simp [opArr, size_set, size_zrow, Mem.width]
end

theorem foldl_rel (g : Seg) :
    ∀ (os : List MOp) (out : Array (Array Nat)) (outVs : List MV) (tp k : Nat),
      RRel out.toList outVs →
      RRel (os.foldl (stepF g) (out,tp,k)).1.toList (outVs++opsVs g k tp os)
  | [],out,outVs,tp,k,h=>by simpa [opsVs] using h
  | o::os,out,outVs,tp,k,h=>by
    rw [List.foldl_cons]
    have hh:=foldl_rel g os (out.push (opArr g (k+1) tp o)) (outVs++[opV g (k+1) tp o]) o.t (k+1)
      (by rw [Array.toList_push]; exact h.append (.cons (opArr_rel g _ _ _) .nil))
    simpa [opsVs,stepF] using hh

theorem segment (g : Seg) : RRel (Gen.Mem.segRows g).toList (segVs g) := by
  rw [segRows_eq]
  have h:=foldl_rel g g.ops #[initArr g] [initV g] 0 0 (.cons (initArr_rel g) .nil)
  simpa [segVs] using h

theorem flat : ∀gs:List Seg,RRel (gs.flatMap (fun g=>(Gen.Mem.segRows g).toList)) (memVs gs)
  | []=>.nil
  | g::gs=>by
    rw [List.flatMap_cons]
    exact (segment g).append (flat gs)

theorem rows (R : Run) : RRel (Gen.Mem.rows R).toList (memVs R.segs) := by
  unfold Gen.Mem.rows
  rw [foldl_append_toList Gen.Mem.segRows R.segs #[]]
  simpa using flat R.segs
end ZkFormal.NearV3.Candidates.MemNativeCells
