import ZkFormal.NearV3.Qv.Candidates.ValueGen

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen.RowCells
open NearSpec

/-! Cached cell projections keep local AIR proofs from repeatedly expanding row lists. -/
@[simp] theorem cell0 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 0 0 = 1 := by
  simp [row,List.range_succ]

@[simp] theorem cell1 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 1 0 = (decide (pos=0)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell2 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 2 0 = (decide (cfg.length=0 ∨ pos+1=cfg.length)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell3 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 3 0 = cfg.vid := by
  simp [row,List.range_succ]

@[simp] theorem cell4 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 4 0 = cfg.length := by
  simp [row,List.range_succ]

@[simp] theorem cell5 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 5 0 = pos := by
  simp [row,List.range_succ]

@[simp] theorem cell6 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 6 0 = byte := by
  simp [row,List.range_succ]

@[simp] theorem cell7 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 7 0 = cfg.users := by
  simp [row,List.range_succ]

@[simp] theorem cell8 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 8 0 = cfg.tau := by
  simp [row,List.range_succ]

@[simp] theorem cell9 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 9 0 = entry := by
  simp [row,List.range_succ]

@[simp] theorem cell10 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 10 0 = cfg.count := by
  simp [row,List.range_succ]

@[simp] theorem cell11 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 11 0 = (decide (cfg.length=0)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell12 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 12 0 = (!(decide (cfg.length=0))).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell13 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 13 0 = (!(decide (cfg.length=0 ∨ pos+1=cfg.length))).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell14 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 14 0 = (decide (cfg.mode=0)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell15 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 15 0 = (decide (cfg.mode=1)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell16 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 16 0 = (decide (cfg.mode=2)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell17 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 17 0 = (decide (phase=0)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell18 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 18 0 = (decide (phase=1)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell19 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 19 0 = (decide (phase=2)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell20 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 20 0 = (decide (phase=3)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell21 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 21 0 = (decide (phase≠4 ∧ subpos=0)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell22 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 22 0 = (decide (phase≠4 ∧ subpos=1)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell23 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 23 0 = (decide (phase≠4 ∧ subpos=2)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell24 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 24 0 = (decide (phase≠4 ∧ subpos=3)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell25 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 25 0 = (decide (phase≠4 ∧ subpos=4)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell26 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 26 0 = (decide (phase≠4 ∧ subpos=5)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell27 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 27 0 = (decide (phase≠4 ∧ subpos=6)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell28 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 28 0 = (decide (phase≠4 ∧ subpos=7)).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell29 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 29 0 = (regs.getD 0 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell30 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 30 0 = (regs.getD 1 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell31 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 31 0 = (regs.getD 2 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell32 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 32 0 = (regs.getD 3 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell33 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 33 0 = (regs.getD 4 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell34 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 34 0 = (regs.getD 5 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell35 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 35 0 = (regs.getD 6 0).toNat := by
  simp [row,List.range_succ]

@[simp] theorem cell36 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase subpos entry regs).getD 36 0 = (regs.getD 7 0).toNat := by
  simp [row,List.range_succ]


@[simp] theorem opt0 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[0]?).getD 0 = 1 := by
  simpa only [List.getD_eq_getElem?_getD] using cell0 cfg pos byte phase subpos entry regs

@[simp] theorem opt1 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[1]?).getD 0 = (decide (pos=0)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell1 cfg pos byte phase subpos entry regs

@[simp] theorem opt2 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[2]?).getD 0 = (decide (cfg.length=0 ∨ pos+1=cfg.length)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell2 cfg pos byte phase subpos entry regs

@[simp] theorem opt3 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[3]?).getD 0 = cfg.vid := by
  simpa only [List.getD_eq_getElem?_getD] using cell3 cfg pos byte phase subpos entry regs

@[simp] theorem opt4 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[4]?).getD 0 = cfg.length := by
  simpa only [List.getD_eq_getElem?_getD] using cell4 cfg pos byte phase subpos entry regs

@[simp] theorem opt5 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[5]?).getD 0 = pos := by
  simpa only [List.getD_eq_getElem?_getD] using cell5 cfg pos byte phase subpos entry regs

@[simp] theorem opt6 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[6]?).getD 0 = byte := by
  simpa only [List.getD_eq_getElem?_getD] using cell6 cfg pos byte phase subpos entry regs

@[simp] theorem opt7 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[7]?).getD 0 = cfg.users := by
  simpa only [List.getD_eq_getElem?_getD] using cell7 cfg pos byte phase subpos entry regs

@[simp] theorem opt8 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[8]?).getD 0 = cfg.tau := by
  simpa only [List.getD_eq_getElem?_getD] using cell8 cfg pos byte phase subpos entry regs

@[simp] theorem opt9 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[9]?).getD 0 = entry := by
  simpa only [List.getD_eq_getElem?_getD] using cell9 cfg pos byte phase subpos entry regs

@[simp] theorem opt10 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[10]?).getD 0 = cfg.count := by
  simpa only [List.getD_eq_getElem?_getD] using cell10 cfg pos byte phase subpos entry regs

@[simp] theorem opt11 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[11]?).getD 0 = (decide (cfg.length=0)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell11 cfg pos byte phase subpos entry regs

@[simp] theorem opt12 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[12]?).getD 0 = (!(decide (cfg.length=0))).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell12 cfg pos byte phase subpos entry regs

@[simp] theorem opt13 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[13]?).getD 0 = (!(decide (cfg.length=0 ∨ pos+1=cfg.length))).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell13 cfg pos byte phase subpos entry regs

@[simp] theorem opt14 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[14]?).getD 0 = (decide (cfg.mode=0)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell14 cfg pos byte phase subpos entry regs

@[simp] theorem opt15 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[15]?).getD 0 = (decide (cfg.mode=1)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell15 cfg pos byte phase subpos entry regs

@[simp] theorem opt16 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[16]?).getD 0 = (decide (cfg.mode=2)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell16 cfg pos byte phase subpos entry regs

@[simp] theorem opt17 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[17]?).getD 0 = (decide (phase=0)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell17 cfg pos byte phase subpos entry regs

@[simp] theorem opt18 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[18]?).getD 0 = (decide (phase=1)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell18 cfg pos byte phase subpos entry regs

@[simp] theorem opt19 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[19]?).getD 0 = (decide (phase=2)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell19 cfg pos byte phase subpos entry regs

@[simp] theorem opt20 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[20]?).getD 0 = (decide (phase=3)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell20 cfg pos byte phase subpos entry regs

@[simp] theorem opt21 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[21]?).getD 0 = (decide (phase≠4 ∧ subpos=0)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell21 cfg pos byte phase subpos entry regs

@[simp] theorem opt22 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[22]?).getD 0 = (decide (phase≠4 ∧ subpos=1)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell22 cfg pos byte phase subpos entry regs

@[simp] theorem opt23 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[23]?).getD 0 = (decide (phase≠4 ∧ subpos=2)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell23 cfg pos byte phase subpos entry regs

@[simp] theorem opt24 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[24]?).getD 0 = (decide (phase≠4 ∧ subpos=3)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell24 cfg pos byte phase subpos entry regs

@[simp] theorem opt25 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[25]?).getD 0 = (decide (phase≠4 ∧ subpos=4)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell25 cfg pos byte phase subpos entry regs

@[simp] theorem opt26 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[26]?).getD 0 = (decide (phase≠4 ∧ subpos=5)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell26 cfg pos byte phase subpos entry regs

@[simp] theorem opt27 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[27]?).getD 0 = (decide (phase≠4 ∧ subpos=6)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell27 cfg pos byte phase subpos entry regs

@[simp] theorem opt28 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[28]?).getD 0 = (decide (phase≠4 ∧ subpos=7)).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell28 cfg pos byte phase subpos entry regs

@[simp] theorem opt29 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[29]?).getD 0 = (regs.getD 0 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell29 cfg pos byte phase subpos entry regs

@[simp] theorem opt30 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[30]?).getD 0 = (regs.getD 1 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell30 cfg pos byte phase subpos entry regs

@[simp] theorem opt31 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[31]?).getD 0 = (regs.getD 2 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell31 cfg pos byte phase subpos entry regs

@[simp] theorem opt32 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[32]?).getD 0 = (regs.getD 3 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell32 cfg pos byte phase subpos entry regs

@[simp] theorem opt33 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[33]?).getD 0 = (regs.getD 4 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell33 cfg pos byte phase subpos entry regs

@[simp] theorem opt34 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[34]?).getD 0 = (regs.getD 5 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell34 cfg pos byte phase subpos entry regs

@[simp] theorem opt35 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[35]?).getD 0 = (regs.getD 6 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell35 cfg pos byte phase subpos entry regs

@[simp] theorem opt36 (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ((row cfg pos byte phase subpos entry regs)[36]?).getD 0 = (regs.getD 7 0).toNat := by
  simpa only [List.getD_eq_getElem?_getD] using cell36 cfg pos byte phase subpos entry regs

end ZkFormal.NearV3.Qv.Candidates.ValueGen.RowCells
