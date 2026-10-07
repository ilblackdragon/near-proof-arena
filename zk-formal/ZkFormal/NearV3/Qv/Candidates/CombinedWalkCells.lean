import ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

/-! Cached projections of actual generated rows for local and traffic proofs. -/

@[simp] theorem Walk.cell0 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 0 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell1 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 1 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell2 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 2 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell3 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 3 0 = (if w.value.isSome then w.vid else 0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell4 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 4 0 = (w.mode) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell5 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 5 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell6 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 6 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell7 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 7 0 = (w.users) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell8 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 8 0 = (w.tau) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell9 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 9 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell10 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 10 0 = (w.count) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell11 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 11 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell12 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 12 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell13 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 13 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell14 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 14 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell15 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 15 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell16 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 16 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell17 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 17 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell18 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 18 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell19 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 19 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell20 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 20 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell21 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 21 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell22 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 22 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell23 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 23 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell24 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 24 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell25 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 25 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell26 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 26 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell27 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 27 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell28 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 28 0 = (0) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell29 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 29 0 = (b.toNat / 2^0 % 2) := by
  have hm : b.toNat / 2^0 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^0) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell30 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 30 0 = (b.toNat / 2^1 % 2) := by
  have hm : b.toNat / 2^1 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^1) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell31 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 31 0 = (b.toNat / 2^2 % 2) := by
  have hm : b.toNat / 2^2 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^2) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell32 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 32 0 = (b.toNat / 2^3 % 2) := by
  have hm : b.toNat / 2^3 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^3) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell33 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 33 0 = (b.toNat / 2^4 % 2) := by
  have hm : b.toNat / 2^4 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^4) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell34 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 34 0 = (b.toNat / 2^5 % 2) := by
  have hm : b.toNat / 2^5 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^5) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell35 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 35 0 = (b.toNat / 2^6 % 2) := by
  have hm : b.toNat / 2^6 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^6) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell36 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 36 0 = (b.toNat / 2^7 % 2) := by
  have hm : b.toNat / 2^7 % 2 < 256 := by have := Nat.mod_lt (b.toNat / 2^7) (by decide : 0<2); omega
  simp_all [Walk.row,ValueGen.row,List.range_succ,UInt8.toNat_ofNat,Nat.mod_eq_of_lt]

@[simp] theorem Walk.cell37 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 37 0 = (1) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell38 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 38 0 = (w.kind.code%2) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell39 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 39 0 = (w.kind.code/2) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell40 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 40 0 = (pos) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell41 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 41 0 = (b.toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell42 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 42 0 = (w.slot) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell43 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 43 0 = ((pos==0).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell44 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 44 0 = ((pos+1==w.kind.bytes.length).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell45 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 45 0 = (((pos+1==w.kind.bytes.length) && w.final).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell46 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 46 0 = ((!w.value.isSome).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell47 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 47 0 = (((w.kind.code==3) && !(pos==0)).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell48 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 48 0 = (((pos+1==w.kind.bytes.length) && w.value.isSome && (w.tau==0) && (w.kind.code==1)).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell49 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 49 0 = ((w.tau==0).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell50 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 50 0 = (w.lastMain.toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.cell51 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b).getD 51 0 = (((pos+1==w.kind.bytes.length) && w.value.isSome).toNat) := by
  simp [Walk.row,ValueGen.row,List.range_succ]

@[simp] theorem Walk.opt29 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[29]?).getD 0 = b.toNat / 2^0 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell29 pos b

@[simp] theorem Walk.opt30 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[30]?).getD 0 = b.toNat / 2^1 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell30 pos b

@[simp] theorem Walk.opt31 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[31]?).getD 0 = b.toNat / 2^2 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell31 pos b

@[simp] theorem Walk.opt32 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[32]?).getD 0 = b.toNat / 2^3 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell32 pos b

@[simp] theorem Walk.opt33 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[33]?).getD 0 = b.toNat / 2^4 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell33 pos b

@[simp] theorem Walk.opt34 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[34]?).getD 0 = b.toNat / 2^5 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell34 pos b

@[simp] theorem Walk.opt35 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[35]?).getD 0 = b.toNat / 2^6 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell35 pos b

@[simp] theorem Walk.opt36 (w : Walk) (pos : Nat) (b : UInt8) :
    ((w.row pos b)[36]?).getD 0 = b.toNat / 2^7 % 2 := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell36 pos b

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
