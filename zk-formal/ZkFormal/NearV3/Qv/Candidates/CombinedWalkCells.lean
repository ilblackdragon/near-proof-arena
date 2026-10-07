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

@[simp] theorem Walk.opt0 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[0]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell0 pos b

@[simp] theorem Walk.opt1 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[1]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell1 pos b

@[simp] theorem Walk.opt2 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[2]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell2 pos b

@[simp] theorem Walk.opt3 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[3]?.getD 0 = (if w.value.isSome then w.vid else 0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell3 pos b

@[simp] theorem Walk.opt4 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[4]?.getD 0 = (w.mode) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell4 pos b

@[simp] theorem Walk.opt5 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[5]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell5 pos b

@[simp] theorem Walk.opt6 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[6]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell6 pos b

@[simp] theorem Walk.opt7 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[7]?.getD 0 = (w.users) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell7 pos b

@[simp] theorem Walk.opt8 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[8]?.getD 0 = (w.tau) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell8 pos b

@[simp] theorem Walk.opt9 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[9]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell9 pos b

@[simp] theorem Walk.opt10 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[10]?.getD 0 = (w.count) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell10 pos b

@[simp] theorem Walk.opt11 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[11]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell11 pos b

@[simp] theorem Walk.opt12 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[12]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell12 pos b

@[simp] theorem Walk.opt13 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[13]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell13 pos b

@[simp] theorem Walk.opt14 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[14]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell14 pos b

@[simp] theorem Walk.opt15 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[15]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell15 pos b

@[simp] theorem Walk.opt16 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[16]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell16 pos b

@[simp] theorem Walk.opt17 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[17]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell17 pos b

@[simp] theorem Walk.opt18 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[18]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell18 pos b

@[simp] theorem Walk.opt19 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[19]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell19 pos b

@[simp] theorem Walk.opt20 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[20]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell20 pos b

@[simp] theorem Walk.opt21 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[21]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell21 pos b

@[simp] theorem Walk.opt22 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[22]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell22 pos b

@[simp] theorem Walk.opt23 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[23]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell23 pos b

@[simp] theorem Walk.opt24 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[24]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell24 pos b

@[simp] theorem Walk.opt25 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[25]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell25 pos b

@[simp] theorem Walk.opt26 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[26]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell26 pos b

@[simp] theorem Walk.opt27 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[27]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell27 pos b

@[simp] theorem Walk.opt28 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[28]?.getD 0 = (0) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell28 pos b

@[simp] theorem Walk.opt37 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[37]?.getD 0 = (1) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell37 pos b

@[simp] theorem Walk.opt38 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[38]?.getD 0 = (w.kind.code%2) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell38 pos b

@[simp] theorem Walk.opt39 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[39]?.getD 0 = (w.kind.code/2) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell39 pos b

@[simp] theorem Walk.opt40 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[40]?.getD 0 = (pos) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell40 pos b

@[simp] theorem Walk.opt41 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[41]?.getD 0 = (b.toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell41 pos b

@[simp] theorem Walk.opt42 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[42]?.getD 0 = (w.slot) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell42 pos b

@[simp] theorem Walk.opt43 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[43]?.getD 0 = ((pos==0).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell43 pos b

@[simp] theorem Walk.opt44 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[44]?.getD 0 = ((pos+1==w.kind.bytes.length).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell44 pos b

@[simp] theorem Walk.opt45 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[45]?.getD 0 = (((pos+1==w.kind.bytes.length) && w.final).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell45 pos b

@[simp] theorem Walk.opt46 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[46]?.getD 0 = ((!w.value.isSome).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell46 pos b

@[simp] theorem Walk.opt47 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[47]?.getD 0 = (((w.kind.code==3) && !(pos==0)).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell47 pos b

@[simp] theorem Walk.opt48 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[48]?.getD 0 = (((pos+1==w.kind.bytes.length) && w.value.isSome && (w.tau==0) && (w.kind.code==1)).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell48 pos b

@[simp] theorem Walk.opt49 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[49]?.getD 0 = ((w.tau==0).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell49 pos b

@[simp] theorem Walk.opt50 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[50]?.getD 0 = (w.lastMain.toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell50 pos b

@[simp] theorem Walk.opt51 (w : Walk) (pos : Nat) (b : UInt8) :
    (w.row pos b)[51]?.getD 0 = (((pos+1==w.kind.bytes.length) && w.value.isSome).toNat) := by
  simpa only [List.getD_eq_getElem?_getD] using w.cell51 pos b

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
