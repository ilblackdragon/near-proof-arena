import ZkFormal.NearV3.Render.Ups.CompactExtract.PlanRows
import ZkFormal.NearV3.Extract.Ups.ByteRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
theorem memBytes {e : Expr} (h : e∈cBytes) : e∈compactConstraints := by simp [compactConstraints,h]
theorem memDigest {e : Expr} (h : e∈cDigest) : e∈compactConstraints := by simp [compactConstraints,h]
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P)
include ok hC

theorem cpTAG (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sTAG = 1) :
    ((C cp : Nat) : Fp) = ((C kRDB : Nat) : Fp) + ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kRBR : Nat) : Fp) + ((C kRBI : Nat) : Fp) + ((C kPT : Nat) : Fp) := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sTAG) (sub (c cp) (sumc [kRDB, kRDE, kRLP, kRBR, kRBI, kPT]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpHPL (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) :
    ((C cp : Nat) : Fp) = ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kPT : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (.add (c sHPL) (c sHPF)) (sub (c cp) (sumc [kRDE, kRLP, kPT]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpHPF (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    ((C cp : Nat) : Fp) = ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kPT : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (.add (c sHPL) (c sHPF)) (sub (c cp) (sumc [kRDE, kRLP, kPT]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpKEY (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sKEY = 1) :
    ((C cp : Nat) : Fp) = ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sKEY) (sub (c cp) (sumc [kRDE, kRLP, kMVL, kMVE]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpVLEN (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sVLEN = 1) :
    ((C cp : Nat) : Fp) = ((C vcp : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpVH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sVH = 1) :
    ((C cp : Nat) : Fp) = ((C vcp : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpBM (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sBM = 1) :
    ((C cp : Nat) : Fp) = ((C kRDB : Nat) : Fp) + ((C kRBR : Nat) : Fp) + ((C kRBV : Nat) : Fp) + ((C kRBI : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sBM) (sub (c cp) (sumc [kRDB, kRBR, kRBV, kRBI]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpCH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sCH = 1) :
    ((C cp : Nat) : Fp) = 1 - ((C wfr : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sCH) (sub (c cp) (not (c wfr)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem cpMEM (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sMEM = 1) :
    ((C cp : Nat) : Fp) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sCH = 0 := by omega
  have f := fact ok (e := .mul (c sMEM) (c cp)) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem hplStep (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fe = 0) :
    ((D qha : Nat) : Fp) = ((C qha : Nat) : Fp) + ((D qhs : Nat) : Fp) * ((D b : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (not (c fe)) (sub (n qha) (.add (c qha) (.mul (n qhs) (n b))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem hplScale (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fe = 0) :
    ((D qhs : Nat) : Fp) = 256 * ((C qhs : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (not (c fe)) (sub (n qhs) (smul 256 (c qhs)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem hplEnd (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fe = 1) :
    ((C qha : Nat) : Fp) = ((C qhk : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (c fe) (sub (c qha) (c qhk))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem hplTop (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fe = 1) :
    ((C b : Nat) : Fp) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (c fe) (c b)) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem hplNibble (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) :
    ((C b : Nat) : Fp) = 16 * (((2 ^ 0 : Nat) : Fp) * ((C (hb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (hb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (hb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (hb 3) : Nat) : Fp)) + (((2 ^ 0 : Nat) : Fp) * ((C (lb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (lb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (lb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (lb 3) : Nat) : Fp)) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sHPL) (sub (c b) (.add (smul 16 hiE) loE))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bCopy  (h0 : C cp = 1) :
    ((C b : Nat) : Fp) = ((C rb : Nat) : Fp) + ((C sBM : Nat) : Fp) * (((C fs : Nat) : Fp) * ((C ba0 : Nat) : Fp) + (1 - ((C fs : Nat) : Fp)) * ((C ba1 : Nat) : Fp)) := by

  have f := fact ok (e := .mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0)) (.mul (not (c fs)) (c ba1))))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, cast0, cast1] at f
  grind

theorem bTAG (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sTAG = 1) :
    ((C b : Nat) : Fp) = ((C qtb1 : Nat) : Fp) + 2 * ((C qtb2 : Nat) : Fp) + 3 * ((C qte : Nat) : Fp) := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (c sTAG) (sub (c b) tagE)) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPL0 (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fs = 1) :
    ((C qha : Nat) : Fp) = ((C b : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (c fs) (sub (c qha) (c b))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPLr (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fs = 1) :
    ((C qhs : Nat) : Fp) = 1 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPL) (c fs) (sub (c qhs) (k 1))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPFm (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C b : Nat) : Fp) - (32 * ((C qtl : Nat) : Fp) + 16 * ((C qodd : Nat) : Fp) + ((C qodd : Nat) : Fp) * (((2 ^ 0 : Nat) : Fp) * ((C (lb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (lb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (lb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (lb 3) : Nat) : Fp)))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (.mul (c sHPF) kM) (sub (c b) (sum [smul 32 (c qtl), smul 16 (c qodd), .mul (c qodd) loE]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPFn (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    ((C kNLF : Nat) : Fp) * (((C b : Nat) : Fp) - (32 + 31 * ((C ts1 : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPF) (c kNLF) (sub (c b) (.add (k 32) (smul 31 (c ts1))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPFw (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    ((C kWEX : Nat) : Fp) * (((C b : Nat) : Fp) - (16 * (((C ts2 : Nat) : Fp) * ((C ti1 : Nat) : Fp)) + 31 * (((C ts3 : Nat) : Fp) * ((C ti1 : Nat) : Fp)))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPF) (c kWEX) (sub (c b) (.add (smul 16 (.mul (c ts2) (c ti1))) (smul 31 (.mul (c ts3) (c ti1)))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bKEYw (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sKEY = 1) :
    ((C kWEX : Nat) : Fp) * (((C b : Nat) : Fp) - 15) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sKEY) (c kWEX) (sub (c b) (k 15))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bHPFp (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    ((C kPT : Nat) : Fp) * ((C b : Nat) : Fp) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPF) (c kPT) (c b)) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bVLEN (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sVLEN = 1) (h1 : C cp = 0) :
    ((C b : Nat) : Fp) = ((C (LR 0) : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sVLEN) (not (c cp)) (sub (c b) (c (LR 0)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem bSPB (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sBM = 1) :
    ((C kSPB : Nat) : Fp) * (((C b : Nat) : Fp) - (((C fs : Nat) : Fp) * ((C bmL : Nat) : Fp) + (1 - ((C fs : Nat) : Fp)) * ((C bmH : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c kSPB) (c sBM) (sub (c b) (.add (.mul (c fs) (c bmL)) (.mul (not (c fs)) (c bmH))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rTAG (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sTAG = 1) :
    ((((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) + ((C xcp : Nat) : Fp)) * (((C rb : Nat) : Fp) - (16 * (((2 ^ 0 : Nat) : Fp) * ((C (hb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (hb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (hb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (hb 3) : Nat) : Fp)) + (((2 ^ 0 : Nat) : Fp) * ((C (lb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (lb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (lb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (lb 3) : Nat) : Fp)))) = 0 := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (.add kM (c xcp)) (c sTAG) (sub (c rb) (.add (smul 16 hiE) loE))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rTAGh (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sTAG = 1) :
    ((((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) + ((C xcp : Nat) : Fp)) * ((((2 ^ 0 : Nat) : Fp) * ((C (hb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (hb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (hb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (hb 3) : Nat) : Fp)) - (2 * ((C qtl : Nat) : Fp) + ((C podd : Nat) : Fp))) = 0 := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (.add kM (c xcp)) (c sTAG) (sub hiE (.add (smul 2 (c qtl)) (c podd)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rHPF (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPF = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C rb : Nat) : Fp) - (16 * (((2 ^ 0 : Nat) : Fp) * ((C (hb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (hb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (hb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (hb 3) : Nat) : Fp)) + (((2 ^ 0 : Nat) : Fp) * ((C (lb 0) : Nat) : Fp) + ((2 ^ 1 : Nat) : Fp) * ((C (lb 1) : Nat) : Fp) + ((2 ^ 2 : Nat) : Fp) * ((C (lb 2) : Nat) : Fp) + ((2 ^ 3 : Nat) : Fp) * ((C (lb 3) : Nat) : Fp)))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sHPF) kM (sub (c rb) (.add (smul 16 hiE) loE))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rHPL (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sHPL = 1) (h1 : C fs = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C plen : Nat) : Fp) - (45 + 4 * ((C qtl : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (mul3 (c sHPL) (c fs) kM) (sub (c plen) (sum [k 45, smul 4 (c qtl), c phk]))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rBM (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sBM = 1) (h1 : C fs = 1) :
    ((C xcp : Nat) : Fp) * (((C plen : Nat) : Fp) - (45 + 4 * ((C qtl : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c sBM) (c fs) (.mul (c xcp) (sub (c plen) (sum [k 45, smul 4 (c qtl), c phk])))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rRBV (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C sTAG = 1) :
    ((C kRBV : Nat) : Fp) * (((C rb : Nat) : Fp) - 1) = 0 := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c kRBV) (c sTAG) (sub (c rb) (k 1))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem rVLEN (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sVLEN = 1) :
    ((C rb : Nat) : Fp) = ((C (SR 0) : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c sVLEN) (sub (c rb) (c (SR 0)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMEM (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sMEM = 1) :
    ((C spos : Nat) : Fp) + 8 = ((C plen : Nat) : Fp) + ((C idx : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sCH = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c sMEM) (sub (.add (c spos) (k 8)) (.add (c plen) (c idx)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pDir  (h0 : C rd = 1) :
    (((C kRDB : Nat) : Fp) + ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kRBR : Nat) : Fp) + ((C kPT : Nat) : Fp)) * (((C spos : Nat) : Fp) - ((C qpos : Nat) : Fp)) = 0 := by

  have f := fact ok (e := mul3 (c rd) (sumc [kRDB, kRDE, kRLP, kRBR, kPT]) (sub (c spos) (c qpos))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, cast0, cast1] at f
  grind

theorem pRBV  (h0 : C rd = 1) :
    ((C kRBV : Nat) : Fp) * (((C spos : Nat) : Fp) + 36 * ((C aft : Nat) : Fp) - ((C qpos : Nat) : Fp)) = 0 := by

  have f := fact ok (e := mul3 (c rd) (c kRBV) (sub (.add (c spos) (smul 36 (c aft))) (c qpos))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, cast0, cast1] at f
  grind

theorem pRBI  (h0 : C rd = 1) :
    ((C kRBI : Nat) : Fp) * (((C spos : Nat) : Fp) + 32 * ((C aft : Nat) : Fp) - ((C qpos : Nat) : Fp)) = 0 := by

  have f := fact ok (e := mul3 (c rd) (c kRBI) (sub (.add (c spos) (smul 32 (c aft))) (c qpos))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, cast0, cast1] at f
  grind

theorem pMT (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sTAG = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) - 5) = 0 := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (c sTAG) (sub (c spos) (k 5)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sHPL = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) - 1) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (c sHPL) (sub (c spos) (k 1)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMKHPF (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sHPF = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMKKEY (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sKEY = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMKVLEN (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sVLEN = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMKVH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sVH = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pMKCH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sCH = 1) :
    (((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp)) * (((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pST (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sTAG = 1) :
    ((C kSPB : Nat) : Fp) * (((C spos : Nat) : Fp) - 5) = 0 := by
  have z0 : C sHPL = 0 := by omega
  have z1 : C sHPF = 0 := by omega
  have z2 : C sKEY = 0 := by omega
  have z3 : C sVLEN = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c kSPB) (.mul (c sTAG) (sub (c spos) (k 5)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pSB (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sBM = 1) :
    ((C kSPB : Nat) : Fp) * (((C spos : Nat) : Fp) - 1) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c kSPB) (.mul (c sBM) (sub (c spos) (k 1)))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pSVVLEN (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sVLEN = 1) :
    ((C kSPB : Nat) : Fp) * (((C spos : Nat) : Fp) + 45 - (((C plen : Nat) : Fp) + ((C qpos : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVH = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c kSPB) (.mul (.add (c sVLEN) (c sVH)) (sub (.add (c spos) (k 45)) (.add (c plen) (c qpos))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pSVVH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sVH = 1) :
    ((C kSPB : Nat) : Fp) * (((C spos : Nat) : Fp) + 45 - (((C plen : Nat) : Fp) + ((C qpos : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c kSPB) (.mul (.add (c sVLEN) (c sVH)) (sub (.add (c spos) (k 45)) (.add (c plen) (c qpos))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem pSC (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C rd = 1) (h1 : C sCH = 1) :
    ((C kSPB : Nat) : Fp) * (((C spos : Nat) : Fp) + 40 - (((C plen : Nat) : Fp) + ((C idx : Nat) : Fp))) = 0 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c rd) (c kSPB) (.mul (c sCH) (sub (.add (c spos) (k 40)) (.add (c plen) (c idx))))) (memBytes (by simp [cBytes]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dVH (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sVH = 1) :
    ((C dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((C tau : Nat) : Fp) + 0) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c gD) (c sVH) (sub (c dI) (upsId (k 0)))) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dVHl (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sVH = 1) :
    ((C dL : Nat) : Fp) = ((C L0 : Nat) : Fp) + (((256 : Nat) : Fp) * ((C L1 : Nat) : Fp) + ((65536 : Nat) : Fp) * ((C L2 : Nat) : Fp)) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sBM = 0 := by omega
  have z6 : C sCH = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := mul3 (c gD) (c sVH) (sub (c dL) Lexpr)) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dCHn (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sCH = 1) (h2 : C wn = 1) :
    ((C dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((C tau : Nat) : Fp) + (((C j : Nat) : Fp) - 1)) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dI) (upsId (sub (c j) (k 1))))) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, h2, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dCHnl (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sCH = 1) (h2 : C wn = 1) :
    ((C dL : Nat) : Fp) = 50 := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dL) (k 50))) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, h2, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dCHm (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sCH = 1) (h2 : C wn = 0) :
    ((C dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((C tau : Nat) : Fp) + ((C jm : Nat) : Fp)) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dI) (upsId (c jm)))) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, h2, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

theorem dCHml (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) (h0 : C gD = 1) (h1 : C sCH = 1) (h2 : C wn = 0) :
    ((C dL : Nat) : Fp) = ((C clen : Nat) : Fp) := by
  have z0 : C sTAG = 0 := by omega
  have z1 : C sHPL = 0 := by omega
  have z2 : C sHPF = 0 := by omega
  have z3 : C sKEY = 0 := by omega
  have z4 : C sVLEN = 0 := by omega
  have z5 : C sVH = 0 := by omega
  have z6 : C sBM = 0 := by omega
  have z7 : C sMEM = 0 := by omega
  have f := fact ok (e := .mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dL) (c clen))) (memDigest (by simp [cDigest]))
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, h0, h1, h2, z0, z1, z2, z3, z4, z5, z6, z7, cast0, cast1] at f
  grind

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
