# Generates ZkFormal/NearV3/Extract/Ups/ByteRows.lean: byte provenance row facts of a node-part row.
# Each clause: (name, premises [(col, val)], constraint Lean expr, conclusion Lean prop, mem tag)
F = lambda x: f"(C {x} : Fp)"   # shorthand used in conclusions; expands to ((C x : Nat) : Fp)
def cast(x): return f"((C ({x}) : Nat) : Fp)" if " " in x else f"((C {x} : Nat) : Fp)"
def ncast(x): return f"((D {x} : Nat) : Fp)"
K = lambda *xs: " + ".join(cast(x) for x in xs)
loE = "(" + " + ".join(f"((2 ^ {i} : Nat) : Fp) * {cast(f'lb {i}')}" for i in range(4)) + ")"
hiE = "(" + " + ".join(f"((2 ^ {i} : Nat) : Fp) * {cast(f'hb {i}')}" for i in range(4)) + ")"
kM = f"({K('kMVL','kMVE')})"
cl = []
def add(name, prem, e, concl, mem="Bytes"): cl.append((name, prem, e, concl, mem))
# copies
add("cpTAG", [("sTAG",1)], ".mul (c sTAG) (sub (c cp) (sumc [kRDB, kRDE, kRLP, kRBR, kRBI, kPT]))",
    f"{cast('cp')} = {K('kRDB','kRDE','kRLP','kRBR','kRBI','kPT')}")
add("cpHPL", [("sHPL",1)], ".mul (.add (c sHPL) (c sHPF)) (sub (c cp) (sumc [kRDE, kRLP, kPT]))",
    f"{cast('cp')} = {K('kRDE','kRLP','kPT')}")
add("cpHPF", [("sHPF",1)], ".mul (.add (c sHPL) (c sHPF)) (sub (c cp) (sumc [kRDE, kRLP, kPT]))",
    f"{cast('cp')} = {K('kRDE','kRLP','kPT')}")
add("cpKEY", [("sKEY",1)], ".mul (c sKEY) (sub (c cp) (sumc [kRDE, kRLP, kMVL, kMVE]))",
    f"{cast('cp')} = {K('kRDE','kRLP','kMVL','kMVE')}")
add("cpVLEN", [("sVLEN",1)], ".mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp))", f"{cast('cp')} = {cast('vcp')}")
add("cpVH", [("sVH",1)], ".mul (.add (c sVLEN) (c sVH)) (sub (c cp) (c vcp))", f"{cast('cp')} = {cast('vcp')}")
add("cpBM", [("sBM",1)], ".mul (c sBM) (sub (c cp) (sumc [kRDB, kRBR, kRBV, kRBI]))",
    f"{cast('cp')} = {K('kRDB','kRBR','kRBV','kRBI')}")
add("cpCH", [("sCH",1)], ".mul (c sCH) (sub (c cp) (not (c wfr)))", f"{cast('cp')} = 1 - {cast('wfr')}")
add("cpMEM", [("sMEM",1)], ".mul (c sMEM) (c cp)", f"{cast('cp')} = 0")
# Four-byte header accumulation; range checks are supplied by byte lookups.
add("hplStep", [("sHPL",1),("fe",0)],
    "mul3 (c sHPL) (not (c fe)) (sub (n qha) (.add (c qha) (.mul (n qhs) (n b))))",
    f"{ncast('qha')} = {cast('qha')} + {ncast('qhs')} * {ncast('b')}")
add("hplScale", [("sHPL",1),("fe",0)],
    "mul3 (c sHPL) (not (c fe)) (sub (n qhs) (smul 256 (c qhs)))",
    f"{ncast('qhs')} = 256 * {cast('qhs')}")
add("hplEnd", [("sHPL",1),("fe",1)],
    "mul3 (c sHPL) (c fe) (sub (c qha) (c qhk))", f"{cast('qha')} = {cast('qhk')}")
add("hplTop", [("sHPL",1),("fe",1)],
    "mul3 (c sHPL) (c fe) (c b)", f"{cast('b')} = 0")
add("hplNibble", [("sHPL",1)],
    ".mul (c sHPL) (sub (c b) (.add (smul 16 hiE) loE))",
    f"{cast('b')} = 16 * {hiE} + {loE}")
# copied byte
add("bCopy", [("cp",1)], ".mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0)) (.mul (not (c fs)) (c ba1))))))",
    f"{cast('b')} = {cast('rb')} + {cast('sBM')} * ({cast('fs')} * {cast('ba0')} + (1 - {cast('fs')}) * {cast('ba1')})")
# grammar bytes
add("bTAG", [("sTAG",1)], ".mul (c sTAG) (sub (c b) tagE)",
    f"{cast('b')} = {cast('qtb1')} + 2 * {cast('qtb2')} + 3 * {cast('qte')}")
add("bHPL0", [("sHPL",1),("fs",1)], "mul3 (c sHPL) (c fs) (sub (c qha) (c b))", f"{cast('qha')} = {cast('b')}")
add("bHPLr", [("sHPL",1),("fs",1)], "mul3 (c sHPL) (c fs) (sub (c qhs) (k 1))", f"{cast('qhs')} = 1")
add("bHPFm", [("sHPF",1)], ".mul (.mul (c sHPF) kM) (sub (c b) (sum [smul 32 (c qtl), smul 16 (c qodd), .mul (c qodd) loE]))",
    f"{kM} * ({cast('b')} - (32 * {cast('qtl')} + 16 * {cast('qodd')} + {cast('qodd')} * {loE})) = 0")
add("bHPFn", [("sHPF",1)], "mul3 (c sHPF) (c kNLF) (sub (c b) (.add (k 32) (smul 31 (c ts1))))",
    f"{cast('kNLF')} * ({cast('b')} - (32 + 31 * {cast('ts1')})) = 0")
add("bHPFw", [("sHPF",1)], "mul3 (c sHPF) (c kWEX) (sub (c b) (.add (smul 16 (.mul (c ts2) (c ti1))) (smul 31 (.mul (c ts3) (c ti1)))))",
    f"{cast('kWEX')} * ({cast('b')} - (16 * ({cast('ts2')} * {cast('ti1')}) + 31 * ({cast('ts3')} * {cast('ti1')}))) = 0")
add("bKEYw", [("sKEY",1)], "mul3 (c sKEY) (c kWEX) (sub (c b) (k 15))", f"{cast('kWEX')} * ({cast('b')} - 15) = 0")
add("bHPFp", [("sHPF",1)], "mul3 (c sHPF) (c kPT) (c b)", f"{cast('kPT')} * {cast('b')} = 0")
add("bVLEN", [("sVLEN",1),("cp",0)], "mul3 (c sVLEN) (not (c cp)) (sub (c b) (c (LR 0)))", f"{cast('b')} = {cast('LR 0')}")
add("bSPB", [("sBM",1)], "mul3 (c kSPB) (c sBM) (sub (c b) (.add (.mul (c fs) (c bmL)) (.mul (not (c fs)) (c bmH))))",
    f"{cast('kSPB')} * ({cast('b')} - ({cast('fs')} * {cast('bmL')} + (1 - {cast('fs')}) * {cast('bmH')})) = 0")
# header reads
add("rTAG", [("sTAG",1)], "mul3 (.add kM (c xcp)) (c sTAG) (sub (c rb) (.add (smul 16 hiE) loE))",
    f"({kM} + {cast('xcp')}) * ({cast('rb')} - (16 * {hiE} + {loE})) = 0")
add("rTAGh", [("sTAG",1)], "mul3 (.add kM (c xcp)) (c sTAG) (sub hiE (.add (smul 2 (c qtl)) (c podd)))",
    f"({kM} + {cast('xcp')}) * ({hiE} - (2 * {cast('qtl')} + {cast('podd')})) = 0")
add("rHPF", [("sHPF",1)], "mul3 (c sHPF) kM (sub (c rb) (.add (smul 16 hiE) loE))",
    f"{kM} * ({cast('rb')} - (16 * {hiE} + {loE})) = 0")
add("rHPL", [("sHPL",1),("fs",1)], ".mul (mul3 (c sHPL) (c fs) kM) (sub (c plen) (sum [k 45, smul 4 (c qtl), c phk]))",
    f"{kM} * ({cast('plen')} - (45 + 4 * {cast('qtl')} + {cast('phk')})) = 0")
add("rBM", [("sBM",1),("fs",1)], "mul3 (c sBM) (c fs) (.mul (c xcp) (sub (c plen) (sum [k 45, smul 4 (c qtl), c phk])))",
    f"{cast('xcp')} * ({cast('plen')} - (45 + 4 * {cast('qtl')} + {cast('phk')})) = 0")
add("rRBV", [("sTAG",1)], "mul3 (c kRBV) (c sTAG) (sub (c rb) (k 1))", f"{cast('kRBV')} * ({cast('rb')} - 1) = 0")
add("rVLEN", [("rd",1),("sVLEN",1)], "mul3 (c rd) (c sVLEN) (sub (c rb) (c (SR 0)))", f"{cast('rb')} = {cast('SR 0')}")
# read positions
add("pMEM", [("rd",1),("sMEM",1)], "mul3 (c rd) (c sMEM) (sub (.add (c spos) (k 8)) (.add (c plen) (c idx)))",
    f"{cast('spos')} + 8 = {cast('plen')} + {cast('idx')}")
add("pDir", [("rd",1)], "mul3 (c rd) (sumc [kRDB, kRDE, kRLP, kRBR, kPT]) (sub (c spos) (c qpos))",
    f"({K('kRDB','kRDE','kRLP','kRBR','kPT')}) * ({cast('spos')} - {cast('qpos')}) = 0")
add("pRBV", [("rd",1)], "mul3 (c rd) (c kRBV) (sub (.add (c spos) (smul 36 (c aft))) (c qpos))",
    f"{cast('kRBV')} * ({cast('spos')} + 36 * {cast('aft')} - {cast('qpos')}) = 0")
add("pRBI", [("rd",1)], "mul3 (c rd) (c kRBI) (sub (.add (c spos) (smul 32 (c aft))) (c qpos))",
    f"{cast('kRBI')} * ({cast('spos')} + 32 * {cast('aft')} - {cast('qpos')}) = 0")
add("pMT", [("rd",1),("sTAG",1)], "mul3 (c rd) kM (.mul (c sTAG) (sub (c spos) (k 5)))",
    f"{kM} * ({cast('spos')} - 5) = 0")
add("pMH", [("rd",1),("sHPL",1)], "mul3 (c rd) kM (.mul (c sHPL) (sub (c spos) (k 1)))",
    f"{kM} * ({cast('spos')} - 1) = 0")
for st in ["sHPF","sKEY","sVLEN","sVH","sCH"]:
    add("pMK"+st[1:], [("rd",1),(st,1)], "mul3 (c rd) kM (.mul (sumc [sHPF, sKEY, sVLEN, sVH, sCH]) (sub (.add (c spos) (c qhk)) (.add (c qpos) (c phk))))",
        f"{kM} * ({cast('spos')} + {cast('qhk')} - ({cast('qpos')} + {cast('phk')})) = 0")
add("pST", [("rd",1),("sTAG",1)], "mul3 (c rd) (c kSPB) (.mul (c sTAG) (sub (c spos) (k 5)))", f"{cast('kSPB')} * ({cast('spos')} - 5) = 0")
add("pSB", [("rd",1),("sBM",1)], "mul3 (c rd) (c kSPB) (.mul (c sBM) (sub (c spos) (k 1)))", f"{cast('kSPB')} * ({cast('spos')} - 1) = 0")
for st in ["sVLEN","sVH"]:
    add("pSV"+st[1:], [("rd",1),(st,1)], "mul3 (c rd) (c kSPB) (.mul (.add (c sVLEN) (c sVH)) (sub (.add (c spos) (k 45)) (.add (c plen) (c qpos))))",
        f"{cast('kSPB')} * ({cast('spos')} + 45 - ({cast('plen')} + {cast('qpos')})) = 0")
add("pSC", [("rd",1),("sCH",1)], "mul3 (c rd) (c kSPB) (.mul (c sCH) (sub (.add (c spos) (k 40)) (.add (c plen) (c idx))))",
    f"{cast('kSPB')} * ({cast('spos')} + 40 - ({cast('plen')} + {cast('idx')})) = 0")
# digest lookups (qb row): window starts
add("dVH", [("gD",1),("sVH",1)], "mul3 (c gD) (c sVH) (sub (c dI) (upsId (k 0)))",
    f"{cast('dI')} = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * {cast('tau')} + 0)", "Digest")
add("dVHl", [("gD",1),("sVH",1)], "mul3 (c gD) (c sVH) (sub (c dL) Lexpr)",
    f"{cast('dL')} = {cast('L0')} + (((256 : Nat) : Fp) * {cast('L1')} + ((65536 : Nat) : Fp) * {cast('L2')})", "Digest")
add("dCHn", [("gD",1),("sCH",1),("wn",1)], ".mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dI) (upsId (sub (c j) (k 1))))",
    f"{cast('dI')} = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * {cast('tau')} + ({cast('j')} - 1))", "Digest")
add("dCHnl", [("gD",1),("sCH",1),("wn",1)], ".mul (mul3 (c gD) (c sCH) (c wn)) (sub (c dL) (k 50))", f"{cast('dL')} = 50", "Digest")
add("dCHm", [("gD",1),("sCH",1),("wn",0)], ".mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dI) (upsId (c jm)))",
    f"{cast('dI')} = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * {cast('tau')} + {cast('jm')})", "Digest")
add("dCHml", [("gD",1),("sCH",1),("wn",0)], ".mul (mul3 (c gD) (c sCH) (not (c wn))) (sub (c dL) (c clen))", f"{cast('dL')} = {cast('clen')}", "Digest")

out = []
out.append('''import ZkFormal.NearV3.Extract.Ups.FieldRows

/-!
# ZkFormal.NearV3.Extract.Ups.ByteRows — byte provenance of a node-part row (generated)

Generated by `test/gen_ups_bytes.py` (run from `zk-formal/`) from `UpsV3.cBytes` / `cDigest`: for a row `C` (with successor `D`)
and the given row flags, each clause is the constraint with its row-flag factors evaluated,
stated in `Fp` (part constants such as the kinds are not yet known to be `0`/`1` here; the
part plan fixes them).  Clauses: which bytes are copies (`cp…`), the copied byte (`bCopy`),
fresh grammar bytes (`b…`), header reads (`r…`), read positions (`p…`) and the `DIGEST`
lookups of fresh windows (`d…`).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem memBytes {e : Expr} (h : e ∈ cBytes) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr h))

theorem memDigest {e : Expr} (h : e ∈ cDigest) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]; exact Or.inl (Or.inr h)

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P)
include ok hC
''')
for (name, prem, e, concl, mem) in cl:
    hyps = " ".join(f"(h{i} : C {x} = {v})" for i,(x,v) in enumerate(prem))
    # one-hot zeros: provide a OneHot-like hypothesis for state premises
    states = ["sTAG","sHPL","sHPF","sKEY","sVLEN","sVH","sBM","sCH","sMEM"]
    stp = [x for (x,v) in prem if x in states]
    oh = "(hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1)" if stp else ""
    rw = ", ".join(f"h{i}" for i in range(len(prem)))
    zs = ""
    if stp:
        st = stp[0]
        others = [x for x in states if x != st]
        zs = "\n".join(f"  have z{j} : C {o} = 0 := by omega" for j,o in enumerate(others))
        rw += ", " + ", ".join(f"z{j}" for j in range(len(others)))
    simpmem = f"mem{mem} (by simp [c{mem}])"
    out.append(f'''theorem {name} {oh} {hyps} :
    {concl} := by
{zs}
  have f := fact ok (e := {e}) ({simpmem})
  try simp only [kM, sumc, List.map_cons, List.map_nil, Dsl.sum, tagE, loE, hiE, bits, winFr, upsId, mid, Lexpr,
    List.range_succ, List.range_zero, List.map_append, List.nil_append, List.cons_append, List.singleton_append] at f
  uev_simp
  simp only [cast_ofNat, {rw}, cast0, cast1] at f
  grind
''')
out.append('''end

end ZkFormal.NearV3.UpsRows
''')
open('ZkFormal/NearV3/Extract/Ups/ByteRows.lean','w').write("\n".join(out))
print(len(cl))
