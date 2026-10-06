import ZkFormal.NearV3.Render.Node.Facts

/-!
# ZkFormal.NearV3.Render.Node.TRow — the bus traffic of one row, from its cells

`rowN c b sd`: the messages (naturals) of a row with cells `c`, one piece per interaction of
`NodeV3.interactions` (in order).  `rowT_eq`: the row's `rowTraffic` is their image in `Fp`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

def gt (x : Nat) (m : ZkFormal.Near.Msg) : List ZkFormal.Near.Msg := if x = 1 then [m] else []

def bmN (c : Nat → Nat) : Nat := ((List.range 16).map fun i => 2 ^ i * c (37 + i)).sum

def regN (c : Nat → Nat) (o : Nat) : List Nat := (List.range 32).map fun i => c (o + i)

/-- The messages of a row with cells `c` on bus `b`, side `sd`. -/
def rowN0 (c : Nat → Nat) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (if B_BYTES = b ∧ true = sd then gt (c 0) [msgId K_NPRE (c 4), c 5, c 8] else []) ++
  (if B_BYTES = b ∧ true = sd then gt (c 0) [msgId K_NPOST (c 4), c 5, c 9] else []) ++
  (if B_DIGEST = b ∧ false = sd then gt (c 142) ([c 140, c 141] ++ regN c 72) else []) ++
  (if B_DIGEST = b ∧ false = sd then gt (c 183) ([c 140 + 1, c 141] ++ regN c 104) else []) ++
  (if B_PARENT = b ∧ true = sd then gt (c 143) [c 137, c 163, c 7 + 1, c 138, c 154] else []) ++
  (if B_PARENT = b ∧ false = sd then gt (c 1) [c 4, c 163, c 7, c 6, c 153] else []) ++
  (if B_VPARENT = b ∧ true = sd then gt (c 142 - c 143) [c 165, c 166] else []) ++
  (if B_EDGE = b ∧ true = sd then gt (c 145) [c 4, c 146, c 147, c 148, c 149, c 174, 0] else []) ++
  (if B_EDGE = b ∧ false = sd then gt (c 145) [c 4, c 146, c 147, c 148, c 149, c 174, c 150] else []) ++
  (if B_EDGE = b ∧ true = sd then gt (c 160) [c 4, c 176, c 177, c 161, c 162, c 175, 0] else []) ++
  (if B_EDGE = b ∧ false = sd then gt (c 160) [c 4, c 176, c 177, c 161, c 162, c 175, c 151] else []) ++
  (if B_BMAP = b ∧ true = sd then gt (c 184) [c 4, bmN c, c 13, 0] else []) ++
  (if B_BMAP = b ∧ false = sd then gt (c 184) [c 4, bmN c, c 13, c 173] else []) ++
  (if B_DIGS = b ∧ true = sd then gt (c 181) [c 182, c 163, c 23, c 8] else []) ++
  (if B_DUP = b ∧ false = sd then gt (c 144) [msgId K_NPRE (c 4), c 172] else []) ++
  (if B_ENT = b ∧ true = sd then gt (c 171) [msgId K_NPRE (c 4), c 6, c 5, c 8] else []) ++
  (if B_ENT = b ∧ false = sd then gt (c 170) [c 172, c 6, c 5, c 8] else []) ++
  (if B_SIZE = b ∧ true = sd then gt (c 3) [0, c 152] else [])

/-- The `UPB` pieces (M7c). -/
def rowNU (c : Nat → Nat) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (if B_UPB = b ∧ true = sd then gt (c 0) [msgId K_NPOST (c 4), c 5, c 9, c 6, c 7, c 137, 0] else []) ++
  (if B_UPB = b ∧ false = sd then gt (c 0) [msgId K_NPOST (c 4), c 5, c 9, c 6, c 7, c 137, c 185] else [])

/-- All pieces, in the order of `NodeV3.interactions`. -/
def rowN (c : Nat → Nat) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg := rowN0 c b sd ++ rowNU c b sd

theorem ofNat_one_iff {v : Nat} (h : v ≤ 1) : Fp.ofNat v = 1 ↔ v = 1 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> decide

theorem piece {P : Prop} [Decidable P] {e : Fp} {x : Nat} (hx : x ≤ 1) (he : e = Fp.ofNat x) {l : List Fp}
    {m : ZkFormal.Near.Msg} (hm : P → x = 1 → l = Msg.toFp m) :
    (if P then List.replicate (if e = 1 then 1 else 0) l else []) = (if P then gt x m else []).map Msg.toFp := by
  by_cases hP : P
  · simp only [hP, if_true, he, ofNat_one_iff hx, gt]
    by_cases h1 : x = 1
    · simp [h1, hm hP h1]
    · simp [h1]
  · simp [hP]

theorem ofNat_sub' {a b : Nat} (h : b ≤ a) : Fp.ofNat a - Fp.ofNat b = Fp.ofNat (a - b) := by
  have : Fp.ofNat a = Fp.ofNat (a - b) + Fp.ofNat b := by rw [ofNat_add']; congr 1; omega
  rw [this]; grind

theorem mid_eq (kk x : Nat) : (kk : Fp) + ((16 : Nat) : Fp) * Fp.ofNat x = Fp.ofNat (msgId kk x) := by
  unfold msgId; rw [natCast_eq, natCast_eq, ofNat_mul', ofNat_add']

theorem multNat_one' {g : Expr} {msg : List Expr} {bus : Nat} {s : Bool} {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} :
    Interaction.multNat ⟨bus, [g], msg, s⟩ tr t r pub = if g.eval tr t r pub = 1 then 1 else 0 := by
  simp [Interaction.multNat, Interaction.multNat.go]

set_option maxHeartbeats 40000000 in
/-- **The row's traffic from its cells.** -/
theorem rowT_eq {tr : Trace Fp} {tt q : Nat} {pub : List Fp} (c : Nat → Nat)
    (hc : ∀ x, x < 186 → tr.cell tt q x = Fp.ofNat (c x))
    (hg : ∀ x, x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 142 ∨ x = 143 ∨ x = 144 ∨ x = 145 ∨ x = 160 ∨ x = 170 ∨ x = 171 ∨
      x = 181 ∨ x = 183 ∨ x = 184 → c x ≤ 1)
    (hvs : c 143 ≤ c 142 ∧ c 142 - c 143 ≤ 1) (b : Nat) (sd : Bool) :
    rowTraffic NodeV3.interactions tr tt q pub b sd = (rowN c b sd).map Msg.toFp := by
  simp only [rowTraffic, NodeV3.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    multNat_one', Interaction.msgVal, rowN, rowN0, rowNU, List.map_append, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  have hcc : ∀ x, x < 186 → (Dsl.c x).eval tr tt q pub = Fp.ofNat (c x) := fun x hx => by rw [eval_c, hc x hx]
  have hreg : ∀ o, o + 32 ≤ 185 → ((List.range 32).map fun i => (Dsl.c (o + i)).eval tr tt q pub) =
      (regN c o).map Fp.ofNat := by
    intro o ho
    simp only [regN, List.map_map]
    apply List.map_congr_left; intro i hi
    have := List.mem_range.1 hi
    simp only [Function.comp_apply]; exact hcc _ (by omega)
  have hbm : NodeV3.bmE.eval tr tt q pub = Fp.ofNat (bmN c) := by
    simp only [NodeV3.bmE, bits, Nat.zero_add]
    rw [WalkProof.evsum 16 _ (fun i => 2 ^ i * c (37 + i)) (fun j hj => by
      rw [eval_smul, hcc _ (by simp only [NodeV3.bm]; omega), natCast_mul, natCast_eq, natCast_eq]; rfl)]
    rfl
  have hmid : ∀ kk, (mid kk (Dsl.c 4)).eval tr tt q pub = Fp.ofNat (msgId kk (c 4)) := by
    intro kk; rw [eval_mid, hcc 4 (by decide), mid_eq]
  try simp only [List.append_assoc]
  have g := hg
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_
    (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))))))))))))))))))
  all_goals first
    | (refine piece ?_ ?_ ?_
       · exact g _ (by decide)
       · exact hcc _ (by decide)
       intro _ _
       try simp only [Msg.toFp, List.map_cons, List.map_nil, List.map_append, hmid, hreg 72 (by decide),
         hreg 104 (by decide), hbm, eval_c, eval_add, eval_k, NodeV3.edgeA, NodeV3.edgeB, NodeV3.bmapMsg,
         NodeV3.entMsg, NodeV3.nid, NodeV3.pos, NodeV3.b, NodeV3.pb, NodeV3.dI, NodeV3.dL, NodeV3.reg, NodeV3.preg,
         NodeV3.cid, NodeV3.tau, NodeV3.depth, NodeV3.clen, NodeV3.cres, NodeV3.len, NodeV3.res, NodeV3.vid,
         NodeV3.vlen, NodeV3.aI, NodeV3.aS, NodeV3.aN, NodeV3.aJ, NodeV3.aK, NodeV3.mA, NodeV3.mB, NodeV3.bI,
         NodeV3.bS, NodeV3.bN, NodeV3.bJ, NodeV3.bK, NodeV3.tb2, NodeV3.mBm, NodeV3.dE, NodeV3.idx, NodeV3.repE,
         NodeV3.sz, NodeV3.upbMsg, NodeV3.mU, hcc _ (show (4 : Nat) < 186 by decide)]
       try simp only [hc 5 (by decide), hc 8 (by decide), hc 9 (by decide), hc 140 (by decide), hc 141 (by decide), hc 137 (by decide), hc 163 (by decide), hc 7 (by decide), hc 138 (by decide), hc 154 (by decide), hc 6 (by decide), hc 153 (by decide), hc 165 (by decide), hc 166 (by decide), hc 146 (by decide), hc 147 (by decide), hc 148 (by decide), hc 149 (by decide), hc 174 (by decide), hc 150 (by decide), hc 176 (by decide), hc 177 (by decide), hc 161 (by decide), hc 162 (by decide), hc 175 (by decide), hc 151 (by decide), hc 13 (by decide), hc 173 (by decide), hc 182 (by decide), hc 23 (by decide), hc 172 (by decide), hc 152 (by decide), hc 185 (by decide), natCast_eq, ofNat_add', List.map_map, Function.comp_def]
       try simp only [hreg 72 (by decide), hreg 104 (by decide)]
       try rfl)
    | (refine piece hvs.2 ?_ ?_
       · simp only [NodeV3.valStart, eval_sub, hcc _ (by decide : (142 : Nat) < 186),
           hcc _ (by decide : (143 : Nat) < 186), NodeV3.gD, NodeV3.gP]
         rw [ofNat_sub' hvs.1]
       intro _ _
       simp only [Msg.toFp, List.map_cons, List.map_nil, eval_c, NodeV3.vid, NodeV3.vlen,
         hcc _ (by decide : (165 : Nat) < 186), hcc _ (by decide : (166 : Nat) < 186)])

end NodeGen3

end ZkFormal.NearV3.Render
