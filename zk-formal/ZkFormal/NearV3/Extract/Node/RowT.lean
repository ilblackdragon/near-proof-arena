import ZkFormal.NearV3.Extract.Node.Of

/-!
# ZkFormal.Near.Extract.NodeRowT — the messages of one node-table row, per bus
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- A single-bit gate: the message once if the gate is `1`. -/
def gate (x : Fp) (m : List Fp) : List (List Fp) := List.replicate (if x = 1 then 1 else 0) m

abbrev rowT (tr : Trace Fp) (pub : List Fp) (r b : Nat) (sd : Bool) : List (List Fp) :=
  rowTraffic NodeV3.interactions tr T_NODE r pub b sd

variable {tr : Trace Fp} {pub : List Fp}

theorem multNat_one (e : Expr) (r : Nat) :
    Interaction.multNat.go tr T_NODE r pub [e] 0 = if e.eval tr T_NODE r pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr T_NODE r pub = 1 <;> simp [h]

theorem gate_eq (x : Fp) (m : List Fp) : gate x m = if x = 1 then [m] else [] := by
  unfold gate; split <;> rfl

def regW (tr : Trace Fp) (r : Nat) (col : Nat → Nat) : List Fp := (List.range 32).map fun i => tr.cell T_NODE r (col i)

def edgeAV (tr : Trace Fp) (r : Nat) (u : Fp) : List Fp :=
  [tr.cell T_NODE r nid, tr.cell T_NODE r aI, tr.cell T_NODE r aS, tr.cell T_NODE r aN, tr.cell T_NODE r aJ,
    tr.cell T_NODE r aK, u]
def edgeBV (tr : Trace Fp) (r : Nat) (u : Fp) : List Fp :=
  [tr.cell T_NODE r nid, tr.cell T_NODE r bI, tr.cell T_NODE r bS, tr.cell T_NODE r bN, tr.cell T_NODE r bJ,
    tr.cell T_NODE r bK, u]

theorem rowT_bytes (r : Nat) :
    rowT tr pub r B_BYTES true =
      gate (tr.cell T_NODE r act) [(K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r pos, tr.cell T_NODE r b] ++
      gate (tr.cell T_NODE r act) [(K_NPOST : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r pos, tr.cell T_NODE r pb] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_bytesR (r : Nat) : rowT tr pub r B_BYTES false = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

theorem rowT_digest (r : Nat) :
    rowT tr pub r B_DIGEST false =
      gate (tr.cell T_NODE r gD) ([tr.cell T_NODE r dI, tr.cell T_NODE r dL] ++ regW tr r reg) ++
      gate (tr.cell T_NODE r gDp) ([tr.cell T_NODE r dI + ((1 : Nat) : Fp), tr.cell T_NODE r dL] ++ regW tr r preg) := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_digestS (r : Nat) : rowT tr pub r B_DIGEST true = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

theorem rowT_parentS (r : Nat) :
    rowT tr pub r B_PARENT true =
      gate (tr.cell T_NODE r gP) [tr.cell T_NODE r cid, tr.cell T_NODE r tau, tr.cell T_NODE r depth + ((1 : Nat) : Fp),
        tr.cell T_NODE r clen, tr.cell T_NODE r cres] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_parentR (r : Nat) :
    rowT tr pub r B_PARENT false =
      gate (tr.cell T_NODE r nf)
        [tr.cell T_NODE r nid, tr.cell T_NODE r tau, tr.cell T_NODE r depth, tr.cell T_NODE r len, tr.cell T_NODE r res] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_vparentS (r : Nat) :
    rowT tr pub r B_VPARENT true = gate (tr.cell T_NODE r gD - tr.cell T_NODE r gP) [tr.cell T_NODE r vid, tr.cell T_NODE r vlen] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_vparentR (r : Nat) : rowT tr pub r B_VPARENT false = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

theorem rowT_edgeS (r : Nat) :
    rowT tr pub r B_EDGE true = gate (tr.cell T_NODE r gA) (edgeAV tr r 0) ++ gate (tr.cell T_NODE r gB) (edgeBV tr r 0) := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_edgeR (r : Nat) :
    rowT tr pub r B_EDGE false = gate (tr.cell T_NODE r gA) (edgeAV tr r (tr.cell T_NODE r mA)) ++
      gate (tr.cell T_NODE r gB) (edgeBV tr r (tr.cell T_NODE r mB)) := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_bmapS (r : Nat) :
    rowT tr pub r B_BMAP true = gate (tr.cell T_NODE r gBm) [tr.cell T_NODE r nid, bmE.eval tr T_NODE r pub, tr.cell T_NODE r tb2, 0] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_bmapR (r : Nat) :
    rowT tr pub r B_BMAP false =
      gate (tr.cell T_NODE r gBm) [tr.cell T_NODE r nid, bmE.eval tr T_NODE r pub, tr.cell T_NODE r tb2, tr.cell T_NODE r mBm] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_digsS (r : Nat) :
    rowT tr pub r B_DIGS true = gate (tr.cell T_NODE r gS)
      [tr.cell T_NODE r dE, tr.cell T_NODE r tau, tr.cell T_NODE r idx, tr.cell T_NODE r b] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_digsR (r : Nat) : rowT tr pub r B_DIGS false = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

theorem rowT_dupR (r : Nat) :
    rowT tr pub r B_DUP false = gate (tr.cell T_NODE r gV)
      [(K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r repE] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_dupS (r : Nat) : rowT tr pub r B_DUP true = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

theorem rowT_entS (r : Nat) :
    rowT tr pub r B_ENT true = gate (tr.cell T_NODE r hd)
      [(K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r len, tr.cell T_NODE r pos, tr.cell T_NODE r b] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_entR (r : Nat) :
    rowT tr pub r B_ENT false = gate (tr.cell T_NODE r dup)
      [tr.cell T_NODE r repE, tr.cell T_NODE r len, tr.cell T_NODE r pos, tr.cell T_NODE r b] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_sizeS (r : Nat) :
    rowT tr pub r B_SIZE true = gate (tr.cell T_NODE r sumr) [0, tr.cell T_NODE r sz] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_sizeR (r : Nat) : rowT tr pub r B_SIZE false = [] := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB]

/-- `UPB` provider messages of a row (`u`: `0` sent, `mU` received). -/
def upbV (tr : Trace Fp) (r : Nat) (u : Fp) : List Fp :=
  [(K_NPOST : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r pos, tr.cell T_NODE r pb,
    tr.cell T_NODE r len, tr.cell T_NODE r depth, tr.cell T_NODE r cid, u]

theorem rowT_upbS (r : Nat) : rowT tr pub r B_UPB true = gate (tr.cell T_NODE r act) (upbV tr r 0) := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, upbV, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_upbR (r : Nat) :
    rowT tr pub r B_UPB false = gate (tr.cell T_NODE r act) (upbV tr r (tr.cell T_NODE r mU)) := by
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DIGS, B_SIZE, B_DUP, B_ENT, B_VPARENT, B_UPB, eval_mid, regW, edgeA, edgeB,
    edgeAV, edgeBV, bmapMsg, entMsg, upbMsg, upbV, valStart]
  all_goals (first | rfl | exact ⟨rfl, Or.inr rfl⟩ | congr)

theorem rowT_other (r b' : Nat) (sd : Bool) (h : b' ≠ B_BYTES ∧ b' ≠ B_DIGEST ∧ b' ≠ B_PARENT ∧ b' ≠ B_EDGE ∧
    b' ≠ B_BMAP ∧ b' ≠ B_DIGS ∧ b' ≠ B_SIZE ∧ b' ≠ B_DUP ∧ b' ≠ B_ENT ∧ b' ≠ B_VPARENT ∧ b' ≠ B_UPB) :
    rowT tr pub r b' sd = [] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp [rowT, rowTraffic, NodeV3.interactions, Dsl.send, Dsl.recv, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
    Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
theorem flatMap_eq_nil' {α β : Type} {l : List α} {f : α → List β} (h : ∀ x ∈ l, f x = []) : l.flatMap f = [] := by
  rw [List.flatMap_eq_nil_iff]; exact h
end ZkFormal.NearV3.NodeProof3
