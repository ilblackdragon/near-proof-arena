import ZkFormal.Near.Extract.NodeOf

/-!
# ZkFormal.Near.Extract.NodeRowT — the messages of one node-table row, per bus
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

/-- A single-bit gate: the message once if the gate is `1`. -/
def gate (x : Fp) (m : List Fp) : List (List Fp) := List.replicate (if x = 1 then 1 else 0) m

abbrev rowT (tr : Trace Fp) (pub : List Fp) (r b : Nat) (sd : Bool) : List (List Fp) :=
  rowTraffic Node.interactions tr T_NODE r pub b sd

variable {tr : Trace Fp} {pub : List Fp}

theorem multNat_one (e : Expr) (r : Nat) :
    Interaction.multNat.go tr T_NODE r pub [e] 0 = if e.eval tr T_NODE r pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr T_NODE r pub = 1 <;> simp [h]

theorem gate_eq (x : Fp) (m : List Fp) : gate x m = if x = 1 then [m] else [] := by
  unfold gate; split <;> rfl

def regW (tr : Trace Fp) (r : Nat) (col : Nat → Nat) : List Fp := (List.range 32).map fun i => tr.cell T_NODE r (col i)

def edgeAV (tr : Trace Fp) (r : Nat) (u : Fp) : List Fp :=
  [tr.cell T_NODE r nid, tr.cell T_NODE r aI, tr.cell T_NODE r aS, tr.cell T_NODE r aN, tr.cell T_NODE r aJ, u]
def edgeBV (tr : Trace Fp) (pub : List Fp) (r : Nat) (u : Fp) : List Fp :=
  [tr.cell T_NODE r nid, kiE.eval tr T_NODE r pub + 1, loE.eval tr T_NODE r pub, tr.cell T_NODE r bN,
    tr.cell T_NODE r bJ, u]

theorem rowT_bytes (r : Nat) :
    rowT tr pub r B_BYTES true =
      gate (tr.cell T_NODE r act) [(K_NPRE : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r pos, tr.cell T_NODE r b] ++
      gate (tr.cell T_NODE r act) [(K_NPOST : Fp) + (16 : Nat) * tr.cell T_NODE r nid, tr.cell T_NODE r pos, tr.cell T_NODE r pb] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, eval_mid]
  all_goals (first | rfl | congr)

theorem rowT_bytesR (r : Nat) : rowT tr pub r B_BYTES false = [] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]

theorem rowT_digest (r : Nat) :
    rowT tr pub r B_DIGEST false =
      gate (tr.cell T_NODE r gD) ([tr.cell T_NODE r dI, tr.cell T_NODE r dL] ++ regW tr r reg) ++
      gate (tr.cell T_NODE r gD) ([tr.cell T_NODE r dI + ((1 : Nat) : Fp), tr.cell T_NODE r dL] ++ regW tr r preg) ++
      gate (if r = 0 then 1 else 0) ([(K_NPRE : Fp), tr.cell T_NODE r len] ++ (List.range 32).map fun i => pub.getD (PV_PRE + i) 0) ++
      gate (if r = 0 then 1 else 0) ([(K_NPOST : Fp), tr.cell T_NODE r len] ++ (List.range 32).map fun i => pub.getD (PV_POST + i) 0) := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, regW, eval_isFirst]
  all_goals (first | rfl | congr)

theorem rowT_digestS (r : Nat) : rowT tr pub r B_DIGEST true = [] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]

theorem rowT_parentS (r : Nat) :
    rowT tr pub r B_PARENT true =
      gate (tr.cell T_NODE r gP) [tr.cell T_NODE r cid, tr.cell T_NODE r depth + ((1 : Nat) : Fp), tr.cell T_NODE r clen,
        tr.cell T_NODE r cres] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]
  all_goals (first | rfl | congr)

theorem rowT_parentR (r : Nat) :
    rowT tr pub r B_PARENT false =
      gate (tr.cell T_NODE r nf - (if r = 0 then 1 else 0))
        [tr.cell T_NODE r nid, tr.cell T_NODE r depth, tr.cell T_NODE r len, tr.cell T_NODE r res] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, eval_isFirst]
  all_goals (first | rfl | congr)

theorem rowT_vslotR (r : Nat) :
    rowT tr pub r B_VSLOT false = gate (tr.cell T_NODE r gV) [tr.cell T_NODE r nid] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]
  all_goals (first | rfl | congr)

theorem rowT_vslotS (r : Nat) : rowT tr pub r B_VSLOT true = [] := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]

theorem rowT_edgeS (r : Nat) :
    rowT tr pub r B_EDGE true = gate (tr.cell T_NODE r gA) (edgeAV tr r 0) ++ gate (tr.cell T_NODE r gB) (edgeBV tr pub r 0) := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, edgeA, edgeB, edgeAV, edgeBV]
  all_goals (first | rfl | congr)

theorem rowT_edgeR (r : Nat) :
    rowT tr pub r B_EDGE false = gate (tr.cell T_NODE r gA) (edgeAV tr r (tr.cell T_NODE r mA)) ++
      gate (tr.cell T_NODE r gB) (edgeBV tr pub r (tr.cell T_NODE r mB)) := by
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Interaction.multNat, multNat_one,
    Interaction.msgVal, gate, Function.comp_def, List.getD_eq_getElem?_getD, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, edgeA, edgeB, edgeAV, edgeBV]
  all_goals (first | rfl | congr)

theorem rowT_other (r b' : Nat) (sd : Bool) (h : b' ≠ B_BYTES ∧ b' ≠ B_DIGEST ∧ b' ≠ B_PARENT ∧ b' ≠ B_VSLOT ∧ b' ≠ B_EDGE) :
    rowT tr pub r b' sd = [] := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp [rowT, rowTraffic, Node.interactions, Dsl.send, Dsl.recv, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
    Ne.symm h5]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
theorem flatMap_eq_nil' {α β : Type} {l : List α} {f : α → List β} (h : ∀ x ∈ l, f x = []) : l.flatMap f = [] := by
  rw [List.flatMap_eq_nil_iff]; exact h
end ZkFormal.Near.NodeProof
