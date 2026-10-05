import ZkFormal.Near.Extract.RcptRegs

/-!
# ZkFormal.Near.Extract.RcptRowT — the messages of one row

`rowT`: the traffic of a row per bus and side, as gated message lists.
`emit_some` / `emit_none`: the emission slots of a row in state `X` are the
`emits` of `X`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem multNat1 (g : Expr) (q : Nat) :
    Interaction.multNat.go tr T_RCPT q pub [g] 0 = if g.eval tr T_RCPT q pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : g.eval tr T_RCPT q pub = 1 <;> simp [h]

def C (tr : Trace Fp) (q x : Nat) : Fp := tr.cell T_RCPT q x

def regsAt (tr : Trace Fp) (q : Nat) : List Fp := (List.range 32).map fun j => tr.cell T_RCPT q (reg j)
def pubsAt (pub : List Fp) (off len : Nat) : List Fp := (List.range len).map fun j => pub.getD (off + j) 0

/-- One emission slot's messages. -/
def slotT (tr : Trace Fp) (q e : Nat) : List (List Fp) :=
  if tr.cell T_RCPT q (eG e) = 1 then
    [[tr.cell T_RCPT q (eId e), tr.cell T_RCPT q (ePos e), tr.cell T_RCPT q (eV e)]] else []

def gt (x : Fp) (m : List Fp) : List (List Fp) := if x = 1 then [m] else []

theorem gate_eq {α : Type} (X bus : Nat) (Y sd : Bool) (P : Prop) [Decidable P] (m : α) :
    (if X = bus ∧ Y = sd then List.replicate (if P then 1 else 0) m else []) =
      (if bus = X ∧ sd = Y then (if P then [m] else []) else []) := by
  by_cases h1 : X = bus <;> by_cases h2 : Y = sd <;> by_cases hp : P <;> simp [h1, h2, hp, eq_comm]

/-- **Messages of a row.** -/
theorem rowT (q bus : Nat) (sd : Bool) :
    rowTraffic Rcpt.interactions tr T_RCPT q pub bus sd =
      (if bus = B_BYTES ∧ sd = true then (List.range 3).flatMap (slotT tr q) else []) ++
      (if bus = B_DIGEST ∧ sd = false then gt (C tr q gDg) ([C tr q dI, C tr q dL] ++ regsAt tr q) else []) ++
      (if bus = B_DIGEST ∧ sd = false then
        gt (C tr q lastR) ([(K_RC : Fp), C tr q oEnd] ++ pubsAt pub PV_RC 32) else []) ++
      (if bus = B_DIGEST ∧ sd = false then
        gt (C tr q lastR) ([(K_RF : Fp), C tr q o2End] ++ pubsAt pub PV_RFC 32) else []) ++
      (if bus = B_KEYNIB ∧ sd = true then
        gt (C tr q gKA) [C tr q Rcpt.r, C tr q tA, C tr q symA, C tr q lastA] else []) ++
      (if bus = B_KEYNIB ∧ sd = true then
        gt (C tr q sV) [C tr q Rcpt.r, (3 : Nat) + (2 : Nat) * C tr q idx, loE.eval tr T_RCPT q pub, (0 : Nat)]
        else []) ++
      (if bus = B_FINAL ∧ sd = false then gt (C tr q rf) [C tr q Rcpt.r, C tr q kslot] else []) ++
      (if bus = B_MEM ∧ sd = false then
        gt (C tr q sDEP) [C tr q kslot, C tr q tprev, C tr q idx, C tr q bef, C tr q lk, C tr q st] else []) ++
      (if bus = B_MEM ∧ sd = true then
        gt (C tr q sDEP) [C tr q kslot, C tr q Rcpt.r + (1 : Nat), C tr q idx, aftE.eval tr T_RCPT q pub,
          C tr q lk, C tr q st] else []) ++
      (if bus = B_RIDS ∧ sd = true then gt (C tr q sRID) [C tr q Rcpt.r, C tr q idx, C tr q b] else []) ++
      (if bus = B_MPOS ∧ sd = true then
        gt (C tr q rf) [(0 : Nat), C tr q Rcpt.r, (K_LEAF : Nat) + (16 : Nat) * C tr q Rcpt.r, (68 : Nat)]
        else []) := by
  simp only [rowTraffic, Rcpt.interactions, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons,
    List.map_nil, List.map_append, List.map_map, eval_c, eval_add, eval_k, eval_smul, eval_mid, eval_pub,
    List.append_assoc, regsAt, pubsAt, Function.comp_def, pubs, C, gt]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))))))))
  · rw [List.flatMap_map]
    by_cases h : bus = B_BYTES ∧ sd = true
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      apply flatMap_congr'
      intro e _
      simp only [slotT, multNat1, eval_c]
      by_cases hg : tr.cell T_RCPT q (eG e) = 1 <;> simp [hg]
    · rw [if_neg h, flatMap_congr' (G := fun _ => []) (fun e _ => by
        rw [if_neg]; intro h'; exact h ⟨h'.1.symm, h'.2.symm⟩), flatMap_nil_fun]
  all_goals exact gate_eq _ _ _ _ _ _

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem mem_emit {X : Nat} {ems : List Em} (hX : (X, ems) ∈ emits) {e : Nat} (he : e < 3) {x : Expr}
    (hx : x ∈ (match ems[e]? with
      | some (id, p, v, g) =>
        [Expr.mul (c X) (sub (c (eId e)) id), Expr.mul (c X) (sub (c (ePos e)) p),
         Expr.mul (c X) (sub (c (eV e)) v), Expr.mul (c X) (sub (c (eG e)) g)]
      | none => [Expr.mul (c X) (c (eG e))] : List Expr)) : x ∈ Rcpt.constraints := by
  apply mem_em
  unfold cEmit
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(X, ems), hX, List.mem_flatMap.mpr
    ⟨e, List.mem_range.mpr he, hx⟩⟩)

/-- An emission slot of state `X`. -/
theorem emit_some {q X : Nat} {ems : List Em} (hq : q < tr.height T_RCPT) (hX : (X, ems) ∈ emits)
    (h1 : tr.cell T_RCPT q X = 1) {e : Nat} (he : e < 3) {id p v g : Expr}
    (hs : ems[e]? = some (id, p, v, g)) :
    slotT tr q e = if g.eval tr T_RCPT q pub = 1 then
      [[id.eval tr T_RCPT q pub, p.eval tr T_RCPT q pub, v.eval tr T_RCPT q pub]] else [] := by
  have c1 := con hL hq (e := .mul (c X) (sub (c (eId e)) id)) (mem_emit hL hX he (by rw [hs]; simp))
  have c2 := con hL hq (e := .mul (c X) (sub (c (ePos e)) p)) (mem_emit hL hX he (by rw [hs]; simp))
  have c3 := con hL hq (e := .mul (c X) (sub (c (eV e)) v)) (mem_emit hL hX he (by rw [hs]; simp))
  have c4 := con hL hq (e := .mul (c X) (sub (c (eG e)) g)) (mem_emit hL hX he (by rw [hs]; simp))
  simp only [eval_mul, eval_c, eval_sub] at c1 c2 c3 c4
  rw [h1] at c1 c2 c3 c4
  have e1 : tr.cell T_RCPT q (eId e) = id.eval tr T_RCPT q pub := by grind
  have e2 : tr.cell T_RCPT q (ePos e) = p.eval tr T_RCPT q pub := by grind
  have e3 : tr.cell T_RCPT q (eV e) = v.eval tr T_RCPT q pub := by grind
  have e4 : tr.cell T_RCPT q (eG e) = g.eval tr T_RCPT q pub := by grind
  simp only [slotT, e1, e2, e3, e4]

theorem emit_none {q X : Nat} {ems : List Em} (hq : q < tr.height T_RCPT) (hX : (X, ems) ∈ emits)
    (h1 : tr.cell T_RCPT q X = 1) {e : Nat} (he : e < 3) (hs : ems[e]? = none) : slotT tr q e = [] := by
  have c1 := con hL hq (e := .mul (c X) (c (eG e))) (mem_emit hL hX he (by rw [hs]; simp))
  simp only [eval_mul, eval_c] at c1
  rw [h1] at c1
  have : tr.cell T_RCPT q (eG e) = 0 := by grind
  simp [slotT, this]

end ZkFormal.Near.RcptProof
