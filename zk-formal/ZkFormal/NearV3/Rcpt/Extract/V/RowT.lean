import ZkFormal.NearV3.Rcpt.Extract.V.Regs

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.RowT — the messages of one row of `rcptV3`

`rowT`: the traffic of a row per bus and side, as gated message lists.
`emit_some` / `emit_none`: the emission slots of a row in state `X` are the
`emits` of `X`.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multNat1 (g : Expr) (q : Nat) :
    Interaction.multNat.go tr tt q pub [g] 0 = if g.eval tr tt q pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : g.eval tr tt q pub = 1 <;> simp [h]

def C (tr : Trace Fp) (tt q x : Nat) : Fp := tr.cell tt q x

def regsAt (tr : Trace Fp) (tt q : Nat) : List Fp := (List.range 32).map fun j => tr.cell tt q (reg j)
def pubsAt (pub : List Fp) (off len : Nat) : List Fp := (List.range len).map fun j => pub.getD (off + j) 0

/-- One emission slot's messages. -/
def slotT (tr : Trace Fp) (tt q e : Nat) : List (List Fp) :=
  if tr.cell tt q (eG e) = 1 then
    [[tr.cell tt q (eId e), tr.cell tt q (ePos e), tr.cell tt q (eV e)]] else []

def gt (x : Fp) (m : List Fp) : List (List Fp) := if x = 1 then [m] else []

theorem gate_eq {α : Type} (X bus : Nat) (Y sd : Bool) (P : Prop) [Decidable P] (m : α) :
    (if X = bus ∧ Y = sd then List.replicate (if P then 1 else 0) m else []) =
      (if bus = X ∧ sd = Y then (if P then [m] else []) else []) := by
  by_cases h1 : X = bus <;> by_cases h2 : Y = sd <;> by_cases hp : P <;> simp [h1, h2, hp, eq_comm]

/-- **Messages of a row.** -/
theorem rowT (q bus : Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub bus sd =
      (if bus = B_BYTES ∧ sd = true then (List.range 3).flatMap (slotT tr tt q) else []) ++
      (if bus = B_DIGEST ∧ sd = false then gt (C tr tt q gDg) ([C tr tt q dI, C tr tt q dL] ++ regsAt tr tt q) else []) ++
      (if bus = B_KEYNIB ∧ sd = true then
        gt (C tr tt q gKA) [wE.eval tr tt q pub, C tr tt q tA, C tr tt q symA, C tr tt q lastA] else []) ++
      (if bus = B_KEYNIB ∧ sd = true then
        gt (C tr tt q gKB) [wE.eval tr tt q pub, C tr tt q tB, C tr tt q symB, (0 : Nat)] else []) ++
      (if bus = B_FINAL ∧ sd = false then
        gt (C tr tt q gF) [C tr tt q RcptV3.r + (W_AK : Nat) * C tr tt q sT0, (0 : Nat), C tr tt q fkF, C tr tt q kF]
        else []) ++
      (if bus = B_MEM ∧ sd = false then
        gt (C tr tt q sDEP) [C tr tt q kslot, C tr tt q tprev, C tr tt q idx, C tr tt q bef, C tr tt q lk, C tr tt q st]
        else []) ++
      (if bus = B_MEM ∧ sd = true then
        gt (C tr tt q sDEP) [C tr tt q kslot, C tr tt q RcptV3.r + (1 : Nat), C tr tt q idx,
          aftE.eval tr tt q pub, C tr tt q lk, C tr tt q st] else []) ++
      (if bus = B_RIDS ∧ sd = true then gt (C tr tt q sRID) [C tr tt q RcptV3.r, C tr tt q idx, C tr tt q b] else []) ++
      (if bus = B_MPOS ∧ sd = true then
        gt (C tr tt q rf) [(0 : Nat), C tr tt q RcptV3.r, (K_LEAF : Nat) + (16 : Nat) * C tr tt q RcptV3.r, (68 : Nat)]
        else []) ++
      (if bus = B_RCL ∧ sd = true then gt (C tr tt q le) [C tr tt q j, C tr tt q oEnd] else []) ++
      (if bus = B_SREC ∧ sd = true then gt (C tr tt q gV) [C tr tt q RcptV3.r, C tr tt q idx, C tr tt q b] else []) ++
      (if bus = B_SREC ∧ sd = false then gt (C tr tt q gS) [C tr tt q RcptV3.r, C tr tt q idx, C tr tt q sx] else []) ++
      (if bus = B_AKC ∧ sd = false then gt (C tr tt q gAK) [C tr tt q kF, C tr tt q uak] else []) ++
      (if bus = B_AKC ∧ sd = true then gt (C tr tt q gAK) [C tr tt q kF, C tr tt q uak + (1 : Nat)] else []) ++
      (if bus = B_BND ∧ sd = false then
        gt (C tr tt q gBd) [(BND_STRIDE : Nat) * C tr tt q RcptV3.q + C tr tt q iB, C tr tt q loB, C tr tt q hiB,
          C tr tt q hnB, C tr tt q uB] else []) ++
      (if bus = B_BND ∧ sd = true then
        gt (C tr tt q gBd) [(BND_STRIDE : Nat) * C tr tt q RcptV3.q + C tr tt q iB, C tr tt q loB, C tr tt q hiB,
          C tr tt q hnB, C tr tt q uB + (1 : Nat)] else []) := by
  simp only [rowTraffic, RcptV3.interactions, bndMsg, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons,
    List.map_nil, List.map_append, List.map_map, eval_c, eval_add, eval_k, eval_smul, eval_mid, eval_pub,
    List.append_assoc, regsAt, pubsAt, Function.comp_def, ZkFormal.Near.Rcpt.pubs, C, gt]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))))))))))))))
  · rw [List.flatMap_map]
    by_cases h : bus = B_BYTES ∧ sd = true
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      apply flatMap_congr'
      intro e _
      simp only [slotT, multNat1, eval_c]
      by_cases hg : tr.cell tt q (eG e) = 1 <;> simp [hg]
    · rw [if_neg h, flatMap_congr' (G := fun _ => []) (fun e _ => by
        rw [if_neg]; intro h'; exact h ⟨h'.1.symm, h'.2.symm⟩), flatMap_nil_fun]
  all_goals exact gate_eq _ _ _ _ _ _

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem mem_emit {X : Nat} {ems : List Em} (hX : (X, ems) ∈ emits) {e : Nat} (he : e < 3) {x : Expr}
    (hx : x ∈ (match ems[e]? with
      | some (id, p, v, g) =>
        [Expr.mul (c X) (sub (c (eId e)) id), Expr.mul (c X) (sub (c (ePos e)) p),
         Expr.mul (c X) (sub (c (eV e)) v), Expr.mul (c X) (sub (c (eG e)) g)]
      | none => [Expr.mul (c X) (c (eG e))] : List Expr)) : x ∈ RcptV3.constraints := by
  apply mem_em
  unfold cEmit
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(X, ems), hX, List.mem_flatMap.mpr
    ⟨e, List.mem_range.mpr he, hx⟩⟩)

/-- An emission slot of state `X`. -/
theorem emit_some {q X : Nat} {ems : List Em} (hq : q < tr.height tt) (hX : (X, ems) ∈ emits)
    (h1 : tr.cell tt q X = 1) {e : Nat} (he : e < 3) {id p v g : Expr}
    (hs : ems[e]? = some (id, p, v, g)) :
    slotT tr tt q e = if g.eval tr tt q pub = 1 then
      [[id.eval tr tt q pub, p.eval tr tt q pub, v.eval tr tt q pub]] else [] := by
  have c1 := con hL hq (e := .mul (c X) (sub (c (eId e)) id)) (mem_emit hL hX he (by rw [hs]; simp))
  have c2 := con hL hq (e := .mul (c X) (sub (c (ePos e)) p)) (mem_emit hL hX he (by rw [hs]; simp))
  have c3 := con hL hq (e := .mul (c X) (sub (c (eV e)) v)) (mem_emit hL hX he (by rw [hs]; simp))
  have c4 := con hL hq (e := .mul (c X) (sub (c (eG e)) g)) (mem_emit hL hX he (by rw [hs]; simp))
  simp only [eval_mul, eval_c, eval_sub] at c1 c2 c3 c4
  rw [h1] at c1 c2 c3 c4
  have e1 : tr.cell tt q (eId e) = id.eval tr tt q pub := by grind
  have e2 : tr.cell tt q (ePos e) = p.eval tr tt q pub := by grind
  have e3 : tr.cell tt q (eV e) = v.eval tr tt q pub := by grind
  have e4 : tr.cell tt q (eG e) = g.eval tr tt q pub := by grind
  simp only [slotT, e1, e2, e3, e4]

theorem emit_none {q X : Nat} {ems : List Em} (hq : q < tr.height tt) (hX : (X, ems) ∈ emits)
    (h1 : tr.cell tt q X = 1) {e : Nat} (he : e < 3) (hs : ems[e]? = none) : slotT tr tt q e = [] := by
  have c1 := con hL hq (e := .mul (c X) (c (eG e))) (mem_emit hL hX he (by rw [hs]; simp))
  simp only [eval_mul, eval_c] at c1
  rw [h1] at c1
  have : tr.cell tt q (eG e) = 0 := by grind
  simp [slotT, this]

end ZkFormal.NearV3.RcptV3Proof
