import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Rcpt.Tables.Bnd

/-!
# ZkFormal.NearV3.Rcpt.Extract.BndProof — the `bndV3` view (`BndViewStmt`, `bnd_view`)

One `BndE` per active row (in row order): the public routing record `(x, lo, hi, hn)` and the
final use count `U`.  Traffic: receives `BNDP (x, lo, hi, hn)` and `BND (x, lo, hi, hn, U)`,
sends `BND (x, lo, hi, hn, 0)`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure BndE where
  x : Nat
  lo : Nat
  hi : Nat
  hn : Nat
  U : Nat
  deriving Repr, Inhabited

def BndE.rec4 (e : BndE) : Msg := [e.x, e.lo, e.hi, e.hn]

structure BndWf (es : List BndE) : Prop where
  canon : ∀ e ∈ es, e.x < P ∧ e.lo < P ∧ e.hi < P ∧ e.hn < P ∧ e.U < P
  rows : es.length ≤ 2 ^ BndV3.maxLog

def bndSends (es : List BndE) (b : Nat) : List Msg :=
  if b = B_BND then es.map fun e => e.rec4 ++ [0] else []

def bndRecvs (es : List BndE) (b : Nat) : List Msg :=
  if b = B_BNDP then es.map BndE.rec4
  else if b = B_BND then es.map fun e => e.rec4 ++ [e.U]
  else []

def bndTraffic (es : List BndE) : Traffic := ⟨bndSends es, bndRecvs es⟩

/-- **The `bndV3` view statement.** -/
def BndViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal BndV3.table tr t pub →
    ∃ es, BndWf es ∧ TableTraffic BndV3.interactions tr t pub (bndTraffic es)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.BndProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.BndV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def rowOf (tr : Trace Fp) (tt q : Nat) : BndE :=
  ⟨(tr.cell tt q x).toNat, (tr.cell tt q lo).toNat, (tr.cell tt q hi).toNat, (tr.cell tt q hn).toNat,
    (tr.cell tt q uu).toNat⟩

def isA (tr : Trace Fp) (tt q : Nat) : Bool := decide (tr.cell tt q act = 1)

theorem flatMap_if {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ l : List α, (l.flatMap fun q => if p q then f q else []) = (l.filter p).flatMap f
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp [h, flatMap_if p f l]
    · simp [h, flatMap_if p f l]

theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic BndV3.interactions tr tt q pub bb sd =
      if isA tr tt q then
        (if sd then bndSends [rowOf tr tt q] bb else bndRecvs [rowOf tr tt q] bb).map Msg.toFp
      else [] := by
  unfold rowTraffic BndV3.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Dsl.recv, rec4, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, eval_c, eval_k, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · simp only [ha, ite_true, isA, decide_true]
    cases sd <;> by_cases h1 : bb = B_BNDP <;> by_cases h2 : bb = B_BND <;>
      simp_all [bndSends, bndRecvs, rowOf, BndE.rec4, Msg.toFp, B_BND, B_BNDP, Fp.ofNat_toNat] <;> first | rfl | omega
  · simp [ha, isA]

theorem bndSends_flat (es : List BndE) (b : Nat) : bndSends es b = es.flatMap fun e => bndSends [e] b := by
  unfold bndSends; split <;> simp [map_eq_flatMap]

theorem bndRecvs_flat (es : List BndE) (b : Nat) : bndRecvs es b = es.flatMap fun e => bndRecvs [e] b := by
  unfold bndRecvs; repeat' split
  all_goals simp [map_eq_flatMap]

end ZkFormal.NearV3.BndProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near BndProof

/-- **The `bndV3` view.** -/
theorem bnd_view : BndViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ b sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic BndV3.interactions tr tt q pub b sd) =
      (if sd then bndSends (rows.map (rowOf tr tt)) b else bndRecvs (rows.map (rowOf tr tt)) b).map Msg.toFp := by
    intro b sd
    simp only [rowT]
    rw [flatMap_if]
    cases sd
    · simp only [Bool.false_eq_true, ite_false]
      rw [bndRecvs_flat, List.map_flatMap, List.flatMap_map]
    · simp only [ite_true]
      rw [bndSends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _⟩
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [bndTraffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [bndTraffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3
