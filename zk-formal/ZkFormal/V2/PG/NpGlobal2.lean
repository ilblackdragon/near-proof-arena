import ZkFormal.V2.PG.NpGlobal

/-!
# ZkFormal.V2.PG.NpGlobal2 (P2 copy of `Prover.NpGlobal2` at `dp = pg g`) — `GlobalStmt` from the bus product equality

`ali_table`: the ALI identity of each table at `z ∉ F`; `global_of`: `GlobalStmt` given
`BusProdStmt` (the honest finals satisfy the bus equation).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- The honest finals satisfy the bus equation. -/
def BusProdStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), Holds A (pubOf Fp cb) tr →
    headerOk A dp (hdr A tr) = true → ∀ α γ : Fp8,
      ((List.range A.tables.length).map fun t =>
        ((finsT A cb tr α γ t).take (layT A tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1 =
      ((List.range A.tables.length).map fun t =>
        ((finsT A cb tr α γ t).drop (layT A tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- **The ALI identity** of table `t` at an out-of-domain point. -/
theorem ali_table (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ αc : Fp8)
    {z : Fp8} (hz : ¬ z.IsBase) :
    combine αc (((tb A t).allConstraints.map (·.evalWith (oodEnv (F := Fp)
        (cb.map fun b => ofNatF b.toNat) (tr.log t) z (mainV A tr t z) (mainV A tr t (omg (lg tr t) * z))))) ++
      auxConstraints (tb A t) dp.auxGroup (oodEnv (F := Fp) (cb.map fun b => ofNatF b.toNat) (tr.log t) z
        (mainV A tr t z) (mainV A tr t (omg (lg tr t) * z))) α γ (auxV A cb tr α γ t z)
        (auxV A cb tr α γ t (omg (lg tr t) * z)) (finsT A cb tr α γ t)) =
      (z ^ (2 ^ tr.log t) - 1) * combine (z ^ (2 ^ tr.log t)) (quotV A cb tr α γ αc t z) := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  rw [oodEnv_eq A cb tr t hlog hz]
  show compX A cb tr α γ αc t z = _
  rw [qC_spec A cb tr hH ht α γ αc z, ev_chunks]
  rfl

theorem foldl_tables {α β : Type} (F : Bool × List α → β → Bool × List α) (g : Nat → β)
    (fins : Nat → List α) : ∀ (l : List Nat) (R X : List α), X = l.flatMap fins ++ R →
    (∀ t ∈ l, ∀ R, F (true, fins t ++ R) (g t) = (true, R)) → (l.map g).foldl F (true, X) = (true, R)
  | [], R, X, hX, _ => by simp [hX]
  | t :: l, R, X, hX, h => by
    rw [hX, List.map_cons, List.foldl_cons, List.flatMap_cons, List.append_assoc, h t (by simp)]
    exact foldl_tables F g fins l R _ rfl (fun t' ht' R' => h t' (by simp [ht']) R')

theorem finalsAll_length (α γ : Fp8) :
    (finalsAll A cb tr α γ).length = ((layout A dp (hdr A tr)).map fun L => L.sendG + L.recvG).sum := by
  rw [lay_eq, List.map_map, finalsAll, sum_flatMap_length]
  congr 1; apply List.map_congr_left; intro t _
  simp [finsT, layT, nG]

theorem oodAll_length (α γ αc z : Fp8) :
    (oodAll A cb tr α γ αc z).length =
      ((layout A dp (hdr A tr)).map fun L => 2 * L.width + 2 * L.aux + L.quot).sum := by
  rw [lay_eq, List.map_map, oodAll, sum_flatMap_length]
  congr 1; apply List.map_congr_left; intro t _
  simp [oodT, mainV, auxV, quotV, layT]; omega

/-- The verifier's context on the honest transcript. -/
theorem prep_hon (cs : List Fp8) (hlen : cs.length = nMsg A tr) :
    (Vd A).prep (honT A cb tr cs).erase = prepCore A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs)
      (cs.drop 4) (finalsC A cb tr cs) (oodC A cb tr cs) (finalPoly A cb tr cs) := by
  have h4 : 4 ≤ cs.length := by rw [hlen, nMsg_eq]; omega
  have hc : cs = cAfp cs :: cGam cs :: cAc cs :: cZ cs :: cs.drop 4 := by
    match cs, h4 with
    | a :: b :: c :: d :: rest, _ => rfl
  show prep A dp (honT A cb tr cs).erase = _
  rw [prep_eq A (honT A cb tr cs).erase (by rw [erase_header, honT_header])
    (by rw [erase_chals, honT_chals A cb tr cs hlen]; exact hc) (by rw [erase_elems, honT_elems])]
  rfl

theorem globalChecks_hon (hB : BusProdStmt) (hH : Holds A (pubOf Fp cb) tr)
    (hok : headerOk A dp (hdr A tr) = true) (α γ αc z : Fp8) (hz : ¬ z.IsBase) :
    globalChecks (F := Fp) A dp (cb.map fun b => ofNatF b.toNat) (layout A dp (hdr A tr))
      ((List.range A.tables.length).map (oodRec A cb tr α γ αc z)) (finalsAll A cb tr α γ) α γ αc z =
      true := by
  unfold globalChecks
  dsimp only
  rw [fins_hon]
  have hT : A.tables = (List.range A.tables.length).map (tb A) := tables_eq A
  have e : finalsAll A cb tr α γ = (List.range A.tables.length).flatMap (finsT A cb tr α γ) ++ [] := by
    rw [List.append_nil]; rfl
  rw [lay_eq]
  have hB' := hB A cb tr hH hok α γ
  generalize hn : A.tables.length = n at hT e hB' ⊢
  rw [hT, zip_map_range, zip_map_range, zip_map_range]
  rw [foldl_tables _ (fun t => (tb A t, layT A tr t, oodRec A cb tr α γ αc z t)) (finsT A cb tr α γ) _ [] _ e
    ?step]
  case step =>
    intro t ht R
    have htn : t < A.tables.length := by rw [hn]; exact List.mem_range.mp ht
    have hto := tabOk A tr hok htn
    have hl : (finsT A cb tr α γ t).length = (layT A tr t).sendG + (layT A tr t).recvG := by
      simp [finsT, layT_sendRecv]
    dsimp only
    rw [List.take_left' hl, List.drop_left' hl]
    dsimp only [layT, oodRec]
    simp only [ali_table A cb tr hH hto α γ αc hz, decide_true, Bool.and_self]
  simp only [Bool.true_and, decide_eq_true_eq]
  rw [List.map_map, List.map_map]
  exact hB'

end

theorem global_of (hB : BusProdStmt) : GlobalStmt := by
  intro A cb tr hH hok cs hlen hz
  rw [prep_hon A cb tr cs hlen]
  show (prepCore A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs) (cs.drop 4) (finalsC A cb tr cs)
    (oodC A cb tr cs) (finalPoly A cb tr cs)).globalOk = true
  unfold prepCore
  dsimp only
  rw [show oodC A cb tr cs = oodAll A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs) from rfl,
    splitOod_hon]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hn := nMsg_eq A tr
  refine ⟨⟨⟨⟨by simp [hlen, hn, nB, kinds]; omega, rfl⟩, finalsAll_length A cb tr _ _⟩,
    oodAll_length A cb tr _ _ _ _⟩, ?_⟩
  exact globalChecks_hon A cb tr hB hH hok _ _ _ _ hz

end ZkFormal.Prover.Np.G
