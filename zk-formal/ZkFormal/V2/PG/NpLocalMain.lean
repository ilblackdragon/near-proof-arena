import ZkFormal.V2.PG.NpFinal
import ZkFormal.V2.PG.NpCompose

/-!
# ZkFormal.V2.PG.NpLocalMain (P2 copy of `Prover.NpLocalMain` at `dp = pg g`) — `localStmt : LocalStmt`
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

/-- Honest openings at position `x`. -/
noncomputable def hOps (x : Nat) : List (List (List Fp)) :=
  ([mainO A tr, auxOc A cb tr cs, quotOc A cb tr cs] ++
    (commits A tr).map (fun p => [friMat A cb tr cs p.1 p.2])).map
    fun o => o.map fun M => M.row (x >>> (n0 A tr - M.log))

theorem trueOpenings_hon (x : Nat) :
    (Vd A).trueOpenings (honT A cb tr cs) x = hOps A cb tr cs x := by
  unfold IopSpec.trueOpenings hOps
  rw [honT_header, honT_oracles]; rfl

theorem hOps_hon (x : Nat) : HonOps A cb tr cs (hOps A cb tr cs x) x := by
  intro k hk
  unfold hOps
  rw [List.map_append]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega)]

theorem hOps_drop (x : Nat) : (hOps A cb tr cs x).drop 3 = (commits A tr).map fun p =>
    [(friMat A cb tr cs p.1 p.2).row (x >>> (n0 A tr - (n0 A tr - p.1 - p.2)))] := by
  unfold hOps
  rw [List.map_append, List.drop_left' (by simp), List.map_map]
  rfl

theorem deep_hon (hlen : cs.length = nMsg A tr) (x m : Nat) :
    deepAt (F := Fp) ((Vd A).prep (honT A cb tr cs).erase) (hOps A cb tr cs x) m x =
      Bw A cb tr cs m (x >>> (n0 A tr - m)) := by
  rw [deepAt_hon A cb tr cs (honCtx_prep A cb tr cs hlen) (ctxFacts A cb tr cs hlen).n0
    (hOps_hon A cb tr cs x) m, deepH_same A cb tr cs hlen, ← Bw_eq A cb tr cs hlen]

/-- The layer value entering the commitment at layer `i` (before its roll-in). -/
noncomputable def preAt (x i : Nat) : Fp8 :=
  if i = 0 then word A cb tr cs 0 x else preW A cb tr cs (i - 1) (x >>> i)

theorem roll_some (x c0 : Nat) (hc0 : c0 ≤ n0 A tr) {γ : Fp8} (hg : (gammaL A tr cs).lookup c0 = some γ) :
    (if c0 = 0 then preAt A cb tr cs x c0 else
      preAt A cb tr cs x c0 + γ * Bw A cb tr cs (n0 A tr - c0) (x >>> (n0 A tr - (n0 A tr - c0)))) =
      word A cb tr cs c0 (x >>> c0) := by
  by_cases h0 : c0 = 0
  · subst h0; simp [preAt]
  · obtain ⟨i, rfl⟩ : ∃ i, c0 = i + 1 := ⟨c0 - 1, by omega⟩
    rw [if_neg h0, word_succ, show n0 A tr - (n0 A tr - (i + 1)) = i + 1 by omega, hg]
    simp only [preAt, if_neg h0, Nat.add_sub_cancel]

theorem roll_none (x c0 : Nat) (hg : (gammaL A tr cs).lookup c0 = none) :
    (if c0 = 0 then preAt A cb tr cs x c0 else preAt A cb tr cs x c0) = word A cb tr cs c0 (x >>> c0) := by
  by_cases h0 : c0 = 0
  · subst h0; simp [preAt]
  · obtain ⟨i, rfl⟩ : ∃ i, c0 = i + 1 := ⟨c0 - 1, by omega⟩
    rw [if_neg h0, word_succ, hg]
    simp only [preAt, if_neg h0, Nat.add_sub_cancel]

theorem leaf_hon (x c0 a : Nat) (h : c0 + a ≤ n0 A tr) :
    ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 []) =
      (List.range (2 ^ a)).map fun s => word A cb tr cs c0 ((x >>> c0 >>> a) * 2 ^ a + s) := by
  rw [List.getD_cons_zero, show n0 A tr - (n0 A tr - c0 - a) = c0 + a by omega, Nat.shiftRight_add]
  simp only [friMat, ksOfRow_limbsL]

end

theorem localStmt : LocalStmt := by
  intro A cb tr _ hok cs hlen hz x hx
  have hf := ctxFacts A cb tr cs hlen
  unfold IopSpec.ChecksPass
  rw [trueOpenings_hon]
  show checkAt (F := Fp) ((Vd A).prep (honT A cb tr cs).erase) x (hOps A cb tr cs x) = true
  have hdeep := deep_hon A cb tr cs hlen x
  generalize (Vd A).prep (honT A cb tr cs).erase = c at hf hdeep
  unfold checkAt
  dsimp only
  rw [hf.ok, hf.commits, hf.ell, hf.n0, hf.fp, hf.gammas, hOps_drop]
  simp only [hdeep]
  have hn := n0_le A tr hok
  have hℓ : ell A tr ≤ n0 A tr := ZkFormal.Stark.finalLayer_le_queryLog A dp (hdr A tr)
  have h0 : Bw A cb tr cs (n0 A tr) (x >>> (n0 A tr - n0 A tr)) = preAt A cb tr cs x 0 := by
    simp [preAt, word]
  rw [h0, chain_fold (rollInAt A dp (hdr A tr)) (ell A tr) (preAt A cb tr cs x) _ _ ?hF 0 (commits A tr)
    (Nat.zero_le _) (commits_chain A tr)]
  case hF =>
    intro c0 a ha hca hno
    dsimp only
    have hv : ∀ v : Fp8, v = word A cb tr cs c0 (x >>> c0) → (true &&
        (decide ((ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 [])).getD
          (x >>> c0 % 2 ^ a) 0 = v) &&
         decide ((ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 [])).length =
          2 ^ a)),
        foldLeaf (F := Fp) c c0 a (x >>> c0 >>> a)
          (ksOfRow (F := Fp) ([(friMat A cb tr cs c0 a).row (x >>> (n0 A tr - (n0 A tr - c0 - a)))].getD 0 []))) =
        (true, preAt A cb tr cs x (c0 + a)) := by
      intro v hv
      rw [hv, leaf_hon A cb tr cs x c0 a (by omega),
        foldLeaf_word A cb tr cs c hf.n0 hf.betas c0 a _ ha (fun i h1 h2 => gammaL_none A tr cs (hno i h1 h2))]
      have hmod : x >>> c0 % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmod]
      have hpos : (x >>> c0 >>> a) * 2 ^ a + (x >>> c0) % 2 ^ a = x >>> c0 := by
        rw [Nat.shiftRight_eq_div_pow (x >>> c0) a]; exact Nat.div_add_mod' _ _
      simp only [Option.map_some, Option.getD_some, List.length_map, List.length_range, hpos,
        decide_true, Bool.and_self, Bool.true_and]
      simp only [preAt, if_neg (show c0 + a ≠ 0 by omega), Nat.shiftRight_add]
    cases hg : (gammaL A tr cs).lookup c0 with
    | none => dsimp only; exact hv _ (roll_none A cb tr cs x c0 hg)
    | some γ => dsimp only; exact hv _ (roll_some A cb tr cs x c0 (by omega) hg)
  simp only [Bool.true_and, List.length_map, decide_true, Bool.and_true, decide_eq_true_eq]
  have hfin := final_check A cb tr cs hok hlen hz (x >>> ell A tr)
  cases hg : (gammaL A tr cs).lookup (ell A tr) with
  | none => dsimp only; rw [roll_none A cb tr cs x _ hg]; exact hfin
  | some γ => dsimp only; rw [roll_some A cb tr cs x _ hℓ hg]; exact hfin

/-- **Perfect completeness of the np-udr-stark IOP** (with `A.tables.length < 2^32`). -/
theorem npIopComplete' : NpIopCompleteStmt' :=
  npIopComplete_of schedForm msgFits msgPrefix globalStmt localStmt

end ZkFormal.V2.PG
