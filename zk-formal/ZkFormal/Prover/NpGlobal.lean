import ZkFormal.Prover.NpDeg3

/-!
# ZkFormal.Prover.NpGlobal — the clear-text checks on the honest transcript

* `splitOod_hon`, `fins_hon`: the verifier's slicing of the OOD values and the finals;
* `oodEnv_eq`: off the trace domain the verifier's closed-form selectors are the
  polynomial ones (`z ∉ F`);
* `ali_table`: the ALI identity of every table (`qC_spec`, `ev_chunks`).
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- Folding a step that peels one block per element. -/
theorem foldl_blocks {α β σ : Type} (F : List σ × List α → β → List σ × List α)
    (blk : β → σ → List α) : ∀ (bs : List β) (os : List σ) (acc : List σ) (R : List α),
    bs.length = os.length →
    (∀ p ∈ bs.zip os, ∀ acc R, F (acc, blk p.1 p.2 ++ R) p.1 = (acc ++ [p.2], R)) →
    bs.foldl F (acc, ((bs.zip os).flatMap fun p => blk p.1 p.2) ++ R) = (acc ++ os, R)
  | [], [], acc, R, _, _ => by simp
  | b :: bs, o :: os, acc, R, hl, h => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.foldl_cons, List.append_assoc]
    rw [h (b, o) (by simp) acc]
    rw [foldl_blocks F blk bs os (acc ++ [o]) R (by simpa using hl)
      (fun p hp acc R => h p (by simp [hp]) acc R)]
    simp
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

theorem foldl_blocks' {α β σ : Type} (F : List σ × List α → β → List σ × List α)
    (blk : β → σ → List α) (bs : List β) (os : List σ) (acc : List σ) (R X : List α)
    (hX : X = ((bs.zip os).flatMap fun p => blk p.1 p.2) ++ R) (hl : bs.length = os.length)
    (h : ∀ p ∈ bs.zip os, ∀ acc R, F (acc, blk p.1 p.2 ++ R) p.1 = (acc ++ [p.2], R)) :
    bs.foldl F (acc, X) = (acc ++ os, R) := by
  rw [hX]; exact foldl_blocks F blk bs os acc R hl h

theorem zip_map_range {α β : Type} (n : Nat) (f : Nat → α) (g : Nat → β) :
    ((List.range n).map f).zip ((List.range n).map g) = (List.range n).map fun t => (f t, g t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zip_append, ih]

theorem take_drop_block {α : Type} (a R : List α) :
    (a ++ R).take a.length = a ∧ (a ++ R).drop a.length = R := by
  simp

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- The honest OOD values of table `t`. -/
noncomputable def oodRec (α γ αc z : Fp8) (t : Nat) : TOod Fp8 :=
  ⟨mainV A tr t z, mainV A tr t (omg (lg tr t) * z), auxV A cb tr α γ t z,
    auxV A cb tr α γ t (omg (lg tr t) * z), quotV A cb tr α γ αc t z⟩

theorem splitOod_hon (α γ αc z : Fp8) :
    splitOod (layout A dp (hdr A tr)) (oodAll A cb tr α γ αc z) =
      ((List.range A.tables.length).map (oodRec A cb tr α γ αc z), []) := by
  let blk : TLayout → TOod Fp8 → List Fp8 := fun _ o => o.mainZ ++ o.mainG ++ o.auxZ ++ o.auxG ++ o.quotZ
  have e : oodAll A cb tr α γ αc z =
      (((List.range A.tables.length).map (layT A tr)).zip
        ((List.range A.tables.length).map (oodRec A cb tr α γ αc z))).flatMap
        (fun p => blk p.1 p.2) ++ [] := by
    rw [zip_map_range, List.append_nil, List.flatMap_map]; rfl
  unfold splitOod
  rw [lay_eq, foldl_blocks' _ blk _ _ [] [] _ e (by simp)]
  · simp
  · intro p hp acc R
    rw [zip_map_range] at hp
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp
    simp only [oodRec, layT, List.append_assoc]
    have l1 : (mainV A tr t z).length = (tb A t).width := by simp [mainV]
    have l2 : (mainV A tr t (omg (lg tr t) * z)).length = (tb A t).width := by simp [mainV]
    have l3 : (auxV A cb tr α γ t z).length = (tb A t).auxCount dp.auxGroup := by simp [auxV]
    have l4 : (auxV A cb tr α γ t (omg (lg tr t) * z)).length = (tb A t).auxCount dp.auxGroup := by
      simp [auxV]
    have l5 : (quotV A cb tr α γ αc t z).length = (tb A t).quotCount dp.auxGroup := by simp [quotV]
    simp only [blk, List.append_assoc, List.take_left' l1, List.drop_left' l1, List.take_left' l2,
      List.drop_left' l2, List.take_left' l3, List.drop_left' l3, List.take_left' l4,
      List.drop_left' l4, List.take_left' l5, List.drop_left' l5]

/-- The verifier's per-table slices of the finals. -/
theorem fins_hon (α γ : Fp8) :
    ((layout A dp (hdr A tr)).foldl (fun (acc : List (List Fp8) × List Fp8) L =>
      (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG)))
      ([], finalsAll A cb tr α γ)).1 = (List.range A.tables.length).map (finsT A cb tr α γ) := by
  let blk : TLayout → List Fp8 → List Fp8 := fun _ f => f
  have e : finalsAll A cb tr α γ = (((List.range A.tables.length).map (layT A tr)).zip
      ((List.range A.tables.length).map (finsT A cb tr α γ))).flatMap (fun p => blk p.1 p.2) ++ [] := by
    rw [zip_map_range, List.append_nil, List.flatMap_map]; rfl
  rw [lay_eq, foldl_blocks' _ blk _ _ [] [] _ e (by simp)]
  · simp
  · intro p hp acc R
    rw [zip_map_range] at hp
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp
    have hl : (finsT A cb tr α γ t).length = (layT A tr t).sendG + (layT A tr t).recvG := by
      simp [finsT, layT_sendRecv]
    simp only [blk, List.take_left' hl, List.drop_left' hl]

theorem npMulPow (a b : Fp8) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [Semiring.pow_zero, Semiring.pow_zero, Semiring.pow_zero, Semiring.mul_one]
  | n + 1 => by rw [Semiring.pow_succ, Semiring.pow_succ, Semiring.pow_succ, npMulPow a b n]; grind

theorem tables_eq : A.tables = (List.range A.tables.length).map (tb A) := by
  apply List.ext_getElem (by simp)
  intro t h1 h2; simp [tb_eq A h1]

/-- Off the trace domain the verifier's environment is the polynomial one. -/
theorem oodEnv_eq (t : Nat) (hlog : tr.log t ≤ 27) {z : Fp8} (hz : ¬ z.IsBase) :
    oodEnv (F := Fp) (cb.map fun b => ofNatF b.toNat) (tr.log t) z (mainV A tr t z)
      (mainV A tr t (omg (lg tr t) * z)) = pEnv A cb tr t z := by
  have hT := npTwoPow_ne_zero hlog
  have hz1 : z ≠ 1 := fun h => hz ((Fp8.isBase_iff z).mpr ⟨1, h⟩)
  have hz2 : omg (lg tr t) * z ≠ 1 := by
    intro h
    apply hz
    have hw := npOmg_ne_zero (lg tr t) hlog
    have : z = Fp8.ofBase ((Fp.twoAdicGen (lg tr t))⁻¹) := by
      rw [ofBase_inv]
      show z = (omg (lg tr t))⁻¹
      have e := Field.inv_mul_cancel hw
      calc z = (omg (lg tr t))⁻¹ * (omg (lg tr t) * z) := by
            rw [← Semiring.mul_assoc, e, Semiring.one_mul]
        _ = _ := by rw [h, Semiring.mul_one]
    exact (Fp8.isBase_iff z).mpr ⟨_, this⟩
  have hpow : (omg (lg tr t) * z) ^ (2 ^ lg tr t) = z ^ (2 ^ lg tr t) := by
    rw [npMulPow, omg_pow_T hlog, Semiring.one_mul]
  have hF : selSum (2 ^ lg tr t) z = (z ^ (2 ^ tr.log t) - 1) / (((2 ^ tr.log t : Nat) : Fp8) * (z - 1)) :=
    npSelSum_closed hT hz1
  have hL : selSum (2 ^ lg tr t) (omg (lg tr t) * z) = (z ^ (2 ^ tr.log t) - 1) /
      (((2 ^ tr.log t : Nat) : Fp8) * (omg (lg tr t) * z - 1)) := by
    rw [npSelSum_closed hT hz2, hpow]
  unfold oodEnv pEnv
  simp only [Env.mk.injEq, true_and]
  refine ⟨?_, rfl, hF.symm, hL.symm, by rw [hL]; rfl⟩
  funext c nx
  cases nx <;> rfl

end

end ZkFormal.Prover.Np
