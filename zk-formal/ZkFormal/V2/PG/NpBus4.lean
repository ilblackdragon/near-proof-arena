import ZkFormal.V2.PG.NpBus3

/-!
# ZkFormal.V2.PG.NpBus4 (P2 copy of `Prover.NpBus4` at `dp = pg g`) — `busProd : BusProdStmt`
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- The `(key, multiplicity)` entries of one side of the buses. -/
def entries (s : Bool) : List ((Nat × List Fp) × Nat) :=
  (List.range A.tables.length).flatMap fun t => (List.range (2 ^ tr.log t)).flatMap fun r =>
    ((tb A t).interactions.filter fun i => i.send == s).map fun i =>
      ((i.bus, i.msgVal tr t r (pubOf Fp cb)), i.multNat tr t r (pubOf Fp cb))

theorem cnt_entries (s : Bool) (b : Nat) (m : List Fp) :
    cntK (entries A cb tr s) (b, m) = busCount A tr (pubOf Fp cb) b s m := by
  rw [busCount_eq]
  unfold entries cntK
  rw [sum_flatMap]
  congr 1; apply List.map_congr_left; intro t _
  rw [sum_flatMap, tableBusCount_eq]
  congr 1; apply List.map_congr_left; intro r _
  rw [List.map_map, sum_filter_eq]
  congr 1; apply List.map_congr_left; intro i _
  simp only [Function.comp, Prod.mk.injEq]
  by_cases hs : i.send = s
  · simp [hs]
  · have : (i.send == s) = false := by simp [hs]
    simp [this, hs]

theorem numSide_eq (T : Air.Table) (s : Bool) :
    numGroups (T.numSide s) dp.auxGroup = (T.interactions.filter fun i => i.send == s).length := by
  simp [numGroups, Table.numSide, dp, V2.G.pg, Params.default]

/-- One side's product over the rows of table `t`. -/
noncomputable def sideProd (α γ : Fp8) (t : Nat) (s : Bool) : Fp8 :=
  prodF ((List.range (2 ^ tr.log t)).map fun r =>
    prodF (((tb A t).interactions.filter fun i => i.send == s).map fun i =>
      (γ - FPv α i.bus (i.msgVal tr t r (pubOf Fp cb))) ^ (i.multNat tr t r (pubOf Fp cb))))

theorem rows_side (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ : Fp8) (s : Bool)
    (k : Nat) (f : Nat → Nat) (hk : k = ((tb A t).interactions.filter fun i => i.send == s).length)
    (hf : ∀ r, prodF ((List.range k).map fun j => phiG (rEnv A cb tr t r) α γ (tb A t).interactions (f j)) =
      prodF (((tb A t).interactions.filter fun i => i.send == s).map
        fun i => (chainOf (rEnv A cb tr t r) α γ i).2)) :
    prodF ((List.range k).map fun j => accAt A cb tr α γ t (2 ^ lg tr t) (f j)) = sideProd A cb tr α γ t s := by
  simp only [accAt_prod]
  rw [prodF_swap (fun j r => phiG (rEnv A cb tr t r) α γ (tb A t).interactions (f j))]
  unfold sideProd
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [hf r]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact phi_row A cb tr hH ht α γ (List.mem_range.mp hr) (List.mem_filter.mp hi).1

theorem sends_table (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ : Fp8) :
    ((finsT A cb tr α γ t).take (layT A tr t).sendG).foldl (· * ·) 1 = sideProd A cb tr α γ t true := by
  have hk : (layT A tr t).sendG = ((tb A t).interactions.filter fun i => i.send == true).length :=
    numSide_eq _ true
  have hle : (layT A tr t).sendG ≤ nG A t := by unfold nG; exact Nat.le_add_right _ _
  show prodF _ = _
  unfold finsT
  rw [← List.map_take, List.take_range, Nat.min_eq_left hle]
  refine rows_side A cb tr hH ht α γ true _ id hk fun r => ?_
  have := prod_phiG_send (rEnv A cb tr t r) α γ (tb A t).interactions
  simp only [beq_true] at hk ⊢
  rw [hk]; exact this

theorem recvs_table (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ : Fp8) :
    ((finsT A cb tr α γ t).drop (layT A tr t).sendG).foldl (· * ·) 1 = sideProd A cb tr α γ t false := by
  have hk : (layT A tr t).sendG = ((tb A t).interactions.filter fun i => i.send == true).length :=
    numSide_eq _ true
  have hk' : (layT A tr t).recvG = ((tb A t).interactions.filter fun i => i.send == false).length :=
    numSide_eq _ false
  show prodF _ = _
  unfold finsT
  rw [show nG A t = (layT A tr t).sendG + (layT A tr t).recvG from rfl, List.range_add, List.map_append,
    List.drop_left' (by simp), List.map_map]
  refine rows_side A cb tr hH ht α γ false _ _ hk' fun r => ?_
  have := prod_phiG_recv (rEnv A cb tr t r) α γ (tb A t).interactions
  simp only [beq_true, beq_false] at hk hk' ⊢
  rw [hk', hk]; exact this

end

theorem busProd : BusProdStmt := by
  intro A cb tr hH hok α γ
  let g : Nat × List Fp → Fp8 := fun k => γ - FPv α k.1 k.2
  have hside : ∀ s, prodF ((List.range A.tables.length).map fun t => sideProd A cb tr α γ t s) =
      prodPow g (entries A cb tr s) := by
    intro s
    unfold prodPow entries
    rw [List.map_flatMap, prodF_flatMap]
    congr 1; apply List.map_congr_left; intro t _
    unfold sideProd
    rw [List.map_flatMap, prodF_flatMap]
    congr 1; apply List.map_congr_left; intro r _
    rw [List.map_map]; rfl
  have hl : ∀ s, ((List.range A.tables.length).map fun t =>
      (if s then ((finsT A cb tr α γ t).take (layT A tr t).sendG).foldl (· * ·) 1
       else ((finsT A cb tr α γ t).drop (layT A tr t).sendG).foldl (· * ·) 1)) =
      (List.range A.tables.length).map fun t => sideProd A cb tr α γ t s := by
    intro s
    apply List.map_congr_left; intro t ht
    have hto := tabOk A tr hok (List.mem_range.mp ht)
    cases s
    · exact recvs_table A cb tr hH hto α γ
    · exact sends_table A cb tr hH hto α γ
  have h1 := hl true
  have h2 := hl false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
  show prodF _ = prodF _
  rw [h1, h2, hside true, hside false]
  apply prodPow_eq g _ _ _ (Nat.le_refl _)
  intro k
  obtain ⟨b, m⟩ := k
  rw [cnt_entries, cnt_entries, hH.balance]

end ZkFormal.V2.PG

namespace ZkFormal.V2.PG

/-- **The clear-text checks pass** on every honest complete transcript. -/
theorem globalStmt : GlobalStmt := global_of busProd

end ZkFormal.V2.PG
