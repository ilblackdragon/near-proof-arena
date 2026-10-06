import ZkFormal.V2.PG.NpBus2

/-!
# ZkFormal.V2.PG.NpBus3 (P2 copy of `Prover.NpBus3` at `dp = pg g`) — the honest factors on the trace domain and the bus equation
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem colBound_inter {t : Nat} (h : Air.Table.wf A (2 ^ dp.logBlowup) (tb A t) = true)
    {i : Interaction} (hi : i ∈ (tb A t).interactions) :
    ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ (tb A t).width :=
  fun e he => colBound_of_wf A h e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, he⟩))

theorem goV_eval (t r : Nat) : ∀ (bs : List Expr) (s : Nat),
    (∀ b ∈ bs, b.evalWith (rEnv A cb tr t r) = Fp8.ofBase (b.eval tr t r (pubOf Fp cb))) →
    goV (bs.map (·.evalWith (rEnv A cb tr t r))) s = Interaction.multNat.go tr t r (pubOf Fp cb) bs s
  | [], _, _ => rfl
  | b :: bs, s, h => by
    rw [List.map_cons]
    show (if _ = 1 then 2 ^ s else 0) + _ = (if b.eval tr t r (pubOf Fp cb) = 1 then 2 ^ s else 0) + _
    rw [h b (by simp), goV_eval t r bs (s + 1) (fun b' hb' => h b' (by simp [hb']))]
    congr 1
    by_cases hv : b.eval tr t r (pubOf Fp cb) = 1
    · rw [if_pos hv, if_pos (by rw [hv]; rfl)]
    · rw [if_neg hv, if_neg (fun h' => hv (Fp8.ofBase_inj (h'.trans rfl)))]

theorem fp_fold_eval (env : Env Fp8) (α : Fp8) (vals : Expr → Fp) : ∀ (msg : List Expr) (a : Fp8 × Fp8),
    (∀ e ∈ msg, e.evalWith env = Fp8.ofBase (vals e)) →
    msg.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith env * acc.2, acc.2 * α)) a =
      ((msg.map vals).map Fp8.ofBase).foldl (fun (acc : Fp8 × Fp8) v => (acc.1 + v * acc.2, acc.2 * α)) a
  | [], _, _ => rfl
  | e :: msg, a, h => by
    simp only [List.foldl_cons, List.map_cons]
    rw [h e (by simp)]
    exact fp_fold_eval env α vals msg _ (fun e' he' => h e' (by simp [he']))

/-- **The honest factor of an interaction on row `r`.** -/
theorem phi_row (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ : Fp8)
    {r : Nat} (hr : r < 2 ^ lg tr t) {i : Interaction} (hi : i ∈ (tb A t).interactions) :
    (chainOf (rEnv A cb tr t r) α γ i).2 =
      (γ - FPv α i.bus (i.msgVal tr t r (pubOf Fp cb))) ^ (i.multNat tr t r (pubOf Fp cb)) := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  have hcol := colBound_inter A ht.wf hi
  have hev : ∀ e ∈ i.mult ++ i.msg, e.evalWith (rEnv A cb tr t r) = Fp8.ofBase (e.eval tr t r (pubOf Fp cb)) :=
    fun e he => evalWith_row A cb tr t hlog hr e (hcol e he)
  have hbits : ∀ v ∈ i.mult.map (·.evalWith (rEnv A cb tr t r)), v = 0 ∨ v = 1 := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    rw [hev b (List.mem_append_left _ hb)]
    rcases hH.bits t ht.lt r hr i (by rw [← tb_eq A ht.lt]; exact hi) b hb with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfp : fingerprint (rEnv A cb tr t r) α i = FPv α i.bus (i.msgVal tr t r (pubOf Fp cb)) := by
    unfold fingerprint FPv Interaction.msgVal
    rw [fp_fold_eval (rEnv A cb tr t r) α (fun e => e.eval tr t r (pubOf Fp cb)) i.msg (0, 1)
      (fun e he => hev e (List.mem_append_right _ he))]
  rw [chain_phi _ α γ i hbits, goV_eval A cb tr t r i.mult 0 (fun b hb => hev b (List.mem_append_left _ hb)),
    hfp]
  rfl

theorem foldl_mul_map {β : Type} (f : β → Fp8) : ∀ (l : List β) (c : Fp8),
    l.foldl (fun a x => a * f x) c = c * prodF (l.map f)
  | [], c => by simp [prodF_nil]; grind
  | x :: l, c => by rw [List.foldl_cons, foldl_mul_map f l, List.map_cons, prodF_cons]; grind

theorem accAt_prod (α γ : Fp8) (t r j : Nat) :
    accAt A cb tr α γ t r j =
      prodF ((List.range r).map fun r' => phiG (rEnv A cb tr t r') α γ (tb A t).interactions j) := by
  unfold accAt; rw [foldl_mul_map]; grind

theorem phis_filter (env : Env Fp8) (α γ : Fp8) (is : List Interaction) (s : Bool) :
    (phisOf env α γ is).filter (fun p => p.1.send == s) =
      (is.filter fun i => i.send == s).map fun i => (i, (chainOf env α γ i).2) := by
  unfold phisOf; rw [List.filter_map]; rfl

theorem groups_eq (env : Env Fp8) (α γ : Fp8) (is : List Interaction) :
    groupsOf env α γ is = ((is.filter fun i => i.send).map fun i => [(i, (chainOf env α γ i).2)]) ++
      ((is.filter fun i => !i.send).map fun i => [(i, (chainOf env α γ i).2)]) := by
  unfold groupsOf
  simp only [dp, V2.G.pg, Params.default, show max 1 1 = 1 from rfl, chunksOf_one]
  have h1 := phis_filter env α γ is true
  have h2 := phis_filter env α γ is false
  simp only [beq_true, beq_false] at h1 h2
  rw [h1, h2, List.map_map, List.map_map]; rfl

/-- The product of the group factors of one side, on a row. -/
theorem prod_phiG_send (env : Env Fp8) (α γ : Fp8) (is : List Interaction) :
    prodF ((List.range (is.filter fun i => i.send).length).map (phiG env α γ is)) =
      prodF ((is.filter fun i => i.send).map fun i => (chainOf env α γ i).2) := by
  have e : (List.range (is.filter fun i => i.send).length).map (phiG env α γ is) =
      (is.filter fun i => i.send).map fun i => 1 * (chainOf env α γ i).2 := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold phiG
    rw [groups_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact h1)]
    simp [h1]
  rw [e, prodF_map_mul, prodF_map_one]; grind

theorem prod_phiG_recv (env : Env Fp8) (α γ : Fp8) (is : List Interaction) :
    prodF ((List.range (is.filter fun i => !i.send).length).map
        fun j => phiG env α γ is ((is.filter fun i => i.send).length + j)) =
      prodF ((is.filter fun i => !i.send).map fun i => (chainOf env α γ i).2) := by
  have e : (List.range (is.filter fun i => !i.send).length).map
        (fun j => phiG env α γ is ((is.filter fun i => i.send).length + j)) =
      (is.filter fun i => !i.send).map fun i => 1 * (chainOf env α γ i).2 := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold phiG
    rw [groups_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp [h1]
  rw [e, prodF_map_mul, prodF_map_one]; grind

end

end ZkFormal.V2.PG
