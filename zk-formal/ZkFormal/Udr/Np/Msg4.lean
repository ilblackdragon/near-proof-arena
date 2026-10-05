import ZkFormal.Udr.Np.AuxChain

/-!
# ZkFormal.Udr.Np.Msg4 — the aux commitment round

If the aux columns are close, every constraint (including the aux chain and
running-product constraints) vanishes on the trace domain, and the bus
equation holds on the finals, then the decoded trace satisfies all local
constraints and the grand products of the two sides agree.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Products -/

theorem prod_append_single (l : List Fp8) (x : Fp8) : (l ++ [x]).prod = l.prod * x := by
  induction l with
  | nil => simp only [List.nil_append, List.prod_cons, List.prod_nil]; grind
  | cons a l ih => simp only [List.cons_append, List.prod_cons, ih]; grind

theorem prod_append' (l l' : List Fp8) : (l ++ l').prod = l.prod * l'.prod := by
  induction l with
  | nil => simp only [List.nil_append, List.prod_nil]; grind
  | cons a l ih => simp only [List.cons_append, List.prod_cons, ih]; grind

theorem foldl_mul_prod (l : List Fp8) (a : Fp8) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.prod_nil]; grind
  | cons b l ih => simp only [List.foldl_cons, List.prod_cons, ih]; grind

theorem prod_map_mul {β : Type} (l : List β) (f g : β → Fp8) :
    (l.map fun b => f b * g b).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil]; grind
  | cons b l ih => simp only [List.map_cons, List.prod_cons, ih]; grind

theorem prod_swap {β δ : Type} (l1 : List β) (l2 : List δ) (f : β → δ → Fp8) :
    (l1.map fun a => (l2.map (f a)).prod).prod = (l2.map fun b => (l1.map fun a => f a b).prod).prod := by
  induction l1 with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    induction l2 with
    | nil => rfl
    | cons b l2 ih => simp only [List.map_cons, List.prod_cons, ← ih]; grind
  | cons a l1 ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    rw [← prod_map_mul]

theorem prod_flatMap {β δ : Type} (l : List β) (g : β → List δ) (F : δ → Fp8) :
    ((l.flatMap g).map F).prod = (l.map fun b => ((g b).map F).prod).prod := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.map_append, prod_append', ih, List.map_cons,
      List.prod_cons]

theorem prod_replicate' (k : Nat) (x : Fp8) : (List.replicate k x).prod = x ^ k := by
  induction k with
  | zero => simp only [List.replicate_zero, List.prod_nil, Semiring.pow_zero]
  | succ k ih => rw [List.replicate_succ, List.prod_cons, ih, Semiring.pow_succ]; grind

theorem prod_expand (l : List (List Fp8 × Nat)) (F : List Fp8 → Fp8) :
    ((expand l).map F).prod = (l.map fun p => F p.1 ^ p.2).prod := by
  unfold expand
  rw [prod_flatMap]
  congr 1
  apply List.map_congr_left
  intro ⟨m, k⟩ _
  simp only [List.map_replicate, prod_replicate']

/-! ## The running product -/

theorem running_prod (T : Nat) (hT : 1 ≤ T) (a an φ isF isT isL : Nat → Fp8) (fin : Fp8)
    (hF : ∀ r, r < T → isF r = if r = 0 then 1 else 0)
    (hTr : ∀ r, r < T → isT r = if r + 1 = T then 0 else 1)
    (hL : ∀ r, r < T → isL r = if r + 1 = T then 1 else 0)
    (han : ∀ r, r + 1 < T → an r = a (r + 1))
    (h1 : ∀ r, r < T → isF r * (a r - 1) = 0) (h2 : ∀ r, r < T → isT r * (an r - a r * φ r) = 0)
    (h3 : ∀ r, r < T → isL r * (a r * φ r - fin) = 0) :
    fin = ((List.range T).map φ).prod := by
  have ha : ∀ r, r < T → a r = ((List.range r).map φ).prod := by
    intro r hr
    induction r with
    | zero =>
      have := h1 0 hT; rw [hF 0 hT, if_pos rfl] at this
      simp only [List.range_zero, List.map_nil, List.prod_nil]; grind
    | succ r ih =>
      have := h2 r (by omega); rw [hTr r (by omega), if_neg (by omega), han r hr] at this
      rw [List.range_succ, List.map_append, List.map_singleton, prod_append_single, ← ih (by omega)]
      grind
  have := h3 (T - 1) (by omega)
  rw [hL (T - 1) (by omega), if_pos (by omega), ha (T - 1) (by omega)] at this
  conv => rhs; rw [show T = T - 1 + 1 by omega, List.range_succ, List.map_append, List.map_singleton,
    prod_append_single]
  grind

/-! ## One table -/

theorem bits_bool_of (env : Env Fp8) (henv1 : env.ofNat 1 = 1)
    (hadd : ∀ a b, env.add a b = a + b) (hmul : ∀ a b, env.mul a b = a * b) (hneg : ∀ a, env.neg a = -a)
    (Tb : Air.Table) (hz : ∀ e ∈ Tb.allConstraints, e.evalWith env = 0) :
    ∀ i ∈ Tb.interactions, ∀ b ∈ i.mult, b.evalWith env = 0 ∨ b.evalWith env = 1 := by
  intro i hi b hb
  have h0 := hz _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨b, hb, rfl⟩⟩))
  change env.mul (b.evalWith env) (env.add (b.evalWith env) (env.neg (env.ofNat 1))) = 0 at h0
  rw [hmul, hadd, hneg, henv1] at h0
  rcases ZkFormal.Udr.gp_mul_eq_zero h0 with h | h
  · exact Or.inl h
  · exact Or.inr (by grind)

section
variable (A : Air)

local notation "prm0" => Params.default

theorem table_fins (τ : PTn) (t : Nat) (αfp γ : Fp8)
    (hlog : (tl A prm0 τ t).log ≤ 27)
    (haux : (tl A prm0 τ t).aux = nCons (tableOf A t).interactions + (tableOf A t).interactions.length)
    (hfins : (finsOf A prm0 τ t).length = (tableOf A t).interactions.length)
    (hz : ∀ r, r < 2 ^ (tl A prm0 τ t).log →
      ∀ c ∈ csAt A prm0 τ t αfp γ (omg (tl A prm0 τ t).log ^ r), c = 0)
    (j : Nat) (hj : j < (ordOf (tableOf A t).interactions).length) :
    (finsOf A prm0 τ t).getD j 0 = ((List.range (2 ^ (tl A prm0 τ t).log)).map fun r =>
      phiOf (polyEnv A prm0 τ t (omg (tl A prm0 τ t).log ^ r)) αfp γ
        ((ordOf (tableOf A t).interactions).getD j default)).prod := by
  have hord : (ordOf (tableOf A t).interactions).length = (tableOf A t).interactions.length := by
    unfold ordOf; rw [List.length_append]
    have := length_filter_send (tableOf A t).interactions
    have e1 : (tableOf A t).interactions.filter (fun i => i.send) =
        (tableOf A t).interactions.filter (fun i => i.send == true) :=
      List.filter_congr fun i _ => by cases i.send <;> rfl
    have e2 : (tableOf A t).interactions.filter (fun i => !i.send) =
        (tableOf A t).interactions.filter (fun i => i.send == false) :=
      List.filter_congr fun i _ => by cases i.send <;> rfl
    rw [e1, e2]; exact this
  let log := (tl A prm0 τ t).log
  let ω := omg log
  let cj := nCons (tableOf A t).interactions + j
  have hsem : ∀ r, r < 2 ^ log → _ := fun r hr => by
    have hzr := hz r hr
    unfold csAt at hzr
    have hall : ∀ e ∈ (tableOf A t).allConstraints, e.evalWith (polyEnv A prm0 τ t (ω ^ r)) = 0 :=
      fun e he => hzr _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    have hb := bits_bool_of (polyEnv A prm0 τ t (ω ^ r)) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) _ hall
    exact auxC_sem (tableOf A t) (polyEnv A prm0 τ t (ω ^ r)) αfp γ
      ((List.range (tl A prm0 τ t).aux).map fun a => colAt A prm0 τ ⟨t, 1, a⟩ (ω ^ r))
      ((List.range (tl A prm0 τ t).aux).map fun a => colAt A prm0 τ ⟨t, 1, a⟩ (ω * ω ^ r))
      (finsOf A prm0 τ t) hb (by simp; omega) (fun c hc => hzr c (List.mem_append_right _ hc)) j hj
      (by simp; omega) (by simp; omega) (by omega)
  have hgetZ : ∀ x, ((List.range (tl A prm0 τ t).aux).map fun a => colAt A prm0 τ ⟨t, 1, a⟩ x).getD cj 0 =
      colAt A prm0 τ ⟨t, 1, cj⟩ x := fun x => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  refine running_prod (2 ^ log) (Nat.two_pow_pos _)
    (fun r => colAt A prm0 τ ⟨t, 1, cj⟩ (ω ^ r)) (fun r => colAt A prm0 τ ⟨t, 1, cj⟩ (ω * ω ^ r))
    (fun r => phiOf (polyEnv A prm0 τ t (ω ^ r)) αfp γ ((ordOf (tableOf A t).interactions).getD j default))
    (fun r => (polyEnv A prm0 τ t (ω ^ r)).isFirst) (fun r => (polyEnv A prm0 τ t (ω ^ r)).isTransition)
    (fun r => (polyEnv A prm0 τ t (ω ^ r)).isLast) _
    (fun r hr => selSum_omg hlog hr)
    (fun r hr => by
      show 1 - selSum (2 ^ log) (ω * ω ^ r) = _
      rw [selSum_omg_next hlog hr]; split <;> grind)
    (fun r hr => selSum_omg_next hlog hr)
    (fun r _ => by show colAt A prm0 τ ⟨t, 1, cj⟩ (ω * ω ^ r) = colAt A prm0 τ ⟨t, 1, cj⟩ (ω ^ (r + 1))
                   rw [Semiring.pow_succ]; congr 1; grind)
    (fun r hr => by have := (hsem r hr).1; rw [hgetZ] at this; exact this)
    (fun r hr => by have := (hsem r hr).2.1; rw [hgetZ, hgetZ] at this; exact this)
    (fun r hr => by have := (hsem r hr).2.2; rw [hgetZ] at this; exact this)

end

/-! ## The factors on the decoded trace -/

theorem fp_foldl (env : Env Fp8) (α : Fp8) : ∀ (l : List Expr) (a b : Fp8),
    l.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith env * acc.2, acc.2 * α)) (a, b) =
      (a + b * combine α (l.map (·.evalWith env)), b * α ^ l.length)
  | [], a, b => by
    rw [List.foldl_nil]
    refine Prod.ext ?_ ?_
    · show a = a + b * 0; grind
    · show b = b * α ^ 0; rw [Semiring.pow_zero]; grind
  | e :: l, a, b => by
    rw [List.foldl_cons, fp_foldl env α l]
    refine Prod.ext ?_ ?_
    · show a + e.evalWith env * b + b * α * combine α (l.map (·.evalWith env)) =
        a + b * (e.evalWith env + α * combine α (l.map (·.evalWith env)))
      generalize combine α (l.map (·.evalWith env)) = C
      generalize e.evalWith env = v
      grind
    · show b * α * α ^ l.length = b * α ^ (l.length + 1)
      rw [Semiring.pow_succ]
      generalize α ^ l.length = P
      grind

theorem combine_snoc (α z : Fp8) : ∀ l : List Fp8, combine α (l ++ [z]) = combine α l + α ^ l.length * z
  | [] => by
    show z + α * 0 = 0 + α ^ 0 * z
    rw [Semiring.pow_zero]; grind
  | c :: l => by
    have := combine_snoc α z l
    show c + α * combine α (l ++ [z]) = c + α * combine α l + α ^ (l.length + 1) * z
    rw [this, Semiring.pow_succ]
    generalize combine α l = C
    generalize α ^ l.length = P
    grind

theorem fingerprint_eq (env : Env Fp8) (α : Fp8) (i : Interaction) :
    fingerprint env α i = fpL α (i.msg.map (·.evalWith env) ++ [((i.bus + 1 : Nat) : Fp8)]) := by
  unfold fingerprint fpL
  rw [fp_foldl, combine_snoc, List.length_map]
  have hc : (@Nat.cast Fp8 Semiring.natCast (i.bus + 1)) = ((i.bus + 1 : Nat) : Fp8) := rfl
  dsimp only
  rw [hc]
  generalize combine α (i.msg.map (·.evalWith env)) = C
  generalize α ^ i.msg.length = P
  generalize ((i.bus + 1 : Nat) : Fp8) = B
  grind

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem multNat_go_bval (tr : Air.Trace F) (t r : Nat) (pub : List F) (v : Expr → Fp8)
    (hv : ∀ b, v b = 1 ↔ b.eval tr t r pub = 1) :
    ∀ (bs : List Expr) (k : Nat), Interaction.multNat.go tr t r pub bs k = 2 ^ k * bval (bs.map v)
  | [], k => by simp [Interaction.multNat.go, bval]
  | b :: bs, k => by
    rw [Interaction.multNat.go, multNat_go_bval tr t r pub v hv bs (k + 1)]
    simp only [List.map_cons, bval]
    by_cases h : b.eval tr t r pub = 1
    · rw [if_pos h, if_pos ((hv b).mpr h), Nat.pow_succ]; grind
    · rw [if_neg h, if_neg (fun h' => h ((hv b).mp h')), Nat.pow_succ]; grind

end

theorem phiOf_eq (A : Air) (τ : PTn) (t : Nat)
    (hdl : (hdrOf τ).getD t 0 = (tl A Params.default τ t).log) (hlog : (tl A Params.default τ t).log ≤ 27)
    (hbase : ∀ (c j : Nat), (colAt A Params.default τ ⟨t, 0, c⟩ (omg (tl A Params.default τ t).log ^ j)).IsBase)
    (r : Nat) (hr : r < 2 ^ (tl A Params.default τ t).log) (α γ : Fp8) (i : Interaction) :
    phiOf (polyEnv A Params.default τ t (omg (tl A Params.default τ t).log ^ r)) α γ i =
      (γ - fpL α ((i.msgVal (decTrace A Params.default τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase ++
        [((i.bus + 1 : Nat) : Fp8)])) ^ i.multNat (decTrace A Params.default τ) t r (pubOf Fp τ.cb) := by
  have hh := evalWith_hom A Params.default τ t hdl hlog hbase r hr
  unfold phiOf
  rw [fingerprint_eq]
  have e1 : i.msg.map (·.evalWith (polyEnv A Params.default τ t (omg (tl A Params.default τ t).log ^ r))) =
      (i.msgVal (decTrace A Params.default τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase := by
    unfold Interaction.msgVal; rw [List.map_map]
    exact List.map_congr_left fun e _ => hh e
  rw [e1]
  congr 1
  unfold Interaction.multNat
  rw [multNat_go_bval _ t r _ (fun b => b.evalWith (polyEnv A Params.default τ t
    (omg (tl A Params.default τ t).log ^ r))) (fun b => by
      rw [hh b]; exact ⟨fun h => Fp8.ofBase_inj h, fun h => by rw [h]; rfl⟩) i.mult 0]
  simp

/-! ## Grand products as triple products -/

theorem gp_side (A : Air) (prm : Params) (τ : PTn) (s : Bool) (α γ : Fp8) :
    ((expand (busMsgs A prm τ s)).map fun m => γ - fpL α m).prod =
      ((List.range A.tables.length).map fun t =>
        ((List.range ((decTrace A prm τ).height t)).map fun r =>
          (((tableOf A t).interactions.filter (·.send == s)).map fun i =>
            (γ - fpL α ((i.msgVal (decTrace A prm τ) t r (pubOf Fp τ.cb)).map Fp8.ofBase ++
              [((i.bus + 1 : Nat) : Fp8)])) ^ i.multNat (decTrace A prm τ) t r (pubOf Fp τ.cb)).prod).prod).prod := by
  rw [prod_expand]
  simp only [busMsgs]
  rw [prod_flatMap]
  congr 1; apply List.map_congr_left; intro t _
  rw [prod_flatMap]
  congr 1; apply List.map_congr_left; intro r _
  rw [List.map_map]; rfl

/-- Splitting the finals per table (the `BusFinalsFail` fold). -/
theorem finals_split (n : TLayout → Nat) : ∀ (lay : List TLayout) (acc : List (List Fp8)) (fin : List Fp8),
    (lay.foldl (fun (acc : List (List Fp8) × List Fp8) L => (acc.1 ++ [acc.2.take (n L)], acc.2.drop (n L)))
      (acc, fin)).1 =
    acc ++ (List.range lay.length).map fun t =>
      (fin.drop ((lay.take t).map n).sum).take (n (lay.getD t default))
  | [], acc, fin => by simp
  | L :: lay, acc, fin => by
    rw [List.foldl_cons, finals_split n lay, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.append_assoc, List.cons_append, List.nil_append,
      List.take_zero, List.map_nil, List.sum_nil, List.drop_zero, List.getD_cons_zero]
    congr 2
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ,
      List.drop_drop]

end ZkFormal.Udr.Np
