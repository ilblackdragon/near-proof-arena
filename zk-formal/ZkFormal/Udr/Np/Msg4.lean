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

/-! ## Sides of one table -/

theorem filter_send_eq (is : List Interaction) :
    is.filter (fun i => i.send) = is.filter (fun i => i.send == true) :=
  List.filter_congr fun i _ => by cases i.send <;> rfl

theorem filter_recv_eq (is : List Interaction) :
    is.filter (fun i => !i.send) = is.filter (fun i => i.send == false) :=
  List.filter_congr fun i _ => by cases i.send <;> rfl

theorem table_side (is : List Interaction) (fins : List Fp8) (Φ : Interaction → Fp8)
    (hlen : fins.length = is.length)
    (hj : ∀ j, j < (ordOf is).length → fins.getD j 0 = Φ ((ordOf is).getD j default)) :
    (fins.take (is.filter (fun i => i.send)).length).prod = ((is.filter (fun i => i.send)).map Φ).prod ∧
    (fins.drop (is.filter (fun i => i.send)).length).prod = ((is.filter (fun i => !i.send)).map Φ).prod := by
  have hs := length_filter_send is
  rw [← filter_send_eq, ← filter_recv_eq] at hs
  have hord : ordOf is = is.filter (fun i => i.send) ++ is.filter (fun i => !i.send) := rfl
  have hordl : (ordOf is).length = is.length := by rw [hord, List.length_append]; omega
  generalize hA : is.filter (fun i => i.send) = SA at *
  generalize hB : is.filter (fun i => !i.send) = SB at *
  constructor
  · congr 1
    refine List.ext_getElem (by rw [List.length_take, List.length_map]; omega) fun j h1 h2 => ?_
    rw [List.length_map] at h2
    rw [List.getElem_take, List.getElem_map]
    have := hj j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    simp only [hord]
    rw [List.getElem_append_left]
  · congr 1
    refine List.ext_getElem (by rw [List.length_drop, List.length_map]; omega) fun j h1 h2 => ?_
    rw [List.length_map] at h2
    rw [List.getElem_drop, List.getElem_map]
    have := hj (SA.length + j) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    simp only [hord]
    rw [List.getElem_append_right (by omega)]
    congr 1; omega

theorem sum_take_le (n : TLayout → Nat) (lay : List TLayout) (t : Nat) (ht : t < lay.length) :
    ((lay.take t).map n).sum + n (lay.getD t default) ≤ (lay.map n).sum := by
  have e : lay = lay.take t ++ lay[t] :: lay.drop (t + 1) := by
    conv => lhs; rw [← List.take_append_drop t lay]
    rw [List.drop_eq_getElem_cons ht]
  have e2 : lay.getD t default = lay[t] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  conv => rhs; rw [e]
  rw [e2, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  omega

theorem zip_range_map {β : Type} [Inhabited β] (n : Nat) (f : Nat → List Fp8) (l : List β) (hl : l.length = n) :
    ((List.range n).map f).zip l = (List.range n).map fun t => (f t, l.getD t default) := by
  refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h2; omega)]
  rfl

/-! ## Per-table facts of a shaped transcript -/

section
variable {A : Air}

local notation "prm0" => Params.default

structure TabOk (A : Air) (τ : PTn) (t : Nat) : Prop where
  hdl : (hdrOf τ).getD t 0 = (tl A prm0 τ t).log
  hlog : (tl A prm0 τ t).log ≤ 27
  hbase : ∀ (c j : Nat), (colAt A prm0 τ ⟨t, 0, c⟩ (omg (tl A prm0 τ t).log ^ j)).IsBase
  haux : (tl A prm0 τ t).aux = nCons (tableOf A t).interactions + (tableOf A t).interactions.length
  hsend : (tl A prm0 τ t).sendG = ((tableOf A t).interactions.filter (fun i => i.send)).length
  hn : (tl A prm0 τ t).sendG + (tl A prm0 τ t).recvG = (tableOf A t).interactions.length

theorem tabOk_of {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm0 l = true)
    (t : Nat) (ht : t < A.tables.length) : TabOk A τ t := by
  obtain ⟨hlen, hlog, hwf, _⟩ := headerOk_facts hh
  have htl := tl_eq (prm := prm0) hl hlen t ht
  have hlt := hlog t ht (by omega)
  have hmx := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
  have hs := length_filter_send (tableOf A t).interactions
  rw [← filter_send_eq, ← filter_recv_eq] at hs
  have hT := tableOf_lt ht
  rw [hT] at hs
  refine ⟨?_, ?_, fun c j => ?_, ?_, ?_, ?_⟩
  · rw [htl]; unfold hdrOf; rw [hl]
    simp only [Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < l.length by omega)]
  · rw [htl]; show l[t] ≤ 27; omega
  · have e : omg (tl A prm0 τ t).log ^ j = Fp8.ofBase (Fp.twoAdicGen (tl A prm0 τ t).log ^ j) := by
      unfold omg; rw [ofBase_pow]
    rw [e]
    refine colAt_base τ ⟨t, 0, c⟩ rfl (by rw [htl]) rfl ?_ _
    rw [htl]; show l[t] + 4 ≤ 27
    have := hlt.2.2; simp [Params.default] at this; omega
  · rw [htl, hT]
    show (A.tables[t]).auxCount 1 = _
    unfold Air.Table.auxCount nCons Air.Table.numSide
    rw [numGroups_one, numGroups_one, ← filter_send_eq, ← filter_recv_eq]; omega
  · rw [htl, hT]; show numGroups _ 1 = _
    rw [numGroups_one]; unfold Air.Table.numSide; rw [filter_send_eq]
  · rw [htl, hT]; show numGroups _ 1 + numGroups _ 1 = _
    rw [numGroups_one, numGroups_one]; unfold Air.Table.numSide
    rw [← filter_send_eq, ← filter_recv_eq]; omega

theorem finsOf_length {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm0 l = true)
    (hfl : (finalsOf τ).length = ((layOf A prm0 τ).map fun L => L.sendG + L.recvG).sum)
    (t : Nat) (ht : t < A.tables.length) :
    (finsOf A prm0 τ t).length = (tableOf A t).interactions.length := by
  obtain ⟨hlen, _, _, _⟩ := headerOk_facts hh
  have hlay : (layOf A prm0 τ).length = A.tables.length := by
    unfold layOf hdrOf; rw [hl]; simp [layout, hlen]
  have := sum_take_le (fun L => L.sendG + L.recvG) (layOf A prm0 τ) t (by omega)
  unfold finsOf
  rw [List.length_take, List.length_drop, ← (tabOk_of hl hh t ht).hn]
  unfold tl at *
  omega

end

/-! ## The two contradictions -/

section
variable {A : Air}

local notation "prm0" => Params.default

theorem no_localFail {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm0 l = true)
    (α γ : Fp8)
    (hz : ∀ t, t < A.tables.length → ∀ r, r < 2 ^ (tl A prm0 τ t).log →
      ∀ c ∈ csAt A prm0 τ t α γ (omg (tl A prm0 τ t).log ^ r), c = 0) :
    ¬ LocalFail A prm0 τ := by
  rintro ⟨t, ht, r, hr, e, he, hne⟩
  have tab := tabOk_of hl hh t ht
  have hr' : r < 2 ^ (tl A prm0 τ t).log := by
    have : (decTrace A prm0 τ).height t = 2 ^ (hdrOf τ).getD t 0 := rfl
    rw [this, tab.hdl] at hr; exact hr
  have h1 := evalWith_hom A prm0 τ t tab.hdl tab.hlog tab.hbase r hr' e
  have h2 := hz t ht r hr' _ (by unfold csAt; exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  rw [h1] at h2
  exact hne (Fp8.ofBase_inj (h2.trans rfl))

/-- The per-table factor product `Φ_t(i) = ∏_r φ_i(ω^r)`. -/
noncomputable def PhiT (A : Air) (τ : PTn) (α γ : Fp8) (t : Nat) (i : Interaction) : Fp8 :=
  ((List.range (2 ^ (tl A prm0 τ t).log)).map fun r =>
    phiOf (polyEnv A prm0 τ t (omg (tl A prm0 τ t).log ^ r)) α γ i).prod

theorem gp_tables {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm0 l = true)
    (α γ : Fp8) (s : Bool) :
    ((expand (busMsgs A prm0 τ s)).map fun m => γ - fpL α m).prod =
      ((List.range A.tables.length).map fun t =>
        (((tableOf A t).interactions.filter (fun i => i.send == s)).map (PhiT A τ α γ t)).prod).prod := by
  rw [gp_side]
  congr 1
  apply List.map_congr_left
  intro t ht
  have tab := tabOk_of hl hh t (List.mem_range.mp ht)
  have hh' : (decTrace A prm0 τ).height t = 2 ^ (tl A prm0 τ t).log := by
    show 2 ^ (hdrOf τ).getD t 0 = _; rw [tab.hdl]
  rw [hh']
  unfold PhiT
  rw [prod_swap]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  apply List.map_congr_left
  intro r hr
  exact (phiOf_eq A τ t tab.hdl tab.hlog tab.hbase r (List.mem_range.mp hr) α γ i).symm

theorem no_gpDiffer {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm0 l = true)
    (hfl : (finalsOf τ).length = ((layOf A prm0 τ).map fun L => L.sendG + L.recvG).sum)
    (α γ : Fp8)
    (hz : ∀ t, t < A.tables.length → ∀ r, r < 2 ^ (tl A prm0 τ t).log →
      ∀ c ∈ csAt A prm0 τ t α γ (omg (tl A prm0 τ t).log ^ r), c = 0)
    (hBF : ¬ BusFinalsFail A prm0 τ) : ¬ GpDiffer A prm0 τ α γ := by
  obtain ⟨hlen, _, _, _⟩ := headerOk_facts hh
  have hlay : (layOf A prm0 τ).length = A.tables.length := by
    unfold layOf hdrOf; rw [hl]; simp [layout, hlen]
  have hside : ∀ t, t < A.tables.length →
      ((finsOf A prm0 τ t).take (tl A prm0 τ t).sendG).prod =
        (((tableOf A t).interactions.filter (fun i => i.send == true)).map (PhiT A τ α γ t)).prod ∧
      ((finsOf A prm0 τ t).drop (tl A prm0 τ t).sendG).prod =
        (((tableOf A t).interactions.filter (fun i => i.send == false)).map (PhiT A τ α γ t)).prod := by
    intro t ht
    have tab := tabOk_of hl hh t ht
    have := table_side (tableOf A t).interactions (finsOf A prm0 τ t) (PhiT A τ α γ t)
      (finsOf_length hl hh hfl t ht) (fun j hj => table_fins A τ t α γ tab.hlog tab.haux
        (finsOf_length hl hh hfl t ht) (hz t ht) j hj)
    rw [tab.hsend, ← filter_send_eq, ← filter_recv_eq]
    exact this
  intro hgp
  apply hBF
  unfold BusFinalsFail
  have hsplit := finals_split (fun L => L.sendG + L.recvG) (layOf A prm0 τ) [] (finalsOf τ)
  simp only [List.nil_append] at hsplit
  dsimp only
  rw [hsplit, zip_range_map _ _ _ rfl, List.map_map, List.map_map, foldl_mul_prod, foldl_mul_prod]
  have hmap : ∀ (F G : Nat → Fp8), (∀ t, t < A.tables.length → F t = G t) →
      ((List.range (layOf A prm0 τ).length).map F).prod = ((List.range A.tables.length).map G).prod :=
    fun F G hFG => by rw [hlay]; congr 1; exact List.map_congr_left fun t ht => hFG t (List.mem_range.mp ht)
  have e1 : ∀ x : Fp8, 1 * x = x := fun x => by grind
  rw [e1, e1, hmap _ (fun t => (((tableOf A t).interactions.filter (fun i => i.send == true)).map
      (PhiT A τ α γ t)).prod) (fun t ht => ?_),
    hmap _ (fun t => (((tableOf A t).interactions.filter (fun i => i.send == false)).map
      (PhiT A τ α γ t)).prod) (fun t ht => ?_), ← gp_tables hl hh, ← gp_tables hl hh]
  · exact hgp
  · show ((finsOf A prm0 τ t).drop (tl A prm0 τ t).sendG).foldl (· * ·) 1 = _
    rw [foldl_mul_prod, e1, (hside t ht).2]
  · show ((finsOf A prm0 τ t).take (tl A prm0 τ t).sendG).foldl (· * ·) 1 = _
    rw [foldl_mul_prod, e1, (hside t ht).1]

end

/-! ## `Msg4` -/

theorem elems_nil_E4 {A : Air} {prm : Params} {τ : PTn} (hs : Shaped (Vnp A prm) τ)
    (hE : τ.entries.length = 4) : τ.elems = [] := by
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, _, _⟩ := shaped_hdr hs hne
  obtain ⟨s0, h01, h02⟩ := shaped_fits hs hl 0 (by omega)
  rw [(sched_get l).1] at h01; cases h01
  obtain ⟨a, b, he0, ha, hb⟩ := fits_two h02
  obtain ⟨o, rfl⟩ := fits_oracle hb
  obtain ⟨l', rfl⟩ := fits_header ha
  obtain ⟨s2, h21, h22⟩ := shaped_fits hs hl 2 (by omega)
  rw [(sched_get l).2.1] at h21; cases h21
  have he2 := fits_nil h22
  obtain ⟨s1, h11, h12⟩ := shaped_fits hs hl 1 (by omega)
  obtain ⟨s3, h31, h32⟩ := shaped_fits hs hl 3 (by omega)
  have hs1 : s1 = .chal false := by
    have : (schedule A prm l)[1]? = some (.chal false) := rfl
    rw [this] at h11; cases h11; rfl
  have hs3 : s3 = .chal false := by
    have : (schedule A prm l)[3]? = some (.chal false) := rfl
    rw [this] at h31; cases h31; rfl
  subst hs1; subst hs3
  obtain ⟨c1, he1⟩ := fits_chal h12
  obtain ⟨c3, he3⟩ := fits_chal h32
  match hes : τ.entries, hE with
  | [e0, e1, e2, e3], _ =>
    have : τ = ⟨τ.cb, [e0, e1, e2, e3]⟩ := by rw [← hes]
    simp only [hes, List.getElem_cons_zero, List.getElem_cons_succ] at he0 he1 he2 he3
    subst he0; subst he1; subst he2; subst he3
    rw [this]; simp [PT.elems]

theorem msg4 : Msg4Stmt := by
  intro A prm hok τ m hs _ hE hst
  obtain ⟨hprm, _, _⟩ := hok
  subst hprm
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix A _ τ).1 m hs
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hsτ hne
  obtain ⟨l2, hl2, _, s4, h41, h42⟩ := push_fits hs hne
  rw [hl] at hl2; cases hl2
  rw [hE, (sched_get l).2.2.1] at h41; cases h41
  obtain ⟨a4, b4, hm, ha4, hb4⟩ := fits_two h42
  cases hm
  obtain ⟨o, rfl⟩ := fits_oracle ha4
  obtain ⟨xs, rfl, hxs⟩ := fits_elems hb4
  have hel := elems_nil_E4 hsτ hE
  have hl' : (τ.push [PartV.oracle o, .elems xs]).header? = some l := by rw [header?_push _ _ hne]; exact hl
  have hfin : finalsOf (τ.push [PartV.oracle o, .elems xs]) = xs := by
    unfold finalsOf
    have : (τ.push [PartV.oracle o, .elems xs]).elems = τ.elems ++ [xs] := by
      simp [PT.push, PT.elems, List.flatMap_append]
    rw [this, hel]; rfl
  have hfl : (finalsOf (τ.push [PartV.oracle o, .elems xs])).length =
      ((layOf A Params.default (τ.push [PartV.oracle o, .elems xs])).map fun L => L.sendG + L.recvG).sum := by
    rw [hfin, hxs]; unfold layOf hdrOf; rw [hl']; rfl
  have ho1 := shaped_oracles1 hsτ (by omega)
  have hO : OAgree 1 (τ.push [PartV.oracle o, .elems xs]) τ := (oAgree_push τ _ hne).mono ho1
  have hE' : (τ.push [PartV.oracle o, .elems xs]).entries.length = 5 := by rw [len_push, hE]
  simp only [Stage, hE] at hst
  simp only [Stage, hE', chals_push]
  refine Classical.byContradiction fun hno => ?_
  simp only [_root_.not_or, Classical.not_not] at hno
  obtain ⟨hC2, hCs, hBF⟩ := hno
  have hz : ∀ t, t < A.tables.length → ∀ r, r < 2 ^ (tl A Params.default (τ.push [PartV.oracle o, .elems xs]) t).log →
      ∀ c ∈ csAt A Params.default (τ.push [PartV.oracle o, .elems xs]) t (τ.chals.getD 0 0) (τ.chals.getD 1 0)
        (omg (tl A Params.default (τ.push [PartV.oracle o, .elems xs]) t).log ^ r), c = 0 :=
    fun t ht r hr c hc => Classical.byContradiction fun h0 => hCs ⟨t, ht, r, hr, c, hc, h0⟩
  rcases hst with h | h | h
  · exact h ((allClose_congr hO (Nat.le_refl 1)).mp (allClose_mono (by omega) hC2))
  · exact no_localFail hl' hh _ _ hz ((localFail_congr hO (Nat.le_refl 1)).mpr h)
  · exact no_gpDiffer hl' hh hfl _ _ hz hBF ((gpDiffer_congr hO (Nat.le_refl 1) _ _).mpr h)

end ZkFormal.Udr.Np
