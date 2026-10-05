import ZkFormal.Udr.Np.Hom

/-!
# ZkFormal.Udr.Np.AuxChain — what vanishing aux constraints say (one point)

At a single point, if all constraints of `interactionAux` vanish and the
multiplicity bits are boolean, the factor `φ_i` is `p0^{val bits}` with
`p0 = γ - fingerprint` (the power chain `P_j = P_{j-1}²` and the partial
products).  Through the fold of `auxConstraints`, the factors are
`is.map (fun i => (i, φ_i))` and the running-product columns start after
`Σ 2(|mult|-1)` chain columns.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- `Σ_m [b_m = 1]·2^m`. -/
def bval : List Fp8 → Nat
  | [] => 0
  | b :: bs => (if b = 1 then 1 else 0) + 2 * bval bs

theorem bool_fac {b p : Fp8} (hb : b = 0 ∨ b = 1) : 1 + b * (p - 1) = p ^ (if b = 1 then 1 else 0) := by
  rcases hb with rfl | rfl
  · rw [if_neg (by decide), Semiring.pow_zero]; grind
  · rw [if_pos rfl, Semiring.pow_one]; grind

theorem pow_two_mul' (p : Fp8) (n : Nat) : (p * p) ^ n = p ^ (2 * n) := by
  rw [pow_mul_eq, Semiring.pow_two]

theorem chain_core : ∀ (bs ps pis : List Fp8) (p0 q0 : Fp8),
    ps.length = bs.length → pis.length = bs.length → (∀ b ∈ bs, b = 0 ∨ b = 1) →
    (∀ c ∈ (ps.zip (p0 :: ps)).map (fun x => x.1 - x.2 * x.2), c = 0) →
    (∀ c ∈ ((pis.zip (q0 :: pis)).zip ((bs.zip ps).map (fun x => 1 + x.1 * (x.2 - 1)))).map
      (fun x => x.1.1 - x.1.2 * x.2), c = 0) →
    pis.getLastD q0 = q0 * p0 ^ (2 * bval bs)
  | [], _, [], _, q0, _, _, _, _, _ => by simp only [List.getLastD_nil, bval, Nat.mul_zero, Semiring.pow_zero]; grind
  | [], _, _ :: _, _, _, _, h, _, _, _ => by simp at h
  | b :: bs, p1 :: ps, π1 :: pis, p0, q0, h1, h2, hb, hc1, hc2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.mem_cons, forall_eq_or_imp] at hc1 hc2
    have e1 : p1 = p0 * p0 := by have := hc1.1; grind
    have e2 : π1 = q0 * (1 + b * (p1 - 1)) := by have := hc2.1; grind
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have ih := chain_core bs ps pis p1 π1 h1 h2 (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
      hc1.2 hc2.2
    rw [List.getLastD_cons, ih, e2, bool_fac (hb b (List.mem_cons_self ..)), e1, pow_two_mul',
      pow_two_mul', Semiring.mul_assoc, ← Semiring.pow_add]
    congr 2
    simp only [bval]; omega
  | b :: bs, [], _, _, _, h, _, _, _, _ => by simp at h
  | b :: bs, _ :: _, [], _, _, _, h, _, _, _ => by simp at h

theorem getLastD_ne_nil {l : List Fp8} (h : l ≠ []) (d d' : Fp8) : l.getLastD d = l.getLastD d' := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [List.getLastD_cons, List.getLastD_cons]

/-- Semantics of one interaction's chain. -/
theorem ia_sem (env : Env Fp8) (α γ : Fp8) (i : Interaction) (aux : List Fp8)
    (hlen : 2 * (i.mult.length - 1) ≤ aux.length)
    (hbits : ∀ b ∈ i.mult, b.evalWith env = 0 ∨ b.evalWith env = 1)
    (hz : ∀ c ∈ (interactionAux env α γ i aux).1, c = 0) :
    (interactionAux env α γ i aux).2.1 =
      (γ - fingerprint env α i) ^ bval (i.mult.map (·.evalWith env)) ∧
    (interactionAux env α γ i aux).2.2 = aux.drop (2 * (i.mult.length - 1)) := by
  rcases h : i.mult with _ | ⟨b0, _ | ⟨b1, bs⟩⟩
  · simp only [interactionAux, h, List.map_nil, bval, Semiring.pow_zero]
    simp
  · simp only [interactionAux, h, List.map_cons, List.map_nil]
    refine ⟨?_, rfl⟩
    rw [bool_fac (hbits b0 (by rw [h]; simp))]
    simp [bval]
  · simp only [interactionAux, h, List.map_cons, List.length_cons, List.length_map] at hz ⊢
    rw [h] at hlen; simp only [List.length_cons] at hlen
    refine ⟨?_, by congr 1⟩
    have hl1 : ((aux.drop (bs.length + 1)).take (bs.length + 1)).length = bs.length + 1 := by
      simp; omega
    have hl2 : (aux.take (bs.length + 1)).length = bs.length + 1 := by simp; omega
    have hne : (aux.drop (bs.length + 1)).take (bs.length + 1) ≠ [] := by
      intro h0; rw [h0] at hl1; simp at hl1
    rw [getLastD_ne_nil hne 1 (1 + b0.evalWith env * (γ - fingerprint env α i - 1))]
    rw [chain_core ((b1 :: bs).map (·.evalWith env)) (aux.take (bs.length + 1))
      ((aux.drop (bs.length + 1)).take (bs.length + 1)) (γ - fingerprint env α i)
      (1 + b0.evalWith env * (γ - fingerprint env α i - 1)) (by simp; omega) (by simp; omega)
      (fun b hb => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
        exact hbits e (by rw [h]; exact List.mem_cons_of_mem _ he))
      (fun c hc => hz c (List.mem_append_left _ hc)) (fun c hc => hz c (List.mem_append_right _ hc))]
    rw [bool_fac (hbits b0 (by rw [h]; simp)), ← Semiring.pow_add]
    simp only [List.map_cons, bval]

/-! ## The fold over interactions -/

/-- One step of the interaction fold (projection form). -/
def auxStep (env : Env Fp8) (α γ : Fp8) (acc : List Fp8 × List (Interaction × Fp8) × List Fp8)
    (i : Interaction) : List Fp8 × List (Interaction × Fp8) × List Fp8 :=
  (acc.1 ++ (interactionAux env α γ i acc.2.2).1, acc.2.1 ++ [(i, (interactionAux env α γ i acc.2.2).2.1)],
    (interactionAux env α γ i acc.2.2).2.2)

/-- Number of chain columns. -/
def nCons (is : List Interaction) : Nat := (is.map fun i => 2 * (i.mult.length - 1)).sum

/-- The factor `φ_i` forced by the chain. -/
def phiOf (env : Env Fp8) (α γ : Fp8) (i : Interaction) : Fp8 :=
  (γ - fingerprint env α i) ^ bval (i.mult.map (·.evalWith env))

theorem fold_prefix (env : Env Fp8) (α γ : Fp8) : ∀ (l : List Interaction) acc,
    ∃ X, (l.foldl (auxStep env α γ) acc).1 = acc.1 ++ X
  | [], acc => ⟨[], by simp⟩
  | i :: l, acc => by
    obtain ⟨X, hX⟩ := fold_prefix env α γ l (auxStep env α γ acc i)
    exact ⟨(interactionAux env α γ i acc.2.2).1 ++ X, by rw [List.foldl_cons, hX]; simp [auxStep]⟩

theorem fold_sem (env : Env Fp8) (α γ : Fp8) : ∀ (l : List Interaction) acc,
    (∀ i ∈ l, ∀ b ∈ i.mult, b.evalWith env = 0 ∨ b.evalWith env = 1) →
    nCons l ≤ acc.2.2.length →
    (∀ c ∈ (l.foldl (auxStep env α γ) acc).1, c = 0) →
    (l.foldl (auxStep env α γ) acc).2.1 = acc.2.1 ++ l.map (fun i => (i, phiOf env α γ i)) ∧
    (l.foldl (auxStep env α γ) acc).2.2 = acc.2.2.drop (nCons l)
  | [], acc, _, _, _ => by simp [nCons]
  | i :: l, acc, hb, hlen, hz => by
    rw [List.foldl_cons] at hz ⊢
    obtain ⟨X, hX⟩ := fold_prefix env α γ l (auxStep env α γ acc i)
    have hz1 : ∀ c ∈ (interactionAux env α γ i acc.2.2).1, c = 0 := fun c hc =>
      hz c (by rw [hX]; simp only [auxStep]; exact List.mem_append_left _ (List.mem_append_right _ hc))
    simp only [nCons, List.map_cons, List.sum_cons] at hlen
    have hia := ia_sem env α γ i acc.2.2 (by omega) (hb i (List.mem_cons_self ..)) hz1
    have ih := fold_sem env α γ l (auxStep env α γ acc i) (fun j hj => hb j (List.mem_cons_of_mem _ hj))
      (by simp only [auxStep]; rw [hia.2, List.length_drop]; unfold nCons; omega) hz
    rw [ih.1, ih.2]
    simp only [auxStep, hia.1, hia.2, List.drop_drop, phiOf]
    refine ⟨by simp, ?_⟩
    simp only [nCons, List.map_cons, List.sum_cons]

/-! ## The group constraints -/

theorem mem_flatMap3 {β : Type} {L : List β} {u v w : β → Fp8}
    (h : ∀ c ∈ L.flatMap (fun y => [u y, v y, w y]), c = 0) :
    ∀ y ∈ L, u y = 0 ∧ v y = 0 ∧ w y = 0 := fun y hy =>
  ⟨h _ (List.mem_flatMap.mpr ⟨y, hy, by simp⟩), h _ (List.mem_flatMap.mpr ⟨y, hy, by simp⟩),
    h _ (List.mem_flatMap.mpr ⟨y, hy, by simp⟩)⟩

/-- Interactions in group order: sends, then receives. -/
def ordOf (is : List Interaction) : List Interaction :=
  is.filter (fun i => i.send) ++ is.filter (fun i => !i.send)

theorem auxC_sem (Tb : Air.Table) (env : Env Fp8) (α γ : Fp8) (auxZ auxG fins : List Fp8)
    (hb : ∀ i ∈ Tb.interactions, ∀ b ∈ i.mult, b.evalWith env = 0 ∨ b.evalWith env = 1)
    (hlen : nCons Tb.interactions ≤ auxZ.length)
    (hz : ∀ c ∈ auxConstraints Tb 1 env α γ auxZ auxG fins, c = 0)
    (j : Nat) (hj : j < (ordOf Tb.interactions).length)
    (hjZ : nCons Tb.interactions + j < auxZ.length) (hjG : nCons Tb.interactions + j < auxG.length)
    (hjF : j < fins.length) :
    let a := auxZ.getD (nCons Tb.interactions + j) 0
    let an := auxG.getD (nCons Tb.interactions + j) 0
    let φ := phiOf env α γ ((ordOf Tb.interactions).getD j default)
    env.isFirst * (a - 1) = 0 ∧ env.isTransition * (an - a * φ) = 0 ∧
      env.isLast * (a * φ - fins.getD j 0) = 0 := by
  have e : auxConstraints Tb 1 env α γ auxZ auxG fins =
      (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).1 ++
      List.flatMap (fun y =>
          [env.isFirst * (y.1.2.fst - 1),
            env.isTransition *
              (y.1.2.snd - y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst)),
            env.isLast *
              (y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst) - y.snd)])
        ((((chunksOf 1 (List.filter (fun x => x.fst.send)
            (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.1) ++
          chunksOf 1 (List.filter (fun x => !x.fst.send)
            (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.1)).zip
          ((Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.2.zip
            (List.drop (auxZ.length - (Tb.interactions.foldl (auxStep env α γ) ([], [], auxZ)).2.2.length)
              auxG))).zip fins)) := by
    simp only [auxConstraints]; rfl
  rw [e] at hz
  have hF := fold_sem env α γ Tb.interactions ([], [], auxZ) hb hlen
    (fun c hc => hz c (List.mem_append_left _ hc))
  simp only [List.nil_append] at hF
  rw [hF.1, hF.2, chunksOf_one, chunksOf_one, List.filter_map, List.filter_map, List.length_drop,
    show auxZ.length - (auxZ.length - nCons Tb.interactions) = nCons Tb.interactions by omega] at hz
  have hz2 := mem_flatMap3 (fun c hc => hz c (List.mem_append_right _ hc))
  simp only [Function.comp_def] at hz2
  simp only [← List.map_append, List.map_map] at hz2
  have hfil1 : List.filter (fun x => x.send) Tb.interactions = Tb.interactions.filter (fun i => i.send) := rfl
  have hord : (List.filter (fun x => x.send) Tb.interactions ++ List.filter (fun x => !x.send) Tb.interactions) =
      ordOf Tb.interactions := rfl
  rw [hord] at hz2
  have hjL : j < (((List.map ((fun a => [a]) ∘ fun i => (i, phiOf env α γ i)) (ordOf Tb.interactions)).zip
      ((auxZ.drop (nCons Tb.interactions)).zip (auxG.drop (nCons Tb.interactions)))).zip fins).length := by
    simp only [List.length_zip, List.length_map, List.length_drop]; omega
  have := hz2 _ (List.getElem_mem hjL)
  simp only [List.getElem_zip, List.getElem_map, List.getElem_drop, Function.comp, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjZ, List.getElem?_eq_getElem hjG,
    List.getElem?_eq_getElem hjF, List.getElem?_eq_getElem hj, Option.getD_some]
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, ?_, ?_⟩
  · rw [← h2]; grind
  · rw [← h3]; grind

end ZkFormal.Udr.Np
