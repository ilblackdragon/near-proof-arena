import ZkFormal.V2.G.Groups

/-!
# ZkFormal.V2.G.Deg — constraint degrees and counts with groups of `g ≤ 3` interactions

Generalises v1's `Degree.gc_rep`/`auxC_rep`, `Chal7.table_deg`/`csAt_rep` and
`Ali.csAt_length` from `auxGroup = 1` to `1 ≤ g ≤ 3`.

* Degrees (`Dg T d`: degree `≤ d·T`).  v1 bounds every factor `φ_i` by `32·T` and every
  constraint by `64·T`.  A group product of `≤ g ≤ 3` factors has degree `≤ 96·T`, so the
  group constraints have degree `≤ 98·T`, and all constraint values are bounded by `128·T`
  (`auxC_rep`, `csAt_rep`).  The `Chal7` root count becomes `≤ 128·2^22 = 2^29`, still far
  below the `2^36` budget (with the `≤ 2^31` base-field points).
* `table_deg`: from `Table.degree t g ≤ 16` (part of `headerOk`), every interaction's
  message and bits have degree `≤ 15`, as for `g = 1`: an interaction with one bit lies in
  some group, whose degree `2 + Σ phiDegree` bounds its `phiDegree`.
* `csAt_length`: there are `numGroups n g ≤ n` running products per side.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

/-! ## `chunksOf` on representable families -/

section
variable {β : Type}

theorem chunksOf_go_sub (g : Nat) : ∀ (n : Nat) (l : List β), ∀ c ∈ chunksOf.go g n l, ∀ a ∈ c, a ∈ l
  | 0, _, c, h, _, _ => by simp [chunksOf.go] at h
  | _ + 1, [], c, h, _, _ => by simp [chunksOf.go] at h
  | n + 1, b :: l, c, h, a, ha => by
    simp only [chunksOf.go, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_of_mem_take ha
    · exact List.mem_of_mem_drop (chunksOf_go_sub g n _ c h a ha)

/-- Each group of a representable family is a list of at most `g` members. -/
def ChunkP (g : Nat) (P : (Fp8 → β) → Prop) (G : Fp8 → List β) : Prop :=
  ∃ c : List (Fp8 → β), c.length ≤ g ∧ (∀ f ∈ c, P f) ∧ ∀ x, G x = c.map fun f => f x

theorem Rep.chunks {g : Nat} {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) :
    Rep (ChunkP g P) (fun x => chunksOf g (L x)) := by
  obtain ⟨FL, h1, h2⟩ := h
  refine ⟨(chunksOf g FL).map fun c x => c.map fun f => f x, fun x => ?_, fun G hG => ?_⟩
  · dsimp only; rw [h1, chunksOf_map, List.map_map]; rfl
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hG
    exact ⟨c, chunksOf_le g FL c hc, fun f hf => h2 f (chunksOf_go_sub g _ FL c hc f hf), fun _ => rfl⟩

end

/-! ## The group constraints -/

section
variable {T : Nat}

theorem foldl_prod_deg : ∀ (c : List (Fp8 → Interaction × Fp8)), (∀ f ∈ c, PairP T f) →
    Dg T (32 * c.length) (fun x => List.foldl (fun x1 x2 => x1 * x2) 1
      (List.map (fun x => x.snd) (c.map fun f => f x)))
  | [], _ => Dg.const _ 1
  | f :: c, hc => by
    have ih := foldl_prod_deg c (fun f' hf' => hc f' (List.mem_cons_of_mem _ hf'))
    have hf := (hc f (List.mem_cons_self ..)).2
    have e : ∀ x, List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) ((f :: c).map fun f => f x)) =
        (f x).2 * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) (c.map fun f => f x)) := by
      intro x
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_mul_prod, foldl_mul_prod]; grind
    simp only [e]
    exact (hf.mul ih).mono (by simp only [List.length_cons]; omega)

/-- The group part of `auxConstraints` (group size `g ≤ 3`) on representable families. -/
theorem gc_rep {g : Nat} (hg : 1 ≤ g) (hg3 : g ≤ 3) (env : Fp8 → Env Fp8)
    (hF1 : Dg T 1 (fun x => (env x).isFirst)) (hF2 : Dg T 1 (fun x => (env x).isTransition))
    (hF3 : Dg T 1 (fun x => (env x).isLast))
    (F : Fp8 → List Fp8 × List (Interaction × Fp8) × List Fp8) (auxZ auxG : Fp8 → List Fp8)
    (fins : List Fp8) (hR2 : Rep (PairP T) (fun x => (F x).2.1)) (hR3 : Rep (Dg T 1) (fun x => (F x).2.2))
    (hZ : Rep (Dg T 1) auxZ) (hG : Rep (Dg T 1) auxG) :
    Rep (Dg T 128) (fun x => List.flatMap
        (fun y =>
          [(env x).isFirst * (y.1.2.fst - 1),
            (env x).isTransition *
              (y.1.2.snd - y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst)),
            (env x).isLast *
              (y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst) - y.snd)])
        (((chunksOf (max g 1) (List.filter (fun x => x.fst.send) (F x).2.1) ++
                  chunksOf (max g 1) (List.filter (fun x => !x.fst.send) (F x).2.1)).zip
              ((F x).2.2.zip (List.drop ((auxZ x).length - (F x).2.2.length) (auxG x)))).zip fins)) := by
  obtain ⟨n1, hn1⟩ := hZ.length
  obtain ⟨n2, hn2⟩ := hR3.length
  simp only [hn1, hn2, Nat.max_eq_left hg]
  have hp : ∀ (p : Interaction × Fp8 → Bool), (∀ a b, a.1 = b.1 → p a = p b) →
      ∀ f, PairP T f → ∀ x y, p (f x) = p (f y) := fun p hp f hf x y => by
    obtain ⟨⟨i, hi⟩, _⟩ := hf
    exact hp _ _ (by rw [hi, hi])
  let GP : (Fp8 → List (Interaction × Fp8)) → Prop := fun g =>
    Dg T 96 (fun x => List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) (g x)))
  have hchunk : ∀ G, ChunkP g (PairP T) G → GP G := fun G hG => by
    obtain ⟨c, hcl, hcP, hcx⟩ := hG
    show Dg T 96 _
    simp only [hcx]
    exact (foldl_prod_deg c hcP).mono (by omega)
  have hgroups : Rep GP (fun x => chunksOf g (List.filter (fun x => x.fst.send) (F x).2.1) ++
      chunksOf g (List.filter (fun x => !x.fst.send) (F x).2.1)) :=
    ((Rep.chunks (hR2.filter (fun x => x.fst.send) (hp (fun x => x.fst.send) fun a b h => by rw [h]))).mono hchunk).append
      ((Rep.chunks (hR2.filter (fun x => !x.fst.send) (hp (fun x => !x.fst.send) fun a b h => by rw [h]))).mono hchunk)
  have hall := (hgroups.zip (hR3.zip (hG.drop (n1 - n2)))).zip (Rep.const fins)
  refine hall.flatMapX _ fun f hf => ?_
  obtain ⟨⟨hg, ha, han⟩, ⟨c, hc⟩⟩ := hf
  have hfin : (fun x => (f x).2) = fun _ => c := hc
  refine Rep.cons ((hF1.mul (ha.sub (Dg.const 0 1))).mono (by omega)) (Rep.cons ?_ (Rep.cons ?_ (Rep.nil _)))
  · exact (hF2.mul (han.sub (ha.mul hg))).mono (by omega)
  · have : Dg T 0 (fun x => (f x).2) := by rw [hfin]; exact Dg.const 0 c
    exact (hF3.mul ((ha.mul hg).sub this)).mono (by omega)

theorem auxC_rep {g : Nat} (hg : 1 ≤ g) (hg3 : g ≤ 3) (Tb : Air.Table) (env : Fp8 → Env Fp8) (α γ : Fp8)
    (hfp : ∀ i ∈ Tb.interactions, i.mult ≠ [] → Dg T 15 (fun x => fingerprint (env x) α i))
    (hbits : ∀ i ∈ Tb.interactions, ∀ b ∈ i.mult, Dg T 15 (fun x => b.evalWith (env x)))
    (hF1 : Dg T 1 (fun x => (env x).isFirst)) (hF2 : Dg T 1 (fun x => (env x).isTransition))
    (hF3 : Dg T 1 (fun x => (env x).isLast))
    (auxZ auxG : Fp8 → List Fp8) (fins : List Fp8) (hZ : Rep (Dg T 1) auxZ) (hG : Rep (Dg T 1) auxG) :
    Rep (Dg T 128) (fun x => auxConstraints Tb g (env x) α γ (auxZ x) (auxG x) fins) := by
  have hR := fold_rep env α γ Tb.interactions (fun x => ([], [], auxZ x)) hfp hbits (Rep.nil _)
    (Rep.nil _) hZ
  simp only at hR
  simp only [auxConstraints]
  exact (hR.1.mono fun f hf => hf.mono (by omega)).append
    (gc_rep hg hg3 env hF1 hF2 hF3 _ auxZ auxG fins hR.2.1 hR.2.2 hZ hG)

end

/-! ## Table degrees -/

theorem le_sum_of_mem' {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem table_deg {g : Nat} (hg : 1 ≤ g) (Tb : Air.Table) (h : Tb.degree g ≤ 16) :
    (∀ e ∈ Tb.allConstraints, e.degree ≤ 16) ∧
    ∀ i ∈ Tb.interactions, i.mult ≠ [] → (∀ e ∈ i.msg, e.degree ≤ 15) ∧ ∀ b ∈ i.mult, b.degree ≤ 15 := by
  simp only [Air.Table.degree, Air.Table.auxDegree, Nat.max_eq_left hg] at h
  have hA := Nat.le_trans (Nat.le_max_left _ _) h
  have hC := Nat.le_trans (Nat.le_max_right _ _) h
  refine ⟨fun e he => Nat.le_trans (le_foldr_max_init 2 (List.mem_map.mpr ⟨e, he, rfl⟩)) hC,
    fun i hi hne => ?_⟩
  have hy : ∀ y, y ∈ _ → y ≤ 16 := fun y hy => Nat.le_trans (le_foldr_max_init 2 hy) hA
  have hdm : ∀ e ∈ i.msg, e.degree ≤ (i.msg.map Expr.degree).foldr max 0 := fun e he =>
    le_foldr_max_init 0 (List.mem_map.mpr ⟨e, he, rfl⟩)
  rcases hm : i.mult with _ | ⟨b, _ | ⟨b1, bs⟩⟩
  · exact absurd hm hne
  · have hph : i.phiDegree = b.degree + (i.msg.map Expr.degree).foldr max 0 := by
      unfold Air.Interaction.phiDegree; rw [hm]
    have hgrp : ∀ s : Bool, i.send = s → ∃ grp ∈ chunksOf g (Tb.interactions.filter
        (fun (j : Interaction) => j.send == s)), i ∈ grp := fun s hs => by
      have : i ∈ (chunksOf g (Tb.interactions.filter (fun (j : Interaction) => j.send == s))).flatten := by
        rw [chunksOf_flatten hg]; exact List.mem_filter.mpr ⟨hi, by simp [hs]⟩
      exact List.mem_flatten.mp this
    obtain ⟨grp, hgm, hig⟩ := hgrp i.send rfl
    have hle : i.phiDegree ≤ (grp.map Interaction.phiDegree).sum :=
      le_sum_of_mem' (List.mem_map.mpr ⟨i, hig, rfl⟩)
    have hmem : 2 + (grp.map Interaction.phiDegree).sum ∈
        (List.map (fun grp => 2 + (List.map Interaction.phiDegree grp).sum)
            (chunksOf g (List.filter (fun i => i.send == true) Tb.interactions))) ++
        List.map (fun grp => 2 + (List.map Interaction.phiDegree grp).sum)
            (chunksOf g (List.filter (fun i => i.send == false) Tb.interactions)) := by
      cases hs : i.send
      · rw [hs] at hgm
        exact List.mem_append_right _ (List.mem_map.mpr ⟨grp, hgm, rfl⟩)
      · rw [hs] at hgm
        exact List.mem_append_left _ (List.mem_map.mpr ⟨grp, hgm, rfl⟩)
    have := hy _ (by rw [List.append_assoc]; exact List.mem_append_right _ hmem)
    rw [hph] at hle
    refine ⟨fun e he => by have := hdm e he; omega, fun b' hb' => ?_⟩
    simp only [List.mem_singleton] at hb'; subst hb'; omega
  · have hmem := (List.mem_map (f := fun i : Interaction =>
      match i.mult with
      | [] => 0
      | [_] => 0
      | b0 :: b1 :: bs =>
        max (2 * List.foldr max 0 (List.map Expr.degree i.msg))
          (max 2 (max (b0.degree + List.foldr max 0 (List.map Expr.degree i.msg) + b1.degree + 1)
            (List.foldr max 0 (List.map (fun b : Expr => b.degree + 2) bs)))))).mpr ⟨i, hi, rfl⟩
    have := hy _ (List.mem_append_left _ (List.mem_append_left _ hmem))
    simp only [hm] at this
    refine ⟨fun e he => by have := hdm e he; omega, fun b' hb' => ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · omega
    rcases List.mem_cons.mp hb' with rfl | hb'
    · omega
    have := le_foldr_max_init 0 ((List.mem_map (f := fun b : Expr => b.degree + 2)).mpr ⟨b', hb', rfl⟩)
    omega

theorem csAt_rep (A : Air) {g : Nat} (hg : 1 ≤ g) (hg3 : g ≤ 3) (τ : PTn) (t : Nat)
    (hdeg : (tableOf A t).degree g ≤ 16) (αfp γ : Fp8) :
    Rep (Dg (2 ^ (tl A (pg g) τ t).log) 128) (fun x => csAt A (pg g) τ t αfp γ x) := by
  obtain ⟨hC, hI⟩ := table_deg hg _ hdeg
  unfold csAt
  refine Rep.append (Rep.ofMap _ _ (fun e x => e.evalWith (polyEnv A (pg g) τ t x))
    fun e he => (evalWith_deg A (pg g) τ t e).mono (by have := hC e he; omega)) ?_
  exact auxC_rep hg hg3 (tableOf A t) (polyEnv A (pg g) τ t) αfp γ
    (fun i hi hne => fingerprint_deg _ _ i fun e he =>
      (evalWith_deg A (pg g) τ t e).mono ((hI i hi hne).1 e he))
    (fun i hi b hb => (evalWith_deg A (pg g) τ t b).mono
      ((hI i hi (List.ne_nil_of_mem hb)).2 b hb))
    Dg.selSum (((Dg.const 0 1).sub ((Dg.selSum).scale _)).mono (by simp)) ((Dg.selSum).scale _)
    _ _ _ (Rep.ofMap _ _ (fun a x => colAt A (pg g) τ ⟨t, 1, a⟩ x) fun a _ => Dg.ev _)
    (Rep.ofMap _ _ (fun a x => colAt A (pg g) τ ⟨t, 1, a⟩ (omg (tl A (pg g) τ t).log * x))
      fun a _ => (Dg.ev _).scale _)

/-! ## The number of constraint values -/

theorem csAt_length {A : Air} {prm : Params} (hok : NpOkG A prm) (τ : PTn) (t : Nat)
    (ht : t < A.tables.length) (αfp γ x : Fp8) :
    (csAt A prm τ t αfp γ x).length ≤ 2 ^ 20 := by
  obtain ⟨⟨g, rfl, hg, _⟩, hb, _⟩ := hok
  have hT : tableOf A t = A.tables[t] := by
    unfold tableOf; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  unfold csAt
  rw [List.length_append, List.length_map, hT]
  have h1 := auxConstraints_length A.tables[t] (pg g).auxGroup (polyEnv A (pg g) τ t x)
    αfp γ ((List.range (tl A (pg g) τ t).aux).map fun a =>
      colAt A (pg g) τ ⟨t, 1, a⟩ x)
    ((List.range (tl A (pg g) τ t).aux).map fun a =>
      colAt A (pg g) τ ⟨t, 1, a⟩ (omg (tl A (pg g) τ t).log * x))
    (finsOf A (pg g) τ t)
  have h2 : (finsOf A (pg g) τ t).length ≤ A.tables[t].interactions.length := by
    unfold finsOf
    rw [List.length_take]
    refine Nat.le_trans (Nat.min_le_left _ _) ?_
    unfold tl layOf
    by_cases hl : t < (layout A (pg g) (hdrOf τ)).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
      simp only [Option.getD_some, layout, List.getElem_map, List.getElem_zip]
      show numGroups _ g + numGroups _ g ≤ _
      have := numGroups_le hg (A.tables[t].numSide true)
      have := numGroups_le hg (A.tables[t].numSide false)
      have := length_filter_send A.tables[t].interactions
      unfold Air.Table.numSide at *
      omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]
      exact Nat.zero_le _
  have h3 := hb _ (List.getElem_mem ht)
  have h4 : (A.tables[t].interactions.map fun i => 2 * (i.mult.length - 1)).sum ≤
      A.tables[t].auxCount (pg g).auxGroup := by
    unfold Air.Table.auxCount; omega
  omega

end ZkFormal.V2.G
