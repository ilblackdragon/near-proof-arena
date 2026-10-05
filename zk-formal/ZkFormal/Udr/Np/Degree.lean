import ZkFormal.Udr.Np.BusRounds

/-!
# ZkFormal.Udr.Np.Degree — polynomial degrees of the semantic constraint values

`Dg T d φ` : `φ` is a polynomial function of length `d·T + 1` (degree `≤ d·T`).
`Rep P L` : the family of lists `L x` is the pointwise evaluation of a fixed
list of functions, each satisfying `P`.  Every list operation used by
`auxConstraints` (take, drop, zip, map, filter on `x`-independent data,
flatMap, append, cons) preserves `Rep`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Degrees -/

def Dg (T d : Nat) (φ : Fp8 → Fp8) : Prop := IsPoly (d * T + 1) φ

section
variable {T : Nat}

theorem Dg.mono {d d' : Nat} (h : d ≤ d') {φ : Fp8 → Fp8} (hφ : Dg T d φ) : Dg T d' φ := by
  unfold Dg at *
  have := Nat.mul_le_mul_right T h
  exact IsPoly.mono (by omega) hφ

theorem Dg.const (d : Nat) (a : Fp8) : Dg T d (fun _ => a) := by
  unfold Dg; exact (IsPoly.const a).mono (by omega)

theorem Dg.add {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : Dg T a φ) (h2 : Dg T b ψ) :
    Dg T (max a b) (fun x => φ x + ψ x) := by
  have h1' := h1.mono (Nat.le_max_left a b); have h2' := h2.mono (Nat.le_max_right a b)
  unfold Dg at *; exact h1'.add h2'

theorem Dg.sub {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : Dg T a φ) (h2 : Dg T b ψ) :
    Dg T (max a b) (fun x => φ x - ψ x) := by
  have h1' := h1.mono (Nat.le_max_left a b); have h2' := h2.mono (Nat.le_max_right a b)
  unfold Dg at *; exact h1'.sub h2'

theorem Dg.neg {a : Nat} {φ : Fp8 → Fp8} (h1 : Dg T a φ) : Dg T a (fun x => - φ x) := by
  unfold Dg at *; exact h1.neg

theorem Dg.mul {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : Dg T a φ) (h2 : Dg T b ψ) :
    Dg T (a + b) (fun x => φ x * ψ x) := by
  have := IsPoly.mul h1 h2
  unfold Dg; rw [Nat.add_mul]; exact this

theorem Dg.smul {a : Nat} (c : Fp8) {φ : Fp8 → Fp8} (h1 : Dg T a φ) : Dg T a (fun x => c * φ x) := by
  unfold Dg at *; exact h1.smul c

theorem ev_scale (c : Fp8) : ∀ (m : Nat) (P : Nat → Fp8) (x : Fp8),
    ev m P (c * x) = ev m (fun k => P k * c ^ k) x
  | 0, _, _ => rfl
  | m + 1, Q, x => by
    rw [ev_succ, ev_succ, ev_scale c m (fun k => Q (k + 1)) x]
    have h1 : (fun k => Q (k + 1) * c ^ (k + 1)) = (fun k => c * (Q (k + 1) * c ^ k)) := by
      funext k; rw [Semiring.pow_succ]; generalize c ^ k = u; grind
    rw [h1, ev_smul, Semiring.pow_zero]
    generalize ev m (fun k => Q (k + 1) * c ^ k) x = E
    grind

theorem IsPoly.scale {m : Nat} (c : Fp8) {φ : Fp8 → Fp8} (h : IsPoly m φ) : IsPoly m (fun x => φ (c * x)) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨fun k => Q k * c ^ k, fun x => by dsimp only; rw [hQ, ev_scale]⟩

theorem Dg.scale {a : Nat} (c : Fp8) {φ : Fp8 → Fp8} (h1 : Dg T a φ) : Dg T a (fun x => φ (c * x)) := by
  unfold Dg at *; exact IsPoly.scale c h1

theorem isPoly_pow : ∀ n : Nat, IsPoly (K := Fp8) (n + 1) (fun x => x ^ n)
  | 0 => ⟨fun _ => 1, fun x => by simp only [ev_succ, ev_zero, Semiring.pow_zero]; grind⟩
  | n + 1 => by
    obtain ⟨c, hc⟩ := (isPoly_pow n).mulX
    exact ⟨c, fun x => by have := hc x; dsimp only at this ⊢; rw [← this, Semiring.pow_succ]; grind⟩

theorem Dg.powT : Dg T 1 (fun x => x ^ T) := by
  unfold Dg; rw [Nat.one_mul]; exact isPoly_pow T

theorem Dg.ev (P : Nat → Fp8) : Dg T 1 (fun x => ev (T + 1) P x) := by
  unfold Dg; rw [Nat.one_mul]; exact IsPoly.of_ev _ _

theorem Dg.selSum : Dg T 1 (fun x => selSum T x) := by
  unfold ZkFormal.Udr.Np.selSum
  refine Dg.smul _ ?_
  exact (IsPoly.of_ev T (fun _ => (1 : Fp8))).mono (by omega)

/-! ## Representable families of lists -/

variable {β γ : Type}

/-- `L x` is the evaluation at `x` of a fixed list of functions, each satisfying `P`. -/
def Rep (P : (Fp8 → β) → Prop) (L : Fp8 → List β) : Prop :=
  ∃ FL : List (Fp8 → β), (∀ x, L x = FL.map (fun f => f x)) ∧ ∀ f ∈ FL, P f

theorem Rep.mono {P Q : (Fp8 → β) → Prop} (hPQ : ∀ f, P f → Q f) {L : Fp8 → List β} (h : Rep P L) :
    Rep Q L := by
  obtain ⟨FL, h1, h2⟩ := h; exact ⟨FL, h1, fun f hf => hPQ f (h2 f hf)⟩

theorem Rep.ofMap {σ : Type} (P : (Fp8 → β) → Prop) (l : List σ) (g : σ → Fp8 → β)
    (hg : ∀ s ∈ l, P (g s)) : Rep P (fun x => l.map fun s => g s x) :=
  ⟨l.map g, fun x => by rw [List.map_map]; rfl, fun f hf => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf; exact hg s hs⟩

theorem Rep.nil (P : (Fp8 → β) → Prop) : Rep P (fun _ => []) := ⟨[], fun _ => rfl, by simp⟩

theorem Rep.const (l : List β) : Rep (fun f => ∃ b, f = fun _ => b) (fun _ => l) :=
  ⟨l.map fun b _ => b, fun x => by rw [List.map_map]; exact (List.map_id' l).symm, fun f hf => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hf; exact ⟨b, rfl⟩⟩

theorem Rep.take {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) (k : Nat) :
    Rep P (fun x => (L x).take k) := by
  obtain ⟨FL, h1, h2⟩ := h
  exact ⟨FL.take k, fun x => by dsimp only; rw [h1, List.map_take], fun f hf => h2 f (List.mem_of_mem_take hf)⟩

theorem Rep.drop {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) (k : Nat) :
    Rep P (fun x => (L x).drop k) := by
  obtain ⟨FL, h1, h2⟩ := h
  exact ⟨FL.drop k, fun x => by dsimp only; rw [h1, List.map_drop], fun f hf => h2 f (List.mem_of_mem_drop hf)⟩

theorem Rep.append {P : (Fp8 → β) → Prop} {L M : Fp8 → List β} (h : Rep P L) (h' : Rep P M) :
    Rep P (fun x => L x ++ M x) := by
  obtain ⟨FL, h1, h2⟩ := h; obtain ⟨FM, h1', h2'⟩ := h'
  refine ⟨FL ++ FM, fun x => by dsimp only; rw [h1, h1', List.map_append], fun f hf => ?_⟩
  rcases List.mem_append.mp hf with h | h
  · exact h2 f h
  · exact h2' f h

theorem Rep.cons {P : (Fp8 → β) → Prop} {a : Fp8 → β} {L : Fp8 → List β} (ha : P a) (h : Rep P L) :
    Rep P (fun x => a x :: L x) := by
  obtain ⟨FL, h1, h2⟩ := h
  refine ⟨a :: FL, fun x => by dsimp only; rw [h1]; rfl, fun f hf => ?_⟩
  rcases List.mem_cons.mp hf with rfl | h
  · exact ha
  · exact h2 f h

theorem Rep.map {P : (Fp8 → β) → Prop} {Q : (Fp8 → γ) → Prop} {L : Fp8 → List β} (h : Rep P L)
    (g : β → γ) (hg : ∀ f, P f → Q (fun x => g (f x))) : Rep Q (fun x => (L x).map g) := by
  obtain ⟨FL, h1, h2⟩ := h
  refine ⟨FL.map fun f x => g (f x), fun x => by dsimp only; rw [h1, List.map_map, List.map_map]; rfl,
    fun f hf => ?_⟩
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
  exact hg f' (h2 f' hf')

theorem Rep.zip {P : (Fp8 → β) → Prop} {Q : (Fp8 → γ) → Prop} {L : Fp8 → List β} {M : Fp8 → List γ}
    (h : Rep P L) (h' : Rep Q M) :
    Rep (fun f => P (fun x => (f x).1) ∧ Q (fun x => (f x).2)) (fun x => (L x).zip (M x)) := by
  obtain ⟨FL, h1, h2⟩ := h; obtain ⟨FM, h1', h2'⟩ := h'
  refine ⟨(FL.zip FM).map fun p x => (p.1 x, p.2 x), fun x => ?_, fun f hf => ?_⟩
  · dsimp only; rw [h1, h1', List.zip_map, List.map_map]; rfl
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hf
    exact ⟨h2 a (List.of_mem_zip hab).1, h2' b (List.of_mem_zip hab).2⟩

theorem Rep.filter {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) (p : β → Bool)
    (hp : ∀ f, P f → ∀ x y, p (f x) = p (f y)) : Rep P (fun x => (L x).filter p) := by
  obtain ⟨FL, h1, h2⟩ := h
  refine ⟨FL.filter fun f => p (f 0), fun x => ?_, fun f hf => h2 f (List.mem_filter.mp hf).1⟩
  dsimp only; rw [h1, List.filter_map]
  congr 1
  apply List.filter_congr
  intro f hf
  exact hp f (h2 f hf) x 0

theorem Rep.flatMap {P : (Fp8 → β) → Prop} {Q : (Fp8 → γ) → Prop} {L : Fp8 → List β} (h : Rep P L)
    (g : β → List γ) (hg : ∀ f, P f → Rep Q (fun x => g (f x))) :
    Rep Q (fun x => (L x).flatMap g) := by
  obtain ⟨FL, h1, h2⟩ := h
  have : ∀ FL : List (Fp8 → β), (∀ f ∈ FL, P f) →
      Rep Q (fun x => (FL.map fun f => f x).flatMap g) := by
    intro FL hFL
    induction FL with
    | nil => exact Rep.nil Q
    | cons f FL ih =>
      have := (hg f (hFL f (List.mem_cons_self ..))).append (ih fun f' hf' => hFL f' (List.mem_cons_of_mem _ hf'))
      simpa only [List.map_cons, List.flatMap_cons] using this
  obtain ⟨FR, hR1, hR2⟩ := this FL h2
  exact ⟨FR, fun x => by dsimp only; rw [h1]; exact hR1 x, hR2⟩

theorem Rep.getLastD {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) (d : β)
    (hd : P (fun _ => d)) : P (fun x => (L x).getLastD d) := by
  obtain ⟨FL, h1, h2⟩ := h
  simp only [h1]
  cases hF : FL.reverse with
  | nil =>
    have : FL = [] := List.reverse_eq_nil_iff.mp hF
    subst this; exact hd
  | cons f R =>
    have hFL : FL = R.reverse ++ [f] := by rw [← List.reverse_reverse FL, hF]; simp
    have hf : f ∈ FL := by rw [hFL]; simp
    have e : ∀ x, ((FL.map fun f => f x)).getLastD d = f x := fun x => by
      rw [hFL, List.map_append]; simp [List.getLastD_eq_getLast?]
    simp only [e]; exact h2 f hf

theorem Rep.length {P : (Fp8 → β) → Prop} {L : Fp8 → List β} (h : Rep P L) :
    ∃ n, ∀ x, (L x).length = n := by
  obtain ⟨FL, h1, _⟩ := h; exact ⟨FL.length, fun x => by rw [h1, List.length_map]⟩

/-- `combine` of a representable family of degree-`d` values. -/
theorem Rep.combine {d : Nat} {L : Fp8 → List Fp8} (h : Rep (Dg T d) L) (α : Fp8) :
    Dg T d (fun x => combine α (L x)) := by
  obtain ⟨FL, h1, h2⟩ := h
  simp only [h1]
  clear h1
  induction FL with
  | nil => exact Dg.const d 0
  | cons f FL ih =>
    have := (h2 f (List.mem_cons_self ..)).add ((ih fun f' hf' => h2 f' (List.mem_cons_of_mem _ hf')).smul α)
    rw [Nat.max_self] at this
    exact this

end

end ZkFormal.Udr.Np

/-! ## The aux constraints have bounded degree -/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable {T : Nat}

/-- `interactionAux` on a representable family of aux values. -/
theorem ia_rep (env : Fp8 → Env Fp8) (α γ : Fp8) (i : Interaction) (aux : Fp8 → List Fp8)
    (haux : Rep (Dg T 1) aux) (hfp : i.mult ≠ [] → Dg T 15 (fun x => fingerprint (env x) α i))
    (hbits : ∀ b ∈ i.mult, Dg T 15 (fun x => b.evalWith (env x))) :
    Rep (Dg T 64) (fun x => (interactionAux (env x) α γ i (aux x)).1) ∧
    Dg T 32 (fun x => (interactionAux (env x) α γ i (aux x)).2.1) ∧
    Rep (Dg T 1) (fun x => (interactionAux (env x) α γ i (aux x)).2.2) := by
  rcases h : i.mult with _ | ⟨b0, _ | ⟨b1, bs⟩⟩
  · simp only [interactionAux, h, List.map_nil]
    exact ⟨Rep.nil _, Dg.const _ _, haux⟩
  · simp only [interactionAux, h, List.map_cons, List.map_nil]
    have hp0 : Dg T 15 (fun x => γ - fingerprint (env x) α i) :=
      ((Dg.const 15 γ).sub (hfp (by rw [h]; simp))).mono (by omega)
    have hb := hbits b0 (by rw [h]; simp)
    refine ⟨Rep.nil _, ?_, haux⟩
    exact ((Dg.const 0 1).add (hb.mul (hp0.sub (Dg.const 0 1)))).mono (by omega)
  · simp only [interactionAux, h, List.map_cons, List.length_cons, List.length_map]
    have hp0 : Dg T 15 (fun x => γ - fingerprint (env x) α i) :=
      ((Dg.const 15 γ).sub (hfp (by rw [h]; simp))).mono (by omega)
    have hb0 := hbits b0 (by rw [h]; simp)
    have hps : Rep (Dg T 1) (fun x => (aux x).take (bs.length + 1)) := haux.take _
    have hpis : Rep (Dg T 1) (fun x => ((aux x).drop (bs.length + 1)).take (bs.length + 1)) :=
      (haux.drop _).take _
    have hbitsT : Rep (Dg T 15) (fun x => (b1.evalWith (env x)) ::
        bs.map fun b => b.evalWith (env x)) :=
      Rep.cons (hbits b1 (by rw [h]; simp))
        (Rep.ofMap _ bs (fun b x => b.evalWith (env x)) fun b hb => hbits b (by rw [h]; simp [hb]))
    have hfac : Rep (Dg T 16) (fun x => (((b1.evalWith (env x)) ::
        bs.map fun b => b.evalWith (env x)).zip ((aux x).take (bs.length + 1))).map
          fun p => 1 + p.1 * (p.2 - 1)) :=
      (hbitsT.zip hps).map _ fun f hf =>
        ((Dg.const 0 1).add (hf.1.mul (hf.2.sub (Dg.const 0 1)))).mono (by omega)
    have hprevP : Rep (Dg T 15) (fun x => (γ - fingerprint (env x) α i) ::
        (aux x).take (bs.length + 1)) :=
      Rep.cons hp0 (hps.mono fun f hf => hf.mono (by omega))
    have hprevPi : Rep (Dg T 30) (fun x => (1 + b0.evalWith (env x) * (γ - fingerprint (env x) α i - 1)) ::
        ((aux x).drop (bs.length + 1)).take (bs.length + 1)) :=
      Rep.cons (((Dg.const 0 1).add (hb0.mul (hp0.sub (Dg.const 0 1)))).mono (by omega))
        (hpis.mono fun f hf => hf.mono (by omega))
    refine ⟨Rep.append ((hps.zip hprevP).map _ fun f hf => (hf.1.sub (hf.2.mul hf.2)).mono (by omega))
      (((hpis.zip hprevPi).zip hfac).map _ fun f hf =>
        (hf.1.1.sub (hf.1.2.mul hf.2)).mono (by omega)), ?_, haux.drop _⟩
    exact ((hpis.getLastD 1 (Dg.const 1 1))).mono (by omega)

/-- Pairs `(interaction, φ)` with a fixed interaction and a degree-32 `φ`. -/
def PairP (T : Nat) (f : Fp8 → Interaction × Fp8) : Prop :=
  (∃ i, ∀ x, (f x).1 = i) ∧ Dg T 32 (fun x => (f x).2)

theorem fold_rep (env : Fp8 → Env Fp8) (α γ : Fp8) : ∀ (l : List Interaction)
    (Acc : Fp8 → List Fp8 × List (Interaction × Fp8) × List Fp8),
    (∀ i ∈ l, i.mult ≠ [] → Dg T 15 (fun x => fingerprint (env x) α i)) →
    (∀ i ∈ l, ∀ b ∈ i.mult, Dg T 15 (fun x => b.evalWith (env x))) →
    Rep (Dg T 64) (fun x => (Acc x).1) → Rep (PairP T) (fun x => (Acc x).2.1) →
    Rep (Dg T 1) (fun x => (Acc x).2.2) →
    let R := fun x => l.foldl (fun (acc : List Fp8 × List (Interaction × Fp8) × List Fp8) (i : Interaction) =>
      let (cs, phi, rest) := interactionAux (env x) α γ i acc.2.2
      (acc.1 ++ cs, acc.2.1 ++ [(i, phi)], rest)) (Acc x)
    Rep (Dg T 64) (fun x => (R x).1) ∧ Rep (PairP T) (fun x => (R x).2.1) ∧
      Rep (Dg T 1) (fun x => (R x).2.2)
  | [], Acc, _, _, h1, h2, h3 => ⟨h1, h2, h3⟩
  | i :: l, Acc, hf, hb, h1, h2, h3 => by
    intro R
    have hia := ia_rep env α γ i (fun x => (Acc x).2.2) h3 (hf i (List.mem_cons_self ..))
      (hb i (List.mem_cons_self ..))
    have := fold_rep env α γ l
      (fun x => ((Acc x).1 ++ (interactionAux (env x) α γ i (Acc x).2.2).1,
        (Acc x).2.1 ++ [(i, (interactionAux (env x) α γ i (Acc x).2.2).2.1)],
        (interactionAux (env x) α γ i (Acc x).2.2).2.2))
      (fun j hj => hf j (List.mem_cons_of_mem _ hj)) (fun j hj => hb j (List.mem_cons_of_mem _ hj))
      (h1.append hia.1) (h2.append (Rep.cons ⟨⟨i, fun _ => rfl⟩, hia.2.1⟩ (Rep.nil _))) hia.2.2
    exact this

end

section
variable {T : Nat}

theorem Rep.flatMapX {β γ : Type} {P : (Fp8 → β) → Prop} {Q : (Fp8 → γ) → Prop} {L : Fp8 → List β}
    (h : Rep P L) (g : Fp8 → β → List γ) (hg : ∀ f, P f → Rep Q (fun x => g x (f x))) :
    Rep Q (fun x => (L x).flatMap (g x)) := by
  obtain ⟨FL, h1, h2⟩ := h
  have : ∀ FL : List (Fp8 → β), (∀ f ∈ FL, P f) →
      Rep Q (fun x => (FL.map fun f => f x).flatMap (g x)) := by
    intro FL hFL
    induction FL with
    | nil => exact Rep.nil Q
    | cons f FL ih =>
      have := (hg f (hFL f (List.mem_cons_self ..))).append (ih fun f' hf' => hFL f' (List.mem_cons_of_mem _ hf'))
      simpa only [List.map_cons, List.flatMap_cons] using this
  obtain ⟨FR, hR1, hR2⟩ := this FL h2
  exact ⟨FR, fun x => by dsimp only; rw [h1]; exact hR1 x, hR2⟩

theorem chunksOf_one {α : Type} (l : List α) : chunksOf 1 l = l.map fun a => [a] := by
  unfold chunksOf
  suffices ∀ n (l : List α), l.length = n → chunksOf.go 1 n l = l.map fun a => [a] from this _ l rfl
  intro n
  induction n with
  | zero => intro l hl; rw [List.length_eq_zero_iff.mp hl]; rfl
  | succ n ih =>
    intro l hl
    match l, hl with
    | a :: l, hl =>
      simp only [chunksOf.go, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        List.map_cons]
      rw [ih l (by simp at hl; omega)]

/-- The group part of `auxConstraints` (group size 1) on representable families. -/
theorem gc_rep (env : Fp8 → Env Fp8)
    (hF1 : Dg T 1 (fun x => (env x).isFirst)) (hF2 : Dg T 1 (fun x => (env x).isTransition))
    (hF3 : Dg T 1 (fun x => (env x).isLast))
    (F : Fp8 → List Fp8 × List (Interaction × Fp8) × List Fp8) (auxZ auxG : Fp8 → List Fp8)
    (fins : List Fp8) (hR2 : Rep (PairP T) (fun x => (F x).2.1)) (hR3 : Rep (Dg T 1) (fun x => (F x).2.2))
    (hZ : Rep (Dg T 1) auxZ) (hG : Rep (Dg T 1) auxG) :
    Rep (Dg T 64) (fun x => List.flatMap
        (fun y =>
          [(env x).isFirst * (y.1.2.fst - 1),
            (env x).isTransition *
              (y.1.2.snd - y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst)),
            (env x).isLast *
              (y.1.2.fst * List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) y.1.fst) - y.snd)])
        (((chunksOf (max 1 1) (List.filter (fun x => x.fst.send) (F x).2.1) ++
                  chunksOf (max 1 1) (List.filter (fun x => !x.fst.send) (F x).2.1)).zip
              ((F x).2.2.zip (List.drop ((auxZ x).length - (F x).2.2.length) (auxG x)))).zip fins)) := by
  obtain ⟨n1, hn1⟩ := hZ.length
  obtain ⟨n2, hn2⟩ := hR3.length
  simp only [hn1, hn2, Nat.max_self, chunksOf_one]
  have hp : ∀ (p : Interaction × Fp8 → Bool), (∀ a b, a.1 = b.1 → p a = p b) →
      ∀ f, PairP T f → ∀ x y, p (f x) = p (f y) := fun p hp f hf x y => by
    obtain ⟨⟨i, hi⟩, _⟩ := hf
    exact hp _ _ (by rw [hi, hi])
  let GP : (Fp8 → List (Interaction × Fp8)) → Prop := fun g =>
    Dg T 32 (fun x => List.foldl (fun x1 x2 => x1 * x2) 1 (List.map (fun x => x.snd) (g x)))
  have hsingle : ∀ f, PairP T f → GP (fun x => [f x]) := fun f hf => by
    show Dg T 32 (fun x => List.foldl (fun x1 x2 => x1 * x2) 1 [(f x).2])
    simp only [List.foldl_cons, List.foldl_nil]
    exact ((Dg.const 0 1).mul hf.2).mono (by omega)
  have hgroups : Rep GP (fun x => List.map (fun a => [a]) (List.filter (fun x => x.fst.send) (F x).2.1) ++
      List.map (fun a => [a]) (List.filter (fun x => !x.fst.send) (F x).2.1)) :=
    ((hR2.filter _ (hp _ fun a b h => by rw [h])).map _ hsingle).append
      ((hR2.filter _ (hp _ fun a b h => by rw [h])).map _ hsingle)
  have hall := (hgroups.zip (hR3.zip (hG.drop (n1 - n2)))).zip (Rep.const fins)
  refine hall.flatMapX _ fun f hf => ?_
  obtain ⟨⟨hg, ha, han⟩, ⟨c, hc⟩⟩ := hf
  have hfin : (fun x => (f x).2) = fun _ => c := hc
  refine Rep.cons ((hF1.mul (ha.sub (Dg.const 0 1))).mono (by omega)) (Rep.cons ?_ (Rep.cons ?_ (Rep.nil _)))
  · exact (hF2.mul (han.sub (ha.mul hg))).mono (by omega)
  · have : Dg T 0 (fun x => (f x).2) := by rw [hfin]; exact Dg.const 0 c
    exact (hF3.mul ((ha.mul hg).sub this)).mono (by omega)

end

section
variable {T : Nat}

theorem auxC_rep (Tb : Air.Table) (env : Fp8 → Env Fp8) (α γ : Fp8)
    (hfp : ∀ i ∈ Tb.interactions, i.mult ≠ [] → Dg T 15 (fun x => fingerprint (env x) α i))
    (hbits : ∀ i ∈ Tb.interactions, ∀ b ∈ i.mult, Dg T 15 (fun x => b.evalWith (env x)))
    (hF1 : Dg T 1 (fun x => (env x).isFirst)) (hF2 : Dg T 1 (fun x => (env x).isTransition))
    (hF3 : Dg T 1 (fun x => (env x).isLast))
    (auxZ auxG : Fp8 → List Fp8) (fins : List Fp8) (hZ : Rep (Dg T 1) auxZ) (hG : Rep (Dg T 1) auxG) :
    Rep (Dg T 64) (fun x => auxConstraints Tb 1 (env x) α γ (auxZ x) (auxG x) fins) := by
  have hR := fold_rep env α γ Tb.interactions (fun x => ([], [], auxZ x)) hfp hbits (Rep.nil _)
    (Rep.nil _) hZ
  simp only at hR
  simp only [auxConstraints]
  exact hR.1.append (gc_rep env hF1 hF2 hF3 _ auxZ auxG fins hR.2.1 hR.2.2 hZ hG)

end

end ZkFormal.Udr.Np
