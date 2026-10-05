import ZkFormal.Stark.NpBounds
import ZkFormal.Prover.Statements

/-!
# ZkFormal.Prover.SizeBound — a header-free bound on `sizeBound` (lane L7-size)

`sizeBound_le`: for every AIR `A`, parameters `prm` and admissible header `hdr`,
`sizeBound (Iop.verifier F K A prm) hdr ≤ sizeMax A prm κ`, where `sizeMax` is a closed
formula in the AIR's static column counts and the parameters, and `κ` is any per-layer
constant with `32·2^a ≤ a·κ` for every admissible FRI arity log `1 ≤ a ≤ max maxArityLog 1`.

Accounting:
* prefix: header `8 + #tables`, three main roots, finals and OOD values (static counts),
  at most one FRI root per FRI layer (`ℓ ≤ maxLogLde`), and the final polynomial;
* openings of the main/aux/quotient oracles: static widths, tree depth `≤ maxLogLde`;
* FRI openings: the committed layers `c₀ = 0 < c₁ < … ≤ ℓ` (`cₖ₊₁ = cₖ + aₖ`) cost
  `nq·(32·2^aₖ + 64·(n0 - cₖ₊₁))`, which is at most the potential
  `Σ_{j ∈ (cₖ, cₖ₊₁]} (κ + 64·(n0 - j))` (`pot`); summed over all layers this is
  `pot κ n0 0 ℓ ≤ pot κ maxLogLde 0 (maxLogLde - logBlowup - finalLog)`.
-/

namespace ZkFormal.Prover

open ArenaCore Lean.Grind ZkFormal.Stark ZkFormal.Air

namespace SizeBound

/-! ## List arithmetic -/

theorem sum_map_le {α : Type} {f g : α → Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := sum_map_le (l := l) fun x hx => h x (by simp [hx])
    omega

theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add f g l]
    omega

theorem sum_map_mul {α : Type} (n : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map fun x => n * f x).sum = n * (l.map f).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_mul n f l, Nat.mul_add]

theorem sum_map_flatMap {α β : Type} (f : α → List β) (h : β → Nat) :
    ∀ l : List α, ((l.flatMap f).map h).sum = (l.map fun x => ((f x).map h).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap f h l]

theorem sum_map_const_le {α : Type} (f : α → Nat) (k : Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ k) → (l.map f).sum ≤ l.length * k
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := sum_map_const_le f k l fun x hx => h x (by simp [hx])
    omega

theorem sum_ite_zero (k G : Nat) :
    ∀ l : List Nat, k ∉ l → (l.map fun i => if i = k then G else 0).sum = 0
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.mem_cons, _root_.not_or] at h
    have hne : a ≠ k := fun e => h.1 e.symm
    simp only [List.map_cons, List.sum_cons, hne, ite_false, sum_ite_zero k G l h.2]

theorem sum_ite_le (k G : Nat) :
    ∀ l : List Nat, l.Nodup → (l.map fun i => if i = k then G else 0).sum ≤ G
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.sum_cons]
    by_cases hak : a = k
    · subst hak
      simp only [eq_self, ↓reduceIte]
      rw [sum_ite_zero a G l h.1]; omega
    · simp only [hak, ite_false]
      have := sum_ite_le k G l h.2
      omega

/-- The value at `i` of a function given on the keys of an association list. -/
def lkSum (g : Nat → Nat → Nat) (L : List (Nat × Nat)) (i : Nat) : Nat :=
  match L.lookup i with
  | some a => g i a
  | none => 0

theorem lkSum_cons (g : Nat → Nat → Nat) (p : Nat × Nat) (L : List (Nat × Nat)) (i : Nat) :
    lkSum g (p :: L) i ≤ (if i = p.1 then g p.1 p.2 else 0) + lkSum g L i := by
  obtain ⟨k, b⟩ := p
  unfold lkSum
  by_cases h : i = k
  · subst h; simp [List.lookup]
  · have : (i == k) = false := by simp [h]
    simp [List.lookup, this, h]

/-- Summing a lookup over distinct indices counts every entry at most once. -/
theorem sum_lkSum_le (g : Nat → Nat → Nat) (l : List Nat) (hl : l.Nodup) :
    ∀ L : List (Nat × Nat), (l.map (lkSum g L)).sum ≤ (L.map fun p => g p.1 p.2).sum
  | [] => by
    have : ∀ i ∈ l, lkSum g [] i ≤ 0 := fun i _ => by simp [lkSum, List.lookup]
    have := sum_map_const_le (lkSum g []) 0 l this
    simp at this ⊢; omega
  | p :: L => by
    have h1 := sum_map_le (l := l) (f := lkSum g (p :: L))
      (g := fun i => (if i = p.1 then g p.1 p.2 else 0) + lkSum g L i)
      (fun i _ => lkSum_cons g p L i)
    rw [sum_map_add] at h1
    have h2 := sum_ite_le p.1 (g p.1 p.2) l hl
    have h3 := sum_lkSum_le g l hl L
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## The FRI potential -/

/-- `pot κ n0 c k = Σ_{j = c+1}^{c+k} (κ + 64·(n0 - j))`. -/
def pot (κ n0 : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | c, k + 1 => κ + 64 * (n0 - (c + 1)) + pot κ n0 (c + 1) k

theorem pot_add (κ n0 : Nat) : ∀ a c k, pot κ n0 c (a + k) = pot κ n0 c a + pot κ n0 (c + a) k
  | 0, c, k => by simp [pot]
  | a + 1, c, k => by
    rw [show a + 1 + k = (a + k) + 1 by omega]
    simp only [pot]
    rw [pot_add κ n0 a (c + 1) k, show c + 1 + a = c + (a + 1) by omega]
    omega

theorem pot_ge (κ n0 : Nat) :
    ∀ a c, κ * (a + 1) + 64 * (n0 - (c + (a + 1))) ≤ pot κ n0 c (a + 1)
  | 0, c => by simp [pot]
  | a + 1, c => by
    have ih := pot_ge κ n0 a (c + 1)
    simp only [pot] at ih ⊢
    rw [show c + 1 + (a + 1) = c + (a + 1 + 1) by omega] at ih
    rw [Nat.mul_succ]
    generalize κ * (a + 1) = t at *
    omega

theorem pot_mono_n0 (κ : Nat) {n0 N : Nat} (h : n0 ≤ N) :
    ∀ k c, pot κ n0 c k ≤ pot κ N c k
  | 0, c => by simp [pot]
  | k + 1, c => by
    simp only [pot]
    have := pot_mono_n0 κ h k (c + 1)
    have : n0 - (c + 1) ≤ N - (c + 1) := by omega
    omega

theorem pot_mono_k (κ n0 c : Nat) {k k' : Nat} (h : k ≤ k') : pot κ n0 c k ≤ pot κ n0 c k' := by
  rw [show k' = k + (k' - k) by omega, pot_add]
  omega

/-! ## FRI commitments -/

section
variable (A : Air) (prm : Params) (hdr : List Nat)

/-- Per-query bytes of the FRI oracle committed at layer `p.1` with arity log `p.2`. -/
def fcost (n0 : Nat) (p : Nat × Nat) : Nat := 4 * (8 * 2 ^ p.2) + 64 * (n0 - p.1 - p.2)

theorem fcost_step (κ n0 ℓ c nxt rest : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ)
    (h1 : c < nxt) (h2 : nxt ≤ ℓ) (h3 : nxt ≤ c + max prm.maxArityLog 1)
    (ih : rest ≤ pot κ n0 nxt (ℓ - nxt)) :
    fcost n0 (c, nxt - c) + rest ≤ pot κ n0 c (ℓ - c) := by
  have hsplit := pot_add κ n0 (nxt - c) c (ℓ - nxt)
  rw [show nxt - c + (ℓ - nxt) = ℓ - c by omega, show c + (nxt - c) = nxt by omega] at hsplit
  have hge := pot_ge κ n0 (nxt - c - 1) c
  rw [show nxt - c - 1 + 1 = nxt - c by omega, show c + (nxt - c) = nxt by omega] at hge
  have hk := hκ (nxt - c) (by omega) (by omega)
  unfold fcost
  simp only
  rw [show n0 - c - (nxt - c) = n0 - nxt by omega]
  rw [Nat.mul_comm (nxt - c) κ] at hk
  generalize 2 ^ (nxt - c) = e at *
  generalize κ * (nxt - c) = t at *
  omega

theorem go_cost (κ n0 ℓ : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ) :
    ∀ fuel c, ((friCommits.go A prm hdr ℓ c fuel).map (fcost n0)).sum ≤ pot κ n0 c (ℓ - c)
  | 0, c => by simp [friCommits.go]
  | fuel + 1, c => by
    rw [friCommits.go]
    dsimp only
    split
    · simp
    · rename_i hcl
      simp only [List.map_cons, List.sum_cons]
      split
      · rename_i i hi
        have := List.mem_of_find?_eq_some hi
        simp only [List.mem_map, List.mem_range] at this
        obtain ⟨x, hx, hxi⟩ := this
        exact fcost_step prm κ n0 ℓ c _ _ hκ (by rw [Nat.min_def]; split <;> omega)
          (Nat.min_le_right _ _) (by rw [Nat.min_def]; split <;> omega)
          (go_cost κ n0 ℓ hκ fuel _)
      · exact fcost_step prm κ n0 ℓ c _ _ hκ (by rw [Nat.min_def]; split <;> omega)
          (Nat.min_le_right _ _) (by rw [Nat.min_def]; split <;> omega)
          (go_cost κ n0 ℓ hκ fuel _)

theorem friCommits_cost (κ : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ) :
    ((friCommits A prm hdr).map (fcost (queryLog A prm hdr))).sum
      ≤ pot κ (queryLog A prm hdr) 0 (finalLayer A prm hdr) := by
  have := go_cost A prm hdr κ (queryLog A prm hdr) (finalLayer A prm hdr) hκ
    (finalLayer A prm hdr) 0
  simpa [friCommits] using this

/-! ## Opening sizes -/

theorem openSize_friOracleAt (nq i : Nat) :
    ((friOracleAt A prm hdr i).map (openSize nq)).sum =
      lkSum (fun i a => nq * fcost (queryLog A prm hdr) (i, a)) (friCommits A prm hdr) i := by
  unfold friOracleAt lkSum
  cases (friCommits A prm hdr).lookup i with
  | none => rfl
  | some a => simp [openSize, treeLog, fcost]

theorem fri_open_le (nq κ : Nat) (h : headerOk A prm hdr = true)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ) :
    ((schedOracles (friSchedule A prm hdr)).map (openSize nq)).sum
      ≤ nq * pot κ prm.maxLogLde 0 (prm.maxLogLde - prm.logBlowup - prm.finalLog) := by
  rw [schedOracles_fri, sum_map_flatMap]
  simp only [openSize_friOracleAt]
  have h1 := sum_lkSum_le (fun i a => nq * fcost (queryLog A prm hdr) (i, a))
    (List.range (finalLayer A prm hdr)) List.nodup_range (friCommits A prm hdr)
  have h2 := sum_map_mul nq (fcost (queryLog A prm hdr)) (friCommits A prm hdr)
  have h3 := friCommits_cost A prm hdr κ hκ
  have hq := queryLog_le A prm hdr h
  have h4 := pot_mono_n0 κ hq (finalLayer A prm hdr) 0
  have h5 := pot_mono_k κ prm.maxLogLde 0 (k := finalLayer A prm hdr)
    (k' := prm.maxLogLde - prm.logBlowup - prm.finalLog) (by unfold finalLayer; omega)
  have h6 := Nat.mul_le_mul_left nq (Nat.le_trans h3 (Nat.le_trans h4 h5))
  refine Nat.le_trans h1 ?_
  rw [h2]; exact h6

/-! ## Main/aux/quotient openings -/

/-- The layout entry of table `T` at log `l`. -/
def mkL (prm : Params) (T : Air.Table) (l : Nat) : TLayout where
  log := l
  lde := l + prm.logBlowup
  width := T.width
  aux := T.auxCount prm.auxGroup
  quot := T.quotCount prm.auxGroup
  sendG := numGroups (T.numSide true) prm.auxGroup
  recvG := numGroups (T.numSide false) prm.auxGroup

theorem layout_eq : layout A prm hdr = (A.tables.zip hdr).map fun p => mkL prm p.1 p.2 := by
  unfold layout
  apply List.map_congr_left
  intro p _
  obtain ⟨T, l⟩ := p
  rfl

theorem layout_sum_le (G : Air.Table → Nat) (f : TLayout → Nat)
    (hfg : ∀ (T : Air.Table) (l : Nat), f (mkL prm T l) = G T) :
    ((layout A prm hdr).map f).sum ≤ (A.tables.map G).sum := by
  rw [layout_eq, List.map_map]
  have : (A.tables.zip hdr).map (f ∘ fun p => mkL prm p.1 p.2)
      = (A.tables.zip hdr).map fun p => G p.1 := by
    apply List.map_congr_left
    intro p _
    exact hfg p.1 p.2
  rw [this]
  exact sum_zip_fst_le G A.tables hdr

theorem open_layout_le (nq : Nat) (h : headerOk A prm hdr = true)
    (G : Air.Table → Nat) (f : TLayout → Nat)
    (hfg : ∀ (T : Air.Table) (l : Nat), f (mkL prm T l) = G T) :
    openSize nq ((layout A prm hdr).map fun L => (L.lde, f L))
      ≤ nq * (4 * (A.tables.map G).sum + 64 * prm.maxLogLde) := by
  unfold openSize
  apply Nat.mul_le_mul_left
  rw [List.map_map]
  have h1 : ((layout A prm hdr).map ((·.2) ∘ fun L => (L.lde, f L))).sum ≤ (A.tables.map G).sum :=
    layout_sum_le A prm hdr G _ hfg
  have h2 : treeLog ((layout A prm hdr).map fun L => (L.lde, f L)) ≤ prm.maxLogLde := by
    apply treeLog_le_of
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨L, hL, rfl⟩ := hp
    exact lde_le_of_headerOk A prm hdr h L hL
  omega

/-! ## The commit-phase prefix -/

theorem prefixSize_append (a b : List Slot) : prefixSize (a ++ b) = prefixSize a + prefixSize b := by
  simp [prefixSize, List.map_append, List.sum_append]

theorem prefixSize_flatMap_le {α : Type} (f : α → List Slot) (k : Nat) :
    ∀ l : List α, (∀ x ∈ l, prefixSize (f x) ≤ k) → prefixSize (l.flatMap f) ≤ l.length * k
  | [], _ => by simp [prefixSize]
  | a :: l, h => by
    rw [List.flatMap_cons, prefixSize_append, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := prefixSize_flatMap_le f k l fun x hx => h x (by simp [hx])
    omega

theorem prefix_fri_le (h : headerOk A prm hdr = true) :
    prefixSize (friSchedule A prm hdr) ≤ 64 * prm.maxLogLde + 64 := by
  unfold friSchedule
  simp only [prefixSize_append]
  have h4 := finalLayer_le_queryLog A prm hdr
  have h5 : finalLayer A prm hdr ≤ prm.maxLogLde := Nat.le_trans h4 (queryLog_le A prm hdr h)
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (prefixSize_flatMap_le _ 64 _ ?_)
    (Nat.le_of_eq (?_ : _ = 0))) (Nat.le_of_eq (rfl : prefixSize [Slot.msg [.elems 2]] = 64))) ?_
  · intro i _
    rw [prefixSize_append]
    cases rollInAt A prm hdr i <;> cases (friCommits A prm hdr).lookup i <;>
      simp [prefixSize, partSize]
  · cases rollInAt A prm hdr (finalLayer A prm hdr) <;> simp [prefixSize]
  · rw [List.length_range]
    have : prefixSize [Slot.msg [.elems 2]] = 64 := rfl
    omega

/-- Static number of running-product finals (K elements) of the AIR. -/
def finalsMax (A : Air) (prm : Params) : Nat :=
  (A.tables.map fun T => numGroups (T.numSide true) prm.auxGroup +
    numGroups (T.numSide false) prm.auxGroup).sum

/-- Header-free prefix bound. -/
def prefixMax (A : Air) (prm : Params) : Nat :=
  (8 + A.tables.length) + 64 + (64 + 32 * finalsMax A prm) + 64 + 32 * totalCols A prm +
    (64 * prm.maxLogLde + 64)

theorem prefix_le (h : headerOk A prm hdr = true) :
    prefixSize (schedule A prm hdr) ≤ prefixMax A prm := by
  unfold schedule
  dsimp only
  simp only [prefixSize_append]
  have hb := prefixSize_flatMap_le (fun _ => [Slot.msg [], Slot.chal false]) 0
    (List.range (batchRounds (layout A prm hdr) - 1)) (by intro _ _; simp [prefixSize])
  have hf := prefix_fri_le A prm hdr h
  have hfin := layout_sum_le A prm hdr
    (fun T => numGroups (T.numSide true) prm.auxGroup + numGroups (T.numSide false) prm.auxGroup)
    (fun L => L.sendG + L.recvG) (fun _ _ => rfl)
  have hood := layout_sum_le A prm hdr
    (fun T => 2 * T.width + 2 * T.auxCount prm.auxGroup + T.quotCount prm.auxGroup)
    (fun L => 2 * L.width + 2 * L.aux + L.quot) (fun _ _ => rfl)
  simp only [Nat.mul_zero] at hb
  simp only [prefixSize, partSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hb hf ⊢
  unfold prefixMax finalsMax totalCols
  omega

/-- **Header-free proof-size bound** (`κ`: per-FRI-layer arity cost). -/
def sizeMax (A : Air) (prm : Params) (κ : Nat) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixMax A prm +
    nq * (4 * (A.tables.map fun T => T.width).sum + 64 * N) +
    nq * (4 * (A.tables.map fun T => 8 * T.auxCount prm.auxGroup).sum + 64 * N) +
    nq * (4 * (A.tables.map fun T => 8 * T.quotCount prm.auxGroup).sum + 64 * N) +
    nq * pot κ N 0 (N - prm.logBlowup - prm.finalLog)

end

/-- **Generic size bound**: on every admissible header, `sizeBound ≤ sizeMax`. -/
theorem sizeBound_le {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (hdr : List Nat) (κ : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ)
    (h : headerOk A prm hdr = true) :
    sizeBound (Iop.verifier F K A prm) hdr ≤ sizeMax A prm κ := by
  show prefixSize (schedule A prm hdr) +
    ((schedOracles (schedule A prm hdr)).map (openSize (prm.numChunks * prm.posPerChunk))).sum ≤ _
  rw [schedOracles_schedule]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons]
  have hp := prefix_le A prm hdr h
  have h1 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => T.width) (fun L => L.width) (fun _ _ => rfl)
  have h2 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.auxCount prm.auxGroup) (fun L => 8 * L.aux) (fun _ _ => rfl)
  have h3 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.quotCount prm.auxGroup) (fun L => 8 * L.quot) (fun _ _ => rfl)
  have h4 := fri_open_le A prm hdr (prm.numChunks * prm.posPerChunk) κ h hκ
  unfold sizeMax
  dsimp only at h1 h2 h3 ⊢
  omega

end SizeBound

end ZkFormal.Prover
