import ZkFormal.Bcs.TransStatements

/-!
# ZkFormal.Bcs.TransCompose — L3's `RbrWith` gives the byte-level RBR facts

`transport`: from lane L3's round-by-round facts for L4's IOP `V` (any doomed
predicate `D` with `Udr.RbrWith V InLang Kall bad agree D`), the byte-level
predicate `DoomedB V D` satisfies exactly the hypotheses `hinit`, `hmsg`,
`hround`, `hquery` of `Bcs.stark_romSound'`, with
* `B = bad · Dm`, where `Dm` bounds the fibers of the challenge decoders
  (L1: `3^8` for `decodeChal`, `2·3^8` for `decodeOod`), and
* `g j = G` for any `G ≥ agree(2^n0)^p · 2^(256 - p·n0)` over admissible
  headers (`n0 = queryLog`, `p = posPerChunk`).
Proved from the statements in `Bcs.TransStatements`.
-/

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem count_false_le {α : Type} (l : List α) (P : α → Prop) (h : ∀ a ∈ l, ¬ P a) (G : Nat) :
    count l P ≤ G := by
  have : count l P ≤ count l (fun _ => False) := count_mono_mem l fun a ha hp => h a ha hp
  rw [count_const] at this
  simp at this
  omega

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

theorem points_ne (V : Stark.IopSpec F K) (hp : 0 < V.posPerChunk) (vt : View) (j : Nat) (y : Bytes) :
    ∃ pt, pt ∈ (Adapter.adapt (F := F) V).points vt j y := by
  simp only [Adapter.adapt]
  split
  · refine ⟨_, List.mem_flatMap.mpr ⟨y, List.mem_singleton_self _, List.mem_map.mpr ⟨0, List.mem_range.mpr hp, rfl⟩⟩⟩
  · exact ⟨0, List.mem_singleton_self _⟩

theorem transport (hNone : DecNoneStmt) (hMsg : DecMsgStmt) (hChal : DecChalStmt)
    (hQuery : DecQueryStmt) (hPos : PosCountStmt)
    (V : Stark.IopSpec F K) (hS : Adapter.SchedOk V)
    (InLang : Bytes → Prop) (Kall : List K) (bad : Nat) (agree : Nat → Nat)
    (D : Stark.PT K (Stark.Oracle F) → Prop) (hR : Udr.RbrWith V InLang Kall bad agree D)
    (Dm : Nat) (hdec : ∀ ood (P : K → Prop) b, count Kall P ≤ b →
      count (List.range roRange) (fun v => P (decChal (F := F) ood (LazyRO.answer v))) ≤ b * Dm)
    (hp : 0 < V.posPerChunk) (hpb : V.posPerChunk * V.posBits ≤ 256)
    (hql : ∀ hdr, V.headerOk hdr = true → V.queryLog hdr ≤ V.posBits)
    (G : Nat) (hG : ∀ hdr, V.headerOk hdr = true →
      agree (2 ^ V.queryLog hdr) ^ V.posPerChunk * 2 ^ (256 - V.posPerChunk * V.queryLog hdr) ≤ G) :
    (∀ cb, ¬ InLang cb → DoomedB V D ⟨cb, []⟩) ∧
    (∀ τ roots raw os, DoomedB V D τ → DoomedB V D (τ.push (.msg roots raw os))) ∧
    (∀ τ : PT mmcs, DoomedB V D τ →
      count (List.range roRange) (fun v => ¬ DoomedB V D (τ.push (.chal (LazyRO.answer v)))) ≤ bad * Dm) ∧
    (∀ (τ : PT mmcs) (j : Nat), DoomedB V D τ →
      count (List.range roRange) (fun v =>
        ∀ pt ∈ (Adapter.adapt (F := F) V).points τ.view j (LazyRO.answer v),
          Pass (Adapter.adapt (F := F) V) τ pt) ≤ G) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- init
    intro cb hL σ hσ
    simp only [decodePT, Option.some.injEq] at hσ
    subst hσ
    exact hR.init cb hL
  · -- prover messages
    intro τ roots raw os hd σ' hσ'
    obtain ⟨σ, m, hσ, hnext, rfl⟩ := hMsg F K V hS τ roots raw os σ' hσ'
    exact hR.prover σ m (hd σ hσ) hnext
  · -- challenges
    intro τ hd
    cases hdτ : decodePT (F := F) V τ with
    | none =>
      exact count_false_le _ _ (fun v _ hv => hv fun σ' h' => by
        rw [hNone F K V τ _ hdτ] at h'; cases h') _
    | some σ =>
      obtain ⟨ood, hood⟩ := hChal F K V hS τ σ hdτ
      by_cases hnc : V.NextIsChal σ
      · have h1 := hR.chal σ (hd σ hdτ) hnc
        have h2 := hdec ood _ bad h1
        refine Nat.le_trans (count_mono _ fun v hv => ?_) h2
        refine Classical.byContradiction fun hD => hv fun σ' h' => ?_
        obtain ⟨_, rfl⟩ := hood _ σ' h'
        exact Classical.byContradiction hD
      · exact count_false_le _ _ (fun v _ hv => hv fun σ' h' => by
          exact absurd (hood _ σ' h').1 hnc) _
  · -- query phase
    intro τ j hd
    cases hdv : Adapter.decodeView (F := F) V τ.view with
    | none =>
      refine count_false_le _ _ (fun v _ hall => ?_) _
      obtain ⟨pt, hpt⟩ := points_ne V hp τ.view j (LazyRO.answer v)
      obtain ⟨vals, _, hdec'⟩ := hall pt hpt
      simp only [Adapter.adapt, Adapter.decideA, hdv] at hdec'
      cases hdec'
    | some hs =>
      obtain ⟨hdr, σu⟩ := hs
      obtain ⟨σ, hσ, herase, hat, hshape, hdom, hrows⟩ := hQuery F K V hS τ hdr σu hdv
      have hhv : V.headerOk hdr = true ∧ Adapter.viewHeader V τ.view.entries [] = some hdr := by
        simp only [Adapter.decodeView] at hdv
        split at hdv
        · rename_i hdr' hh
          split at hdv
          · rename_i hok'
            simp only [Option.map_eq_some_iff] at hdv
            obtain ⟨_, _, he⟩ := hdv
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, _⟩ := he
            exact ⟨hok', hh⟩
          · cases hdv
        · cases hdv
      obtain ⟨hok, hvh⟩ := hhv
      by_cases hglob : V.global (V.prep σu) = true
      · have hq := hR.query σ (hd σ hσ) hat hshape (by rw [herase]; exact hglob)
        rw [hdom] at hq
        have hc := hPos V.posPerChunk V.posBits (V.queryLog hdr)
          (fun x => V.ChecksPass σ x (V.trueOpenings σ x)) _ hpb (hql hdr hok) hq
        refine Nat.le_trans (count_mono _ fun v hall => ?_) (Nat.le_trans hc (hG hdr hok))
        intro x hx
        have hx' : x ∈ (Adapter.adapt (F := F) V).points τ.view j (LazyRO.answer v) := by
          simp only [Adapter.adapt, hvh, Stark.IopSpec.positions, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          exact hx
        obtain ⟨vals, hvals, hdec'⟩ := hall x hx'
        simp only [Adapter.adapt, Adapter.decideA, hdv, Bool.and_eq_true] at hdec'
        unfold Stark.IopSpec.ChecksPass
        rw [← hrows x vals hvals, herase]
        exact hdec'.2
      · refine count_false_le _ _ (fun v _ hall => ?_) _
        obtain ⟨pt, hpt⟩ := points_ne V hp τ.view j (LazyRO.answer v)
        obtain ⟨vals, _, hdec'⟩ := hall pt hpt
        simp only [Adapter.adapt, Adapter.decideA, hdv, Bool.and_eq_true] at hdec'
        exact hglob hdec'.1

end

end ZkFormal.Bcs.Transport
