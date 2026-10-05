import ZkFormal.Udr.Np.Avail

/-!
# ZkFormal.Udr.Np.FrameMsg — `MsgLateStmt`: later messages do not change the stage

A message at `E ≥ 10` (batching `msg []`, FRI `msg []` / commitment, final
polynomial) leaves header and challenges unchanged and only appends oracles
and clear-text parts.  `GlobalFail` and the batched DEEP words read the first
three oracles and the first two clear-text parts, present since `E ≥ 9`.
A drawn FRI condition of key `K` reads only the committed layers `c` with
`2c + 1 ≤ K`, whose oracles are present (`oracle_avail`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params)

theorem commits_head (hdr : List Nat) (x : Nat × Nat) (h : (friCommits A prm hdr).head? = some x) :
    x.1 = 0 := by
  simp only [friCommits] at h
  generalize hℓ : finalLayer A prm hdr = ℓ at h
  rcases ℓ with _ | ℓ
  · simp [friCommits.go] at h
  · obtain ⟨nxt, -, -, -, -, -, he⟩ := go_step A prm hdr (ℓ + 1) 0 ℓ (by omega)
    rw [he] at h; simp at h; rw [← h]

/-- Agreement of two transcripts on everything FRI words of key `≤ B` read. -/
structure SameFriB (τ τ' : PTn) (B : Nat) : Prop where
  hdr : hdrOf τ' = hdrOf τ
  deep : ∀ m p, deepAtPos A prm τ' m p = deepAtPos A prm τ m p
  look : friChals A prm τ' = friChals A prm τ
  cm : ∀ j (hj : j < (commitsOf A prm τ).length), 2 * ((commitsOf A prm τ)[j]).1 + 1 ≤ B →
    committedAt τ' j = committedAt τ j

variable {A prm}

theorem SameFriB.toSame {τ τ' : PTn} {B : Nat} (h : SameFriB A prm τ τ' B) :
    (n0Of A prm τ' = n0Of A prm τ) ∧ (ellOf A prm τ' = ellOf A prm τ) ∧
    (commitsOf A prm τ' = commitsOf A prm τ) ∧ (permAt A prm τ' = permAt A prm τ) ∧
    (setupData A prm τ' = setupData A prm τ) ∧ (rollG A prm τ' = rollG A prm τ) ∧
    (betaOf A prm τ' = betaOf A prm τ) ∧ (gammaOf A prm τ' = gammaOf A prm τ) := by
  have hn : n0Of A prm τ' = n0Of A prm τ := by simp [n0Of, h.hdr]
  have hl : ellOf A prm τ' = ellOf A prm τ := by simp [ellOf, h.hdr]
  have hp : permAt A prm τ' = permAt A prm τ := by funext i j; simp [permAt, hn, hl]
  refine ⟨hn, hl, by simp [commitsOf, h.hdr], hp, by simp [setupData, hn, hl, hp], ?_,
    by funext i; simp [betaOf, h.look], by funext i; simp [gammaOf, h.look]⟩
  funext i j u; simp [rollG, h.hdr, hn, hp, h.deep]

theorem friF_congrB {τ τ' : PTn} {B : Nat} (h : SameFriB A prm τ τ' B) :
    ∀ i, 2 * i + 1 ≤ B → friF A prm τ' i = friF A prm τ i
  | 0, hB => by
    obtain ⟨hn, -, hc, hp, -, -, -, -⟩ := h.toSame
    funext j u
    simp only [friF, hc, hp, h.deep, hn]
    split
    · rename_i x a hx
      have h0 := commits_head A prm (hdrOf τ) _ (by simpa [commitsOf] using hx)
      have hx' : (commitsOf A prm τ)[0]? = some (x, a) := by rw [← List.head?_eq_getElem?]; exact hx
      obtain ⟨hlen, hx0⟩ := List.getElem?_eq_some_iff.mp hx'
      rw [h.cm 0 hlen (by rw [hx0]; simp at h0 ⊢; omega)]
    · rfl
  | i + 1, hB => by
    obtain ⟨hn, -, hc, hp, hs, hr, hb, hg⟩ := h.toSame
    have ih := friF_congrB h i (by omega)
    simp only [friF, hc, hp, hs, hr, hb, hg, ih]
    split
    · rename_i c a k hf
      have hm := List.mem_of_find?_eq_some hf
      have hpc := List.find?_some hf
      simp only [beq_iff_eq] at hpc
      have hk := List.mem_zipIdx_iff_getElem?.mp hm
      simp only at hk
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
      rw [h.cm k hlt (by rw [hget]; simp; omega)]
    · rfl

theorem friChalGood_congrB {τ τ' : PTn} {B : Nat} (h : SameFriB A prm τ τ' B) (k : Bool × Nat)
    (hk1 : k.1 → 1 ≤ k.2) (hkB : keyOf k ≤ B) (c : Fp8) :
    FriChalGood A prm τ' k.1 k.2 c ↔ FriChalGood A prm τ k.1 k.2 c := by
  obtain ⟨hn, -, -, -, hs, hr, hb, -⟩ := h.toSame
  rcases k with ⟨b, i⟩
  cases b with
  | true =>
    have hi := hk1 rfl
    rw [show keyOf (true, i) = 2 * i from rfl] at hkB
    have hf := friF_congrB h (i - 1) (by omega)
    have he : evenF A prm τ' (i - 1) = evenF A prm τ (i - 1) := by
      funext j u; simp only [evenF, hf, hs]
    have ho : oddF A prm τ' (i - 1) = oddF A prm τ (i - 1) := by
      funext j u; simp only [oddF, hf, hs]
    have hfo : foldF A prm τ' (i - 1) = foldF A prm τ (i - 1) := by
      simp only [foldF, he, ho, hb]
    simp only [FriChalGood, ↓reduceIte, hs, hn, hr, hfo]
  | false =>
    rw [show keyOf (false, i) = 2 * i + 1 from rfl] at hkB
    have hf := friF_congrB h i hkB
    have he : evenF A prm τ' i = evenF A prm τ i := by funext j u; simp only [evenF, hf, hs]
    have ho : oddF A prm τ' i = oddF A prm τ i := by funext j u; simp only [oddF, hf, hs]
    simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte, hs, hn, he, ho]

end

/-! ## `MsgLateStmt` -/

theorem getD_append_of_lt {α : Type} (l l' : List α) (k : Nat) (d : α) (h : k < l.length) :
    (l ++ l').getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem msgLate : MsgLateStmt := by
  intro k hk A prm hok τ m hs' hnext hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE; omega
  have hs : Shaped (Vnp A prm) τ := (shapedPrefix A prm τ).1 m hs'
  obtain ⟨hdr, hh, hok', hsl⟩ := sh_header A prm τ hs (by omega)
  simp only [Stage, show τ.entries.length = (k - 9) + 9 by omega] at hst
  simp only [Stage, len_push, show k + 1 = (k - 8) + 9 by omega, hE]
  -- basic frame facts
  have hh' : (τ.push m).header? = τ.header? := push_header τ m hne
  have hhdr' : hdrOf (τ.push m) = hdrOf τ := by simp [hdrOf, hh']
  have hlay' : layOf A prm (τ.push m) = layOf A prm τ := by simp [layOf, hhdr']
  have hn0' : n0Of A prm (τ.push m) = n0Of A prm τ := by simp [n0Of, hhdr']
  have hch : (τ.push m).chals = τ.chals := push_chals τ m
  obtain ⟨os, hos⟩ := push_oracles τ m
  obtain ⟨es, hes⟩ := push_elems τ m
  -- three oracles and two clear-text parts are present
  have hfit := sh_fit A prm τ hs
  have hpre : 10 ≤ (preSlots A prm hdr).length := by
    rw [preSlots_length]; have : 1 ≤ batchRounds (layout A prm hdr) := Nat.le_max_left _ _; omega
  have htake : ((Vnp A prm).slots τ).take τ.entries.length =
      (preSlots A prm hdr).take 10 ++ ((preSlots A prm hdr).drop 10 ++ friSchedule A prm hdr).take
        (τ.entries.length - 10) := by
    rw [hsl, schedule_eq]
    conv => lhs; rw [← List.take_append_drop 10 (preSlots A prm hdr), List.append_assoc]
    rw [List.take_append, List.length_take, Nat.min_eq_left hpre,
      List.take_of_length_le (by rw [List.length_take]; omega)]
  have hor3 : 3 ≤ τ.oracles.length := by
    rw [hfit.1.length_eq, htake, List.flatMap_append, List.length_append]
    have : (((preSlots A prm hdr).take 10).flatMap slotOr).length = 3 := by
      have := preSlots_or A prm hdr
      rw [← List.take_append_drop 10 (preSlots A prm hdr), List.flatMap_append, List.length_append] at this
      have h2 : (((preSlots A prm hdr).drop 10).flatMap slotOr).length = 0 := by
        simp only [preSlots, List.drop_append, List.length_cons, List.length_nil, Nat.sub_self,
          List.drop_zero, List.drop_eq_nil_of_le (Nat.le_refl _)]
        simp [pairs_or]
      omega
    omega
  have hel2 : 2 ≤ τ.elems.length := by
    rw [hfit.2.length_eq, htake, List.flatMap_append, List.length_append]
    have : (((preSlots A prm hdr).take 10).flatMap slotEl).length = 2 := by
      have := preSlots_el A prm hdr
      rw [← List.take_append_drop 10 (preSlots A prm hdr), List.flatMap_append, List.length_append] at this
      have h2 : (((preSlots A prm hdr).drop 10).flatMap slotEl).length = 0 := by
        simp only [preSlots, List.drop_append, List.length_cons, List.length_nil, Nat.sub_self,
          List.drop_zero, List.drop_eq_nil_of_le (Nat.le_refl _)]
        simp [pairs_el]
      omega
    omega
  have hor' : ∀ i, i < τ.oracles.length → oracleOf (τ.push m) i = oracleOf τ i := by
    intro i hi; simp only [oracleOf, hos]; exact getD_append_of_lt _ _ _ _ hi
  have hel' : ∀ i, i < τ.elems.length → (τ.push m).elems.getD i [] = τ.elems.getD i [] := by
    intro i hi; rw [hes]; exact getD_append_of_lt _ _ _ _ hi
  have hdw : ∀ m', deepWord A prm (τ.push m) m' = deepWord A prm τ m' := by
    intro m'; funext p j
    simp only [deepWord, hlay']
    split
    · rename_i d s hds
      have hk : d.kind = 0 ∨ d.kind = 1 ∨ d.kind = 2 := by
        have hmem := List.mem_of_getElem? hds
        simp only [deepCols, List.mem_flatMap, List.mem_append, List.mem_map] at hmem
        obtain ⟨_, _, h⟩ := hmem
        rcases h with ((((⟨c, _, h⟩ | ⟨c, _, h⟩) | ⟨c, _, h⟩) | ⟨c, _, h⟩) | ⟨c, _, h⟩) <;>
          (simp only [Prod.mk.injEq] at h; rw [← h.1]; simp)
      have hcv : colVal (τ.push m) d p = colVal τ d p := by
        simp only [colVal, hor' d.kind (by omega)]
      simp only [hcv, claimed, hlay', tl, zOf, hch, hn0', hel' 1 (by omega)]
    · rfl
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · -- `GlobalFail` survives
    left
    unfold GlobalFail at hgf ⊢
    rw [hch, hes, hlay', show (τ.push m).cb = τ.cb from rfl]
    revert hgf
    rcases τ.chals with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨z, rest⟩⟩⟩⟩ <;>
      rcases τ.elems with _ | ⟨f, _ | ⟨o, r⟩⟩ <;> simp
  · right
    have hbc : batchChals A prm (τ.push m) = batchChals A prm τ := by
      simp [batchChals, hch, nBatch, hlay']
    have hbw : ∀ m', batchedWord A prm (τ.push m) m' = batchedWord A prm τ m' := by
      intro m'; simp [batchedWord, hbc, hdw]
    have hfc : friChals A prm (τ.push m) = friChals A prm τ := by
      simp [friChals, hhdr', hch, nBatch, hlay']
    refine ⟨⟨L, hlay' ▸ hL, by simpa [BatchFar, hbw, hn0'] using hfar⟩, ?_⟩
    intro q hq
    have hq' : q < (friChals A prm τ).length := by rw [← hfc]; exact hq
    let K := keyOf ((friChals A prm τ)[q]).1
    have hsame : SameFriB A prm τ (τ.push m) K := by
      refine ⟨hhdr', fun m' p => by simp [deepAtPos, hbw], hfc, fun j hj hjB => ?_⟩
      have := oracle_avail A prm τ hs (by omega) q hq' j hj hjB
      funext a p; simp only [committedAt, hor' (3 + j) this]
    have hmem : ((friChals A prm τ)[q]).1 ∈ friChalKinds A prm (hdrOf τ) := by
      have h1 := List.getElem_mem hq'
      generalize (friChals A prm τ)[q] = x at h1 ⊢
      simp only [friChals] at h1; exact (List.of_mem_zip h1).1
    have hk1 := fun h => ((mem_kinds A prm _ _ hmem).2 h).1
    have := (friChalGood_congrB hsame _ hk1 (Nat.le_refl _) _).mpr (hgood q hq')
    simp only [hfc]; exact this

end ZkFormal.Udr.Np
