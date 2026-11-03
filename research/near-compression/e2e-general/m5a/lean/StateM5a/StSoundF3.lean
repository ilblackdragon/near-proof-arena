import StateM5a.WsBus

/-!
# StateM5a.StSoundF3 — the final value of an entry is its latest access (record level)

For one working-set entry (index `i`, key digest `kd`, INTAKE value `v0`), with the facts
`WsEntries.ws_entries` / `WsKey.ws_decoded_final3` give about the touched-leaf rows `wsl` and the
accesses `wsa` (the first touching segment opens with `v0`, a later one with the closing value of
the last earlier touching segment, each closing value is `lastVal` of its segment's accesses in
time order, every access of `kd` belongs to a touched leaf of index `i` in its segment):

* **`ncur_latest`**: a touched leaf of segment `s` closes with `v0` if no access of `kd` has
  segment `≤ s`, else with the written value of the access of `kd` that is greatest in
  `(segment, time)` order among those with segment `≤ s`;
* **`final_latest`**: hence the FINAL value (`v0` if untouched, else the closing value of the last
  touching segment) is `v0` if `kd` has no access, else the written value of its
  `(segment, time)`-greatest access.
-/

namespace StateM5a.StSound

open StateM5a.WsBus StateM5a.WsCost

/-- `(s, t) ≤ (s', t')` lexicographically. -/
def LexLe (s t s' t' : Nat) : Prop := s < s' ∨ (s = s' ∧ t ≤ t')

section
variable {Kd V α : Type} [DecidableEq Kd]

/-- `v` is the latest written value of `kd` among the accesses whose segment satisfies `P`, or `v0`
if there are none. -/
def Latest (wsa : List (WsaRow Kd V)) (kd : Kd) (v0 : V) (P : Nat → Prop) (v : V) : Prop :=
  (v = v0 ∧ ∀ a ∈ wsa, a.kd = kd → ¬ P a.seg) ∨
  (∃ a ∈ wsa, a.kd = kd ∧ P a.seg ∧ v = a.new ∧ ∀ b ∈ wsa, b.kd = kd → P b.seg → LexLe b.seg b.t a.seg a.t)

theorem Latest.congr {wsa : List (WsaRow Kd V)} {kd : Kd} {v0 : V} {P Q : Nat → Prop} {v : V}
    (hPQ : ∀ a ∈ wsa, a.kd = kd → (P a.seg ↔ Q a.seg)) (h : Latest wsa kd v0 P v) : Latest wsa kd v0 Q v := by
  rcases h with ⟨h1, h2⟩ | ⟨a, ha, h1, h2, h3, h4⟩
  · exact .inl ⟨h1, fun a ha hk hq => h2 a ha hk ((hPQ a ha hk).2 hq)⟩
  · exact .inr ⟨a, ha, h1, (hPQ a ha h1).1 h2, h3, fun b hb hk hq => h4 b hb hk ((hPQ b hb hk).2 hq)⟩

theorem exists_max {β : Type} (f : β → Nat) (p : β → Prop) :
    ∀ L : List β, (∃ x ∈ L, p x) → ∃ x ∈ L, p x ∧ ∀ y ∈ L, p y → f y ≤ f x
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | z :: L, h => by
    by_cases hL : ∃ x ∈ L, p x
    · obtain ⟨x, hx, px, hm⟩ := exists_max f p L hL
      by_cases hz : p z ∧ f x ≤ f z
      · refine ⟨z, List.mem_cons_self .., hz.1, fun y hy py => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans (hm y hy py) hz.2
      · refine ⟨x, List.mem_cons_of_mem _ hx, px, fun y hy py => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_of_lt (Nat.lt_of_not_le fun h' => hz ⟨py, h'⟩)
        · exact hm y hy py
    · obtain ⟨x, hx, px⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨x, List.mem_cons_self .., px, fun y hy py => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · exact absurd ⟨y, hy, py⟩ hL
      · exact absurd ⟨x, hx, px⟩ hL

variable (wsl : List (WslRow Kd V α)) (wsa : List (WsaRow Kd V)) (i : Nat) (kd : Kd) (v0 : V)
  (hkd : ∀ l ∈ wsl, l.i = i → l.kd = kd)
  (hacc : ∀ a ∈ wsa, a.kd = kd → ∃ l ∈ wsl, l.i = i ∧ l.seg = a.seg)
  (hfirst : ∀ l ∈ wsl, l.i = i → (∀ l' ∈ wsl, l'.i = i → l.seg ≤ l'.seg) → l.cur = v0)
  (hprev : ∀ l ∈ wsl, l.i = i → ∀ l' ∈ wsl, l'.i = i → l'.seg < l.seg →
    (∀ l'' ∈ wsl, l''.i = i → l''.seg < l.seg → l''.seg ≤ l'.seg) → l.cur = l'.ncur)
  (hchain : ∀ l ∈ wsl, ∃ s : List (Acc V), s.Perm (accOf wsa l.key) ∧
    s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = lastVal l.cur s)
include hkd hacc hfirst hprev hchain

/-- **A touched leaf closes with the latest written value of its segments so far.** -/
theorem ncur_latest : ∀ s, ∀ l ∈ wsl, l.i = i → l.seg = s → Latest wsa kd v0 (· ≤ s) l.ncur := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro l hl hli hls
  -- the opening value
  have hcur : Latest wsa kd v0 (· < s) l.cur := by
    by_cases hS : ∃ l' ∈ wsl, l'.i = i ∧ l'.seg < s
    · obtain ⟨l', hl', ⟨hi', hs'⟩, hm⟩ := exists_max (fun l' => l'.seg) (fun l' => l'.i = i ∧ l'.seg < s) wsl hS
      have e := hprev l hl hli l' hl' hi' (by rw [hls]; exact hs')
        (fun l'' hl'' hi'' hs'' => hm l'' hl'' ⟨hi'', by rw [← hls]; exact hs''⟩)
      rw [e]
      refine Latest.congr (fun a ha hk => ?_) (ih l'.seg hs' l' hl' hi' rfl)
      obtain ⟨l'', hl'', hi'', hs''⟩ := hacc a ha hk
      constructor
      · intro h; omega
      · intro h
        have := hm l'' hl'' ⟨hi'', by omega⟩
        omega
    · have e := hfirst l hl hli (fun l' hl' hi' => by
        rw [hls]; exact Nat.le_of_not_lt fun h => hS ⟨l', hl', hi', h⟩)
      refine .inl ⟨e, fun a ha hk hlt => ?_⟩
      obtain ⟨l'', hl'', hi'', hs''⟩ := hacc a ha hk
      exact hS ⟨l'', hl'', hi'', by omega⟩
  -- the closing value
  obtain ⟨sl, hp, hsort, hn⟩ := hchain l hl
  have hkey : l.key = (s, kd) := by
    show (l.seg, l.kd) = _
    rw [hls, hkd l hl hli]
  have hmem : ∀ b ∈ wsa, b.kd = kd → b.seg = s → b.acc ∈ sl := by
    intro b hb hk hs
    refine hp.mem_iff.2 (List.mem_map.2 ⟨b, List.mem_filter.2 ⟨hb, ?_⟩, rfl⟩)
    rw [hkey]
    simp [WsaRow.key, hk, hs]
  cases sl with
  | nil =>
    rw [hn]
    refine Latest.congr (fun a ha hk => ?_) hcur
    constructor
    · intro h; omega
    · intro h
      rcases Nat.lt_or_ge a.seg s with h' | h'
      · exact h'
      · exact absurd (hmem a ha hk (by omega)) List.not_mem_nil
  | cons h rest =>
    obtain ⟨b, hb, hbe⟩ := List.mem_map.1 (hp.mem_iff.1 (List.mem_cons_self ..))
    obtain ⟨hb, hbk⟩ := List.mem_filter.1 hb
    have hbk' : b.key = (s, kd) := by rw [← hkey]; exact of_decide_eq_true hbk
    simp only [WsaRow.key, Prod.mk.injEq] at hbk'
    refine .inr ⟨b, hb, hbk'.2, Nat.le_of_eq hbk'.1, ?_, fun b' hb' hk' hs' => ?_⟩
    · rw [hn, ← hbe]; rfl
    · rcases Nat.lt_or_ge b'.seg s with h' | h'
      · exact .inl (by omega)
      · refine .inr ⟨by omega, ?_⟩
        have hm := hmem b' hb' hk' (by omega)
        rw [List.pairwise_cons] at hsort
        rcases List.mem_cons.1 hm with e | e
        · rw [← hbe] at e
          have := congrArg Acc.t e
          exact Nat.le_of_eq this
        · have := hsort.1 _ e
          rw [← hbe] at this
          exact Nat.le_of_lt this

/-- **The FINAL value is the latest written value** (or `v0`). -/
theorem final_latest {vF : V} (hun : (∀ l ∈ wsl, l.i ≠ i) → vF = v0)
    (hto : ∀ l ∈ wsl, l.i = i → (∀ l' ∈ wsl, l'.i = i → l'.seg ≤ l.seg) → vF = l.ncur) :
    Latest wsa kd v0 (fun _ => True) vF := by
  by_cases hT : ∃ l ∈ wsl, l.i = i
  · obtain ⟨l, hl, hli, hm⟩ := exists_max (fun l => l.seg) (fun l => l.i = i) wsl hT
    rw [hto l hl hli hm]
    refine Latest.congr (fun a ha hk => ?_)
      (ncur_latest wsl wsa i kd v0 hkd hacc hfirst hprev hchain l.seg l hl hli rfl)
    obtain ⟨l'', hl'', hi'', hs''⟩ := hacc a ha hk
    have := hm l'' hl'' hi''
    exact ⟨fun _ => trivial, fun _ => by omega⟩
  · rw [hun (fun l hl e => hT ⟨l, hl, e⟩)]
    refine .inl ⟨rfl, fun a ha hk _ => ?_⟩
    obtain ⟨l'', hl'', hi'', -⟩ := hacc a ha hk
    exact hT ⟨l'', hl'', hi''⟩

end

end StateM5a.StSound
