import ZkFormal.Near.Extract.SmallViews

/-!
# ZkFormal.Near.Link.MrkLevels — `mrkShape` and nearcore `merklize`, combinatorially

* `sz n j` — size of level `j` (`sz n 0 = n`, halving rounded up);
* `levels_mem` / `levels_complete` / `levels_nodup` — the entries of
  `mrkLevels` are exactly the positions `(j, i)` of the levels above the leaves,
  each once, hashed iff the node has two children;
* `lvl`, `merkleLevel_get`, `merkleRoot_eq` — the levels of `merklize`.
-/

namespace ZkFormal.Near

open NearSpec

namespace Link

def sz (n : Nat) : Nat → Nat
  | 0 => n
  | j + 1 => (sz n j + 1) / 2

theorem sz_shift : ∀ d sp, sz sp (d + 1) = sz ((sp + 1) / 2) d
  | 0, _ => rfl
  | d + 1, sp => by
    show (sz sp (d + 1) + 1) / 2 = (sz ((sp + 1) / 2) d + 1) / 2
    rw [sz_shift d sp]

theorem levels_mem : ∀ f j sp j' i b, (j', i, b) ∈ mrkLevels f j sp →
    ∃ d, j' = j + d ∧ i < sz sp (d + 1) ∧ b = decide (2 * i + 1 < sz sp d) ∧
      ∀ d', d' < d → sz sp (d' + 1) ≠ 1
  | 0, _, _, _, _, _, h => by simp [mrkLevels] at h
  | f + 1, j, sp, j', i, b, h => by
    simp only [mrkLevels, List.mem_append, List.mem_map, List.mem_range] at h
    rcases h with ⟨i', hi', he⟩ | h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨0, rfl, hi', rfl, fun d' h => absurd h (Nat.not_lt_zero _)⟩
    · split at h
      · simp at h
      · next hs =>
        obtain ⟨d, h1, h2, h3, h4⟩ := levels_mem f (j + 1) ((sp + 1) / 2) j' i b h
        refine ⟨d + 1, by omega, by rw [sz_shift]; exact h2, by rw [sz_shift]; exact h3, ?_⟩
        intro d' hd'
        cases d' with
        | zero => exact hs
        | succ d' => rw [sz_shift]; exact h4 d' (by omega)

theorem levels_complete : ∀ f j sp d, d < f → (∀ d', d' < d → sz sp (d' + 1) ≠ 1) →
    ∀ i, i < sz sp (d + 1) → ∃ b, (j + d, i, b) ∈ mrkLevels f j sp
  | 0, _, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, j, sp, 0, _, _, i, hi => by
    refine ⟨decide (2 * i + 1 < sp), ?_⟩
    simp only [mrkLevels, List.mem_append, List.mem_map, List.mem_range]
    exact .inl ⟨i, hi, rfl⟩
  | f + 1, j, sp, d + 1, hd, hne, i, hi => by
    have hs : (sp + 1) / 2 ≠ 1 := hne 0 (by omega)
    obtain ⟨b, hb⟩ := levels_complete f (j + 1) ((sp + 1) / 2) d (by omega)
      (fun d' h => by rw [← sz_shift]; exact hne (d' + 1) (by omega)) i (by rw [← sz_shift]; exact hi)
    refine ⟨b, ?_⟩
    simp only [mrkLevels, List.mem_append]
    right; rw [if_neg hs, show j + (d + 1) = j + 1 + d from by omega]; exact hb

theorem levels_nodup : ∀ f j sp, ((mrkLevels f j sp).map fun e => (e.1, e.2.1)).Nodup
  | 0, _, _ => by simp [mrkLevels]
  | f + 1, j, sp => by
    simp only [mrkLevels, List.map_append, List.map_map]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun h he => h (by
        simp only [Function.comp, Prod.mk.injEq] at he; exact he.2))
    · split
      · simp
      · exact levels_nodup f (j + 1) _
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      split at hy
      · simp at hy
      · obtain ⟨e, he, hee⟩ := List.mem_map.mp hy
        obtain ⟨d, h1, -⟩ := levels_mem f (j + 1) _ e.1 e.2.1 e.2.2 he
        simp only [Function.comp, Prod.mk.injEq] at hee
        omega

/-! ## merklize -/

def lvl (L : List Bytes) : Nat → List Bytes
  | 0 => L
  | j + 1 => merkleLevel (lvl L j)

theorem merkleLevel_length : ∀ (l : List Bytes), (merkleLevel l).length = (l.length + 1) / 2
  | [] => by simp [merkleLevel]
  | [_] => by simp [merkleLevel]
  | a :: b :: rest => by
    simp only [merkleLevel, List.length_cons, merkleLevel_length rest]; omega

theorem lvl_length (L : List Bytes) : ∀ j, (lvl L j).length = sz L.length j
  | 0 => rfl
  | j + 1 => by simp only [lvl, sz, merkleLevel_length, lvl_length L j]

theorem lvl_shift (L : List Bytes) : ∀ j, lvl L (j + 1) = lvl (merkleLevel L) j
  | 0 => rfl
  | j + 1 => by simp only [lvl]; rw [← lvl_shift L j]; rfl

theorem merkleLevel_get : ∀ (l : List Bytes) (i : Nat), i < (l.length + 1) / 2 →
    (merkleLevel l).getD i [] =
      if 2 * i + 1 < l.length then sha256 (l.getD (2 * i) [] ++ l.getD (2 * i + 1) []) else l.getD (2 * i) []
  | [], _, h => by simp at h
  | [a], i, h => by
    have : i = 0 := by simp at h; omega
    subst this; simp [merkleLevel]
  | a :: b :: rest, 0, _ => by simp [merkleLevel]
  | a :: b :: rest, i + 1, h => by
    simp only [List.length_cons] at h
    have := merkleLevel_get rest i (by omega)
    simp only [merkleLevel, List.getD_cons_succ, List.length_cons]
    rw [this, show 2 * (i + 1) = 2 * i + 2 from by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 from by omega]
    simp only [List.getD_cons_succ]
    split <;> split <;> first | rfl | omega

theorem merkleLevel_single (x : Bytes) : merkleLevel [x] = [x] := by simp [merkleLevel]

theorem lvl_single (x : Bytes) : ∀ j, lvl [x] j = [x]
  | 0 => rfl
  | j + 1 => by simp only [lvl, lvl_single x j, merkleLevel_single]

theorem merkleFold_eq : ∀ f (L : List Bytes), 1 ≤ L.length → L.length ≤ f + 1 →
    ∀ J, sz L.length J = 1 → merkleFold f L = (lvl L J).getD 0 []
  | f, [x], _, _, J, _ => by rw [lvl_single]; cases f <;> rfl
  | f, [], h, _, _, _ => by simp at h
  | 0, a :: b :: rest, _, h, _, _ => by simp at h
  | f + 1, a :: b :: rest, _, hf, J, hJ => by
    cases J with
    | zero => simp [sz] at hJ
    | succ J =>
      have hl := merkleLevel_length (a :: b :: rest)
      simp only [List.length_cons] at hl hf hJ
      rw [show merkleFold (f + 1) (a :: b :: rest) = merkleFold f (merkleLevel (a :: b :: rest)) from rfl,
        lvl_shift]
      apply merkleFold_eq f _ (by rw [hl]; omega) (by rw [hl]; omega)
      rw [hl, ← sz_shift]; exact hJ

theorem merkleRoot_eq (L : List Bytes) (hL : 1 ≤ L.length) (J : Nat) (hJ : sz L.length J = 1) :
    merkleRoot L = (lvl L J).getD 0 [] :=
  merkleFold_eq L.length L hL (by omega) J hJ

end Link

end ZkFormal.Near
