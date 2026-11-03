import NearSpecV3.D2.State

/-!
# StateM5a.StSoundF1 — the spec's committed overlay of a list of storage requests

A storage request (`Req`: `storage_write` / `storage_remove` at time `ts` of segment `seg`, with
its key / value bytes and the linear-memory pointers it read them from) acts on the spec's overlay
`NearSpecV3.D2.Ovl` exactly as nearcore's `TrieUpdate`: `Ovl.set` / `Ovl.remove` on the
prospective overlay, then `Ovl.commit`.  **`committedOf T reqs`** is the committed overlay after
the requests (from `Ovl.ofTrie T`) — the list `Ovl.finalize` sorts and applies.

* **`committedOf_eq`**: `committedOf T reqs = ovl reqs`, the `kvPut`-fold of the requests'
  changes `(key, some val | none)`;
* **`mem_ovl`**: `p ∈ ovl reqs` iff `p` is a request's change and no later request has its key
  (latest write per key);
* **`ovl_nodup`**: the keys of `ovl reqs` are distinct.
-/

namespace StateM5a.StSound

open NearSpec NearSpecV3.D2

/-- An execution-side storage request (M5b's `SREQ` with its bytes). -/
structure Req where
  ts : Nat
  seg : Nat
  pr : Bool
  kptr : Nat
  vptr : Nat
  key : Bytes
  val : Bytes

/-- The request's committed change. -/
def Req.change (q : Req) : Bytes × Option Bytes := (q.key, if q.pr then some q.val else none)

/-- The request on the spec's overlay (`TrieUpdate::set` / `remove`). -/
def Req.apply (o : Ovl) (q : Req) : Ovl := if q.pr then o.set q.key q.val else o.remove q.key

/-- **The spec's committed overlay after the requests.** -/
def committedOf (T : PTrie) (reqs : List Req) : List (Bytes × Option Bytes) :=
  (reqs.foldl Req.apply (Ovl.ofTrie T)).commit.committed

def kvF (c : List (Bytes × Option Bytes)) (p : Bytes × Option Bytes) : List (Bytes × Option Bytes) :=
  kvPut p.1 p.2 c

/-- Latest change per key. -/
def ovl (reqs : List Req) : List (Bytes × Option Bytes) := (reqs.map Req.change).foldl kvF []

/-! ## `kvPut` -/

theorem kvPut_keys (k : Bytes) (v : Option Bytes) :
    ∀ c : List (Bytes × Option Bytes), ∀ x, x ∈ (kvPut k v c).map Prod.fst ↔ x = k ∨ x ∈ c.map Prod.fst
  | [], x => by simp [kvPut]
  | (k', v') :: rest, x => by
    by_cases h : k' = k
    · subst h; simp [kvPut]
    · have ih := kvPut_keys k v rest x
      simp only [kvPut, beq_iff_eq, h, if_false, List.map_cons, List.mem_cons] at ih ⊢
      rw [ih]
      constructor <;> rintro (h' | h' | h') <;> simp [h']

theorem kvPut_nodup (k : Bytes) (v : Option Bytes) :
    ∀ c : List (Bytes × Option Bytes), (c.map Prod.fst).Nodup → ((kvPut k v c).map Prod.fst).Nodup
  | [], _ => by simp [kvPut]
  | (k', v') :: rest, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases e : k' = k
    · subst e; simpa [kvPut] using h
    · simp only [kvPut, beq_iff_eq, e, if_false, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, kvPut_nodup k v rest h.2⟩
      rcases (kvPut_keys k v rest k').1 hm with h' | h'
      · exact e h'
      · exact h.1 h'

theorem kvPut_mem (k : Bytes) (v : Option Bytes) :
    ∀ c : List (Bytes × Option Bytes), (c.map Prod.fst).Nodup → ∀ p,
      p ∈ kvPut k v c ↔ p = (k, v) ∨ (p ∈ c ∧ p.1 ≠ k)
  | [], _, p => by simp [kvPut]
  | (k', v') :: rest, h, p => by
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases e : k' = k
    · subst e
      simp only [kvPut, beq_self_eq_true, if_true, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact .inl h1
        · refine .inr ⟨.inr h1, fun e1 => h.1 ?_⟩
          rw [← e1]; exact List.mem_map_of_mem h1
      · rintro (h1 | ⟨h1 | h1, h2⟩)
        · exact .inl h1
        · exact absurd (by rw [h1]) h2
        · exact .inr h1
    · have ih := kvPut_mem k v rest h.2 p
      simp only [kvPut, beq_iff_eq, e, if_false, List.mem_cons]
      rw [ih]
      constructor
      · rintro (h1 | h1 | ⟨h1, h2⟩)
        · exact .inr ⟨.inl h1, by rw [h1]; exact e⟩
        · exact .inl h1
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h1 | ⟨h1 | h1, h2⟩)
        · exact .inr (.inl h1)
        · exact .inl h1
        · exact .inr (.inr ⟨h1, h2⟩)

theorem foldl_nodup : ∀ (l c : List (Bytes × Option Bytes)), (c.map Prod.fst).Nodup →
    ((l.foldl kvF c).map Prod.fst).Nodup
  | [], _, h => h
  | x :: l, c, h => foldl_nodup l (kvF c x) (kvPut_nodup _ _ c h)

/-- **Membership in a `kvPut` fold: the latest change per key.** -/
theorem mem_foldl : ∀ (l c : List (Bytes × Option Bytes)), (c.map Prod.fst).Nodup → ∀ p,
    p ∈ l.foldl kvF c ↔ (∃ l1 l2, l = l1 ++ p :: l2 ∧ ∀ x ∈ l2, x.1 ≠ p.1) ∨ (p ∈ c ∧ ∀ x ∈ l, x.1 ≠ p.1)
  | [], c, _, p => by simp
  | x :: l, c, h, p => by
    show p ∈ l.foldl kvF (kvF c x) ↔ _
    rw [mem_foldl l (kvF c x) (kvPut_nodup _ _ c h) p, kvF, kvPut_mem _ _ c h p]
    constructor
    · rintro (⟨l1, l2, e, h2⟩ | ⟨h1 | ⟨h1, h1'⟩, h2⟩)
      · exact .inl ⟨x :: l1, l2, by rw [e]; rfl, h2⟩
      · subst h1; exact .inl ⟨[], l, rfl, h2⟩
      · refine .inr ⟨h1, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact fun e => h1' e.symm
        · exact h2 y hy
    · rintro (⟨l1, l2, e, h2⟩ | ⟨h1, h2⟩)
      · cases l1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact .inr ⟨.inl rfl, h2⟩
        | cons y l1 =>
          simp only [List.cons_append, List.cons.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact .inl ⟨l1, l2, rfl, h2⟩
      · exact .inr ⟨.inr ⟨h1, fun e => h2 x (List.mem_cons_self ..) e.symm⟩,
          fun y hy => h2 y (List.mem_cons_of_mem _ hy)⟩

theorem ovl_nodup (reqs : List Req) : ((ovl reqs).map Prod.fst).Nodup :=
  foldl_nodup _ [] List.nodup_nil

theorem mem_ovl (reqs : List Req) (p : Bytes × Option Bytes) :
    p ∈ ovl reqs ↔ ∃ l1 l2, reqs.map Req.change = l1 ++ p :: l2 ∧ ∀ x ∈ l2, x.1 ≠ p.1 := by
  unfold ovl
  rw [mem_foldl _ [] List.nodup_nil p]
  simp

/-! ## The spec's overlay -/

theorem apply_fields (o : Ovl) (q : Req) :
    (Req.apply o q).prosp = kvF o.prosp q.change ∧ (Req.apply o q).committed = o.committed := by
  unfold Req.apply Req.change kvF
  cases q.pr <;> simp [Ovl.set, Ovl.remove]

theorem foldl_apply : ∀ (reqs : List Req) (o : Ovl),
    (reqs.foldl Req.apply o).prosp = (reqs.map Req.change).foldl kvF o.prosp ∧
    (reqs.foldl Req.apply o).committed = o.committed
  | [], o => ⟨rfl, rfl⟩
  | q :: rest, o => by
    obtain ⟨h1, h2⟩ := foldl_apply rest (Req.apply o q)
    obtain ⟨a1, a2⟩ := apply_fields o q
    refine ⟨?_, ?_⟩
    · rw [List.foldl_cons, h1, a1]; rfl
    · rw [List.foldl_cons, h2, a2]

/-- `kvPut` of a fresh key appends. -/
theorem kvPut_fresh (k : Bytes) (v : Option Bytes) :
    ∀ c : List (Bytes × Option Bytes), k ∉ c.map Prod.fst → kvPut k v c = c ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have e : (k' == k) = false := by simp [beq_iff_eq]; exact fun e => h.1 e.symm
    simp only [kvPut, e, Bool.false_eq_true, if_false, List.cons_append]
    rw [kvPut_fresh k v rest h.2]

theorem foldl_fresh : ∀ (l c : List (Bytes × Option Bytes)), ((c ++ l).map Prod.fst).Nodup →
    l.foldl kvF c = c ++ l
  | [], c, _ => by simp
  | x :: l, c, h => by
    have hx : x.1 ∉ c.map Prod.fst := by
      intro hm
      simp only [List.map_append, List.map_cons] at h
      exact (List.nodup_append.1 h).2.2 _ hm _ (List.mem_cons_self ..) rfl
    show l.foldl kvF (kvPut x.1 x.2 c) = _
    rw [kvPut_fresh _ _ c hx, foldl_fresh l (c ++ [(x.1, x.2)]) (by simpa using h)]
    simp

/-- **The spec's committed overlay is the latest change per key.** -/
theorem committedOf_eq (T : PTrie) (reqs : List Req) : committedOf T reqs = ovl reqs := by
  obtain ⟨h1, h2⟩ := foldl_apply reqs (Ovl.ofTrie T)
  have := foldl_fresh (ovl reqs) [] (by simpa using ovl_nodup reqs)
  simp only [List.nil_append] at this
  show List.foldl _ (List.foldl Req.apply (Ovl.ofTrie T) reqs).committed
    (List.foldl Req.apply (Ovl.ofTrie T) reqs).prosp = _
  rw [h1, h2]
  exact this

/-! ## Pairwise orders -/

theorem pairwise_two {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with e1 | ha1 <;> rcases List.mem_cons.1 hb with e2 | hb1
    · exact absurd (e1.trans e2.symm) hne
    · subst e1; exact .inl (h.1 b hb1)
    · subst e2; exact .inr (h.1 a ha1)
    · exact pairwise_two h.2 ha1 hb1 hne

end StateM5a.StSound
