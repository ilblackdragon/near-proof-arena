import NearSpecV3.PrepD0

/-!
# ZkFormal.NearV3.Sched.Spec.Buckets — `process_bandwidth_requests` over a push log

The spec keeps `BTreeMap<allowance, Vec<Req>>` as an ascending-key list built by `bucketPush`.
The AIR keeps a *push log*: every push is a message `(key, z, ts, v)` with `v = rid·64 + j`
(request `rid`, its `j`-th increase next). This file relates the two:

* `reqAt reqs v` — the spec request of entry `v`: link of `rid`, increases from `j` on;
* `bucketsOf P` — the bucket map obtained by pushing the log `P` in order;
* `groupsOf P` — the same map described directly (ascending distinct keys, each bucket the
  pushes with that key in log order): `bucketsOf_eq_groups`;
* `pop`: the last bucket is the largest key's group, `dropLast` is the map of the other pushes.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- A push message. -/
structure PM where
  key : Nat
  z : Nat
  ts : Nat
  v : Nat
  deriving DecidableEq, Repr

/-- The spec request of entry `v = rid·64 + j`. -/
def reqAt (reqs : List Req) (v : Nat) : Req :=
  let q := reqs.getD (v / 64) ⟨0, []⟩
  ⟨q.link, q.incs.drop (v % 64)⟩

/-- Pushing a log in order. -/
def bucketsOf (reqs : List Req) (P : List PM) : List (Nat × List Req) :=
  P.foldl (fun bk p => bucketPush p.key (reqAt reqs p.v) bk) []

/-- Insert a key into an ascending duplicate-free list. -/
def insKey (k : Nat) : List Nat → List Nat
  | [] => [k]
  | k' :: ks => if k = k' then k' :: ks else if k < k' then k :: k' :: ks else k' :: insKey k ks

/-- Ascending distinct keys of a log. -/
def keysOf (P : List PM) : List Nat := P.foldl (fun ks p => insKey p.key ks) []

/-- The bucket of key `k`. -/
def grp (reqs : List Req) (P : List PM) (k : Nat) : List Req :=
  (P.filter fun p => p.key = k).map fun p => reqAt reqs p.v

def groupsOf (reqs : List Req) (P : List PM) : List (Nat × List Req) :=
  (keysOf P).map fun k => (k, grp reqs P k)

/-- Induction from the right (core has no `reverseRecOn`). -/
theorem snoc_induction {α : Type} {motive : List α → Prop} (h0 : motive [])
    (hs : ∀ l a, motive l → motive (l ++ [a])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons a t ih => rw [List.reverse_cons]; exact hs _ _ ih

/-! ## Sorted key lists -/

/-- Strictly ascending. -/
def Asc : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a < b ∧ Asc (b :: t)

theorem Asc.tail {a : Nat} {t : List Nat} (h : Asc (a :: t)) : Asc t := by
  cases t with
  | nil => trivial
  | cons b t => exact h.2

theorem Asc.lt_of_mem {a : Nat} {t : List Nat} (h : Asc (a :: t)) : ∀ x ∈ t, a < x := by
  induction t generalizing a with
  | nil => intro x hx; cases hx
  | cons b t ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (ih h.2 x hx)

theorem asc_cons {a : Nat} {t : List Nat} (ht : Asc t) (h : ∀ x ∈ t, a < x) : Asc (a :: t) := by
  cases t with
  | nil => trivial
  | cons b t => exact ⟨h b (List.mem_cons_self ..), ht⟩

theorem mem_insKey (k x : Nat) : ∀ ks : List Nat, x ∈ insKey k ks ↔ x = k ∨ x ∈ ks
  | [] => by simp [insKey]
  | k' :: ks => by
    unfold insKey
    by_cases h1 : k = k'
    · subst h1; simp only [ite_true, List.mem_cons]; grind
    · rw [if_neg h1]
      by_cases h2 : k < k'
      · rw [if_pos h2]; simp only [List.mem_cons]
      · rw [if_neg h2]; simp only [List.mem_cons, mem_insKey k x ks]; grind

theorem asc_insKey (k : Nat) : ∀ ks : List Nat, Asc ks → Asc (insKey k ks)
  | [], _ => trivial
  | k' :: ks, h => by
    unfold insKey
    by_cases h1 : k = k'
    · rw [if_pos h1]; exact h
    · rw [if_neg h1]
      by_cases h2 : k < k'
      · rw [if_pos h2]; exact ⟨h2, h⟩
      · rw [if_neg h2]
        refine asc_cons (asc_insKey k ks h.tail) (fun x hx => ?_)
        rcases (mem_insKey k x ks).1 hx with rfl | hx
        · omega
        · exact h.lt_of_mem x hx

theorem keysOf_snoc (P : List PM) (p : PM) : keysOf (P ++ [p]) = insKey p.key (keysOf P) := by
  simp [keysOf, List.foldl_append]

theorem asc_keysOf (P : List PM) : Asc (keysOf P) := by
  induction P using snoc_induction with
  | h0 => trivial
  | hs P p ih => rw [keysOf_snoc]; exact asc_insKey _ _ ih

theorem mem_keysOf (P : List PM) (k : Nat) : k ∈ keysOf P ↔ ∃ p ∈ P, p.key = k := by
  induction P using snoc_induction with
  | h0 => simp [keysOf]
  | hs P p ih =>
    rw [keysOf_snoc, mem_insKey, ih]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨q, hq, hk⟩)
      · exact ⟨p, Or.inr rfl, h.symm⟩
      · exact ⟨q, Or.inl hq, hk⟩
    · rintro ⟨q, hq | rfl, hk⟩
      · exact Or.inr ⟨q, hq, hk⟩
      · exact Or.inl hk.symm

/-! ## `bucketPush` on group lists -/

theorem grp_snoc_eq (reqs : List Req) (P : List PM) (p : PM) :
    grp reqs (P ++ [p]) p.key = grp reqs P p.key ++ [reqAt reqs p.v] := by
  simp [grp, List.filter_append]

theorem grp_snoc_ne (reqs : List Req) (P : List PM) (p : PM) {k : Nat} (h : k ≠ p.key) :
    grp reqs (P ++ [p]) k = grp reqs P k := by
  simp [grp, List.filter_append, Ne.symm h]

/-- `bucketPush` on an ascending group list: the bucket of `k` gets `q` appended (created if
absent), every other bucket is unchanged. -/
theorem bucketPush_map (k : Nat) (q : Req) (G G' : Nat → List Req)
    (hk : G' k = G k ++ [q]) (hne : ∀ x, x ≠ k → G' x = G x) :
    ∀ ks : List Nat, Asc ks → (k ∉ ks → G k = []) →
      bucketPush k q (ks.map fun x => (x, G x)) = (insKey k ks).map fun x => (x, G' x)
  | [], _, h0 => by
    simp only [List.map_nil, bucketPush, insKey, List.map_cons, hk, h0 (by simp), List.nil_append]
  | k' :: ks, ha, h0 => by
    have hks : ∀ x ∈ ks, k' < x := ha.lt_of_mem
    simp only [List.map_cons, bucketPush, insKey]
    by_cases h1 : k = k'
    · subst h1
      simp only [ite_true, List.map_cons, hk]
      congr 1
      exact List.map_congr_left (fun x hx => by rw [hne x (by have := hks x hx; omega)])
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k < k'
      · rw [if_pos h2, if_pos h2]
        have hk0 : G k = [] := h0 (by
          intro hm; rcases List.mem_cons.1 hm with h | h
          · exact h1 h
          · have := hks k h; omega)
        simp only [List.map_cons, hk, hk0, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and]
        refine ⟨(hne k' (Ne.symm h1)).symm, List.map_congr_left (fun x hx => ?_)⟩
        rw [hne x (by have := hks x hx; omega)]
      · rw [if_neg h2, if_neg h2]
        simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and]
        refine ⟨(hne k' (Ne.symm h1)).symm, bucketPush_map k q G G' hk hne ks ha.tail (fun hm => h0 ?_)⟩
        intro hm'
        rcases List.mem_cons.1 hm' with h | h
        · exact h1 h
        · exact hm h

theorem grp_nil_of_not_mem (reqs : List Req) (P : List PM) (k : Nat) (h : k ∉ keysOf P) :
    grp reqs P k = [] := by
  unfold grp
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro p hp hk
  exact h ((mem_keysOf P k).2 ⟨p, hp, of_decide_eq_true hk⟩)

/-- **The bucket map of a push log is its group list.** -/
theorem bucketsOf_eq_groups (reqs : List Req) (P : List PM) : bucketsOf reqs P = groupsOf reqs P := by
  induction P using snoc_induction with
  | h0 => rfl
  | hs P p ih =>
    have e : bucketsOf reqs (P ++ [p]) = bucketPush p.key (reqAt reqs p.v) (bucketsOf reqs P) := by
      simp [bucketsOf, List.foldl_append]
    rw [e, ih, groupsOf, groupsOf, keysOf_snoc]
    exact bucketPush_map p.key _ (grp reqs P) (grp reqs (P ++ [p])) (grp_snoc_eq reqs P p)
      (fun x hx => grp_snoc_ne reqs P p hx) _ (asc_keysOf P) (grp_nil_of_not_mem reqs P p.key)

/-! ## Popping the largest key -/

theorem asc_ext : ∀ (a b : List Nat), Asc a → Asc b → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).2 (List.mem_cons_self ..)) (by simp)
  | x :: _, [], _, _, h => absurd ((h x).1 (List.mem_cons_self ..)) (by simp)
  | x :: a, y :: b, ha, hb, h => by
    have hxy : x = y := by
      have h1 := (h x).1 (List.mem_cons_self ..)
      have h2 := (h y).2 (List.mem_cons_self ..)
      rcases List.mem_cons.1 h1 with e | h1
      · exact e
      rcases List.mem_cons.1 h2 with e | h2
      · exact e.symm
      have := ha.lt_of_mem y h2
      have := hb.lt_of_mem x h1
      omega
    subst hxy
    rw [asc_ext a b ha.tail hb.tail (fun z => by
      have hz := h z
      constructor
      · intro hza
        have hxz := ha.lt_of_mem z hza
        rcases List.mem_cons.1 (hz.1 (List.mem_cons_of_mem _ hza)) with e | e
        · omega
        · exact e
      · intro hzb
        have hxz := hb.lt_of_mem z hzb
        rcases List.mem_cons.1 (hz.2 (List.mem_cons_of_mem _ hzb)) with e | e
        · omega
        · exact e)]

theorem Asc.sub_of_pair {a : List Nat} (ha : Asc a) (f : Nat → Bool) : Asc (a.filter f) := by
  induction a with
  | nil => trivial
  | cons x a ih =>
    by_cases hf : f x
    · rw [List.filter_cons_of_pos hf]
      exact asc_cons (ih ha.tail) (fun y hy => ha.lt_of_mem y (List.mem_filter.1 hy).1)
    · rw [List.filter_cons_of_neg hf]; exact ih ha.tail

theorem keysOf_filter (P : List PM) (K : Nat) :
    keysOf (P.filter fun p => p.key ≠ K) = (keysOf P).filter fun k => k ≠ K := by
  refine asc_ext _ _ (asc_keysOf _) ((asc_keysOf P).sub_of_pair _) (fun x => ?_)
  rw [mem_keysOf, List.mem_filter, mem_keysOf]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have := List.mem_filter.1 hp
    exact ⟨⟨p, this.1, rfl⟩, this.2⟩
  · rintro ⟨⟨p, hp, rfl⟩, hk⟩
    exact ⟨p, List.mem_filter.2 ⟨hp, hk⟩, rfl⟩

theorem grp_filter (reqs : List Req) (P : List PM) {K k : Nat} (h : k ≠ K) :
    grp reqs (P.filter fun p => p.key ≠ K) k = grp reqs P k := by
  unfold grp
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro p _
  by_cases hk : p.key = k
  · subst hk; simp [h]
  · simp [hk]

/-- An ascending list whose largest element is `K`. -/
theorem asc_split : ∀ (a : List Nat) (K : Nat), Asc a → K ∈ a → (∀ x ∈ a, x ≤ K) →
    a = a.filter (fun k => k ≠ K) ++ [K]
  | [], _, _, h, _ => absurd h (by simp)
  | x :: t, K, ha, hK, hle => by
    by_cases hx : x = K
    · subst hx
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons y t' =>
          have h1 := ha.lt_of_mem y (List.mem_cons_self ..)
          have h2 := hle y (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          omega
      subst ht; simp
    · have hKt : K ∈ t := by
        rcases List.mem_cons.1 hK with e | e
        · exact absurd e.symm hx
        · exact e
      have ih := asc_split t K ha.tail hKt (fun z hz => hle z (List.mem_cons_of_mem _ hz))
      rw [List.filter_cons_of_pos (by simpa using hx), List.cons_append, ← ih]

/-- **Pop.** If `K` is the largest key of a nonempty log, the last bucket is `K`'s group and the
remaining map is the map of the other pushes. -/
theorem groups_pop (reqs : List Req) (P : List PM) (K : Nat) (hK : ∃ p ∈ P, p.key = K)
    (hle : ∀ p ∈ P, p.key ≤ K) :
    (groupsOf reqs P).getLast! = (K, grp reqs P K) ∧
      (groupsOf reqs P).dropLast = groupsOf reqs (P.filter fun p => p.key ≠ K) := by
  have hsplit := asc_split (keysOf P) K (asc_keysOf P) ((mem_keysOf P K).2 hK)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := (mem_keysOf P x).1 hx; exact hle p hp)
  unfold groupsOf
  rw [hsplit, List.map_append]
  simp only [List.map_cons, List.map_nil]
  refine ⟨by simp, ?_⟩
  rw [List.dropLast_concat, keysOf_filter]
  refine List.map_congr_left (fun k hk => ?_)
  rw [grp_filter reqs P (by simpa using (List.mem_filter.1 hk).2)]

end ZkFormal.NearV3.Sched
