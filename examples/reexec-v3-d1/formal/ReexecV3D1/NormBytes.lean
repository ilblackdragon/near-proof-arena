import ReexecV3D1.Canon
import ReexecV3D1.CFTx
import ReexecV3D1.Normal
import ReexecV3D1.NormBytesDefs

/-!
# Bytes of the normal form

Every transition is re-encoded (`encTr`: block hash, `PartialState::TrieValues` tag,
the values, the post-state root), receipt-proof entries are reordered as byte segments of
the original, everything else is the original bytes. `normal_exists`: the normal-form
bytes decode to `normW K R s`, are no longer than the original, and carry the zero
header fields.
-/

namespace ReexecV3D1

open NearSpec NearSpecV3

/-! ## Inversion of the primitive parsers -/

theorem leN_leNat : ∀ (b : Bytes), leN b.length (leNat b) = b
  | [] => rfl
  | x :: xs => by
    simp only [List.length_cons, leN, leNat]
    have h1 : (x.toNat + 256 * leNat xs) % 256 = x.toNat := by have := x.toNat_lt; omega
    have h2 : (x.toNat + 256 * leNat xs) / 256 = leNat xs := by have := x.toNat_lt; omega
    rw [h1, h2, leN_leNat xs]
    simp

theorem leNat_lt : ∀ (b : Bytes), leNat b < 256 ^ b.length
  | [] => by simp [leNat]
  | x :: xs => by
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := leNat_lt xs
    have := x.toNat_lt
    have : 256 * leNat xs + 256 ≤ 256 ^ xs.length * 256 := by
      rw [Nat.mul_comm (256 ^ xs.length)]; omega
    omega

theorem lift_readLE_inv {n : Nat} {w : String} {bs r : Bytes} {v : Nat}
    (h : lift w (readLE n) bs = .ok (v, r)) : bs = leN n v ++ r ∧ v < 256 ^ n := by
  unfold lift at h
  split at h
  · rename_i r0 hr
    cases h
    simp only [readLE, Option.map_eq_some_iff] at hr
    obtain ⟨⟨h', t'⟩, e', he⟩ := hr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨e1, e2⟩ := takeN_split e'
    refine ⟨?_, ?_⟩
    · rw [e1, ← e2, leN_leNat]
    · rw [← e2]; exact leNat_lt h'
  · cases h

theorem pBytes_inv {w : String} {bs v r : Bytes} (h : pBytes w bs = .ok (v, r)) :
    bs = borshBytes v ++ r ∧ v.length < 4294967296 := by
  unfold pBytes lift at h
  split at h
  · rename_i r0 hr
    cases h
    simp only [readBytesT] at hr
    split at hr
    · cases hr
    · rename_i n rest hu
      obtain ⟨e1, e2⟩ := takeT_split' hr
      have hl : lift "" (readLE 4) bs = .ok (n, rest) := by
        unfold lift; simp only [readU32] at hu; rw [hu]
      obtain ⟨b1, b2⟩ := lift_readLE_inv hl
      refine ⟨?_, ?_⟩
      · rw [b1, e1, borshBytes, u32, e2]; simp
      · rw [e2]; simpa using b2
  · cases h
where
  takeT_split' {n : Nat} {bs v r : Bytes} (h : takeT n bs = some (v, r)) : bs = v ++ r ∧ v.length = n := by
    obtain ⟨pre, h1, h2, h3⟩ := takeAcc_split h
    simp at h3; subst h3; exact ⟨h1, h2⟩

theorem pMany_pBytes_inv {w : String} : ∀ (n : Nat) {bs r : Bytes} {vs : List Bytes},
    pMany (pBytes w) n bs = .ok (vs, r) →
      bs = concatAll (vs.map borshBytes) ++ r ∧ vs.length = n ∧ ∀ v ∈ vs, v.length < 4294967296
  | 0, bs, r, vs, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [concatAll]
  | n + 1, bs, r, vs, h => by
    simp only [pMany] at h
    obtain ⟨⟨a, m⟩, h1, h⟩ := bind_ok' h
    obtain ⟨⟨as, m2⟩, h2, h⟩ := bind_ok' h
    dsimp only at h2 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, l1⟩ := pBytes_inv h1
    obtain ⟨e2, l2, l3⟩ := pMany_pBytes_inv n h2
    refine ⟨?_, by simp [l2], ?_⟩
    · rw [e1, e2]; simp [concatAll]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact l1
      · exact l3 v hv

theorem pVec_pBytes_inv {w w' : String} {bs r : Bytes} {vs : List Bytes}
    (h : pVec w (pBytes w') bs = .ok (vs, r)) :
    bs = encList borshBytes vs ++ r ∧ vs.length < 4294967296 ∧ ∀ v ∈ vs, v.length < 4294967296 := by
  unfold pVec at h
  obtain ⟨⟨n, m⟩, h1, h⟩ := bind_ok' h
  obtain ⟨b1, b2⟩ := lift_readLE_inv (n := 4) h1
  obtain ⟨e1, l1, l2⟩ := pMany_pBytes_inv n h
  refine ⟨?_, by rw [l1]; simpa using b2, l2⟩
  rw [b1, e1, encList, l1, u32]; simp

theorem pU8_zero_inv {w : String} {bs r : Bytes} (h : pU8 w bs = .ok (0, r)) : bs = u8 0 ++ r :=
  (lift_readLE_inv (n := 1) h).1

/-- A parsed transition is the canonical encoding of its value. -/
theorem pTransition_inv {bs r : Bytes} {t : Transition} (h : pTransition bs = .ok (t, r)) :
    bs = encTr t ++ r ∧ t.blockHash.length = 32 ∧ t.postStateRoot.length = 32 ∧
      t.values.length < 4294967296 ∧ ∀ v ∈ t.values, v.length < 4294967296 := by
  rw [pTransition_eq] at h
  obtain ⟨⟨bh, m1⟩, h1, h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨hs1, hl1⟩ : bs = bh ++ m1 ∧ bh.length = 32 := by
    unfold pHash lift readHash at h1
    split at h1
    · rename_i r0 hr; cases h1; exact takeN_split hr
    · cases h1
  unfold trTail at h
  obtain ⟨⟨tg, m2⟩, h2, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  · cases h
  rename_i htg
  have : tg = 0 := by simpa using htg
  subst this
  obtain ⟨⟨vals, m3⟩, h3, h⟩ := bind_ok' h
  obtain ⟨⟨post, m4⟩, h4, h⟩ := bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hs4, hl4⟩ : m3 = post ++ m4 ∧ post.length = 32 := by
    unfold pHash lift readHash at h4
    split at h4
    · rename_i r0 hr; cases h4; exact takeN_split hr
    · cases h4
  obtain ⟨hs3, c3, l3⟩ := pVec_pBytes_inv h3
  have hs2 := pU8_zero_inv h2
  refine ⟨?_, hl1, hl4, c3, l3⟩
  rw [hs1, hs2, hs3, hs4]; simp [encTr]

theorem pTransition_enc (t : Transition) (x : Bytes) (h1 : t.blockHash.length = 32)
    (h2 : t.postStateRoot.length = 32) (h3 : t.values.length < 4294967296)
    (h4 : ∀ v ∈ t.values, v.length < 4294967296) :
    pTransition (encTr t ++ x) = .ok (t, x) := by
  rw [pTransition_eq]
  unfold encTr
  rw [List.append_assoc, pHash_any _ _ _ h1, ok_bind]
  dsimp only
  unfold trTail
  rw [show u8 0 ++ (encList borshBytes t.values ++ t.postStateRoot) ++ x =
      u8 0 ++ (encList borshBytes t.values ++ t.postStateRoot ++ x) by simp,
    pU8_ok _ 0 _ (by decide), ok_bind]
  dsimp only
  have hv := pVec_ok "trie values" (pBytes "trie value") borshBytes t.values (t.postStateRoot ++ x) h3
    (fun v hv r => pBytes_ok _ v r (h4 v hv))
  rw [List.append_assoc, hv, ok_bind]
  dsimp only
  rw [pHash_any _ _ _ h2, ok_bind]
  rfl

/-! ## Segments -/

theorem segs_pMany {α : Type} {p : P α} (hp : CF p) : ∀ (n : Nat) {bs r : Bytes} {vs : List α},
    pMany p n bs = .ok (vs, r) →
    ∃ ps : List (α × Bytes), segs p n bs = .ok (ps, r) ∧ ps.map Prod.fst = vs ∧
      bs = concatAll (ps.map Prod.snd) ++ r ∧ ∀ q ∈ ps, ∀ x, p (q.2 ++ x) = .ok (q.1, x)
  | 0, bs, r, vs, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | n + 1, bs, r, vs, h => by
    simp only [pMany] at h
    obtain ⟨⟨a, m⟩, h1, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨as, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨pre, e1, k1⟩ := hp bs a m h1
    obtain ⟨ps, hs, hm, he, hk⟩ := segs_pMany hp n h2
    refine ⟨(a, pre) :: ps, ?_, by simp [hm], by rw [e1, he]; simp [concatAll], ?_⟩
    · simp only [segs]
      rw [h1, ok_bind]
      dsimp only
      rw [hs, ok_bind, e1, consumed_app]
      rfl
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact k1
      · exact hk q hq

theorem segs_concat {α : Type} {p : P α} : ∀ (ps : List (α × Bytes)) (x : Bytes),
    (∀ q ∈ ps, ∀ x, p (q.2 ++ x) = .ok (q.1, x)) →
    segs p ps.length (concatAll (ps.map Prod.snd) ++ x) = .ok (ps, x)
  | [], x, _ => rfl
  | (a, sg) :: ps, x, h => by
    simp only [segs, List.length_cons, List.map_cons, concatAll, List.append_assoc]
    rw [h (a, sg) List.mem_cons_self, ok_bind]
    dsimp only
    rw [segs_concat ps x (fun q hq => h q (List.mem_cons_of_mem _ hq)), ok_bind, consumed_app]
    rfl

theorem pMany_concat {α : Type} {p : P α} : ∀ (ps : List (α × Bytes)) (x : Bytes),
    (∀ q ∈ ps, ∀ x, p (q.2 ++ x) = .ok (q.1, x)) →
    pMany p ps.length (concatAll (ps.map Prod.snd) ++ x) = .ok (ps.map Prod.fst, x)
  | [], x, _ => rfl
  | (a, sg) :: ps, x, h => by
    simp only [pMany, List.length_cons, List.map_cons, concatAll, List.append_assoc]
    rw [h (a, sg) List.mem_cons_self, ok_bind]
    dsimp only
    rw [pMany_concat ps x (fun q hq => h q (List.mem_cons_of_mem _ hq)), ok_bind]
    rfl

/-! ## Sorting and deduplication commute with `map` -/

theorem insertBy_map {α β : Type} (f : α → β) (le : β → β → Bool) (x : α) :
    ∀ l : List α, (insertBy (fun a b => le (f a) (f b)) x l).map f = insertBy le (f x) (l.map f)
  | [] => rfl
  | y :: ys => by
    simp only [insertBy, List.map_cons]
    split <;> simp [insertBy_map f le x ys]

theorem isort_map {α β : Type} (f : α → β) (le : β → β → Bool) :
    ∀ l : List α, (isort (fun a b => le (f a) (f b)) l).map f = isort le (l.map f)
  | [] => rfl
  | x :: xs => by
    simp only [isort, List.map_cons]
    rw [insertBy_map, isort_map f le xs]

theorem dedupLastBy_map {α β : Type} (f : α → β) (k : β → Bytes) :
    ∀ l : List α, (dedupLastBy (fun a => k (f a)) l).map f = dedupLastBy k (l.map f)
  | [] => rfl
  | e :: es => by
    have ha : (es.map f).any (fun x => k x == k (f e)) = es.any (fun x => k (f x) == k (f e)) := by
      rw [List.any_map]; rfl
    simp only [List.map_cons]
    unfold dedupLastBy
    rw [ha]
    split
    · exact dedupLastBy_map f k es
    · simp only [List.map_cons]; rw [dedupLastBy_map f k es]

theorem normPairs_map (ps : List (ProofEntry × Bytes)) :
    (normPairs ps).map Prod.fst = normEntries (ps.map Prod.fst) := by
  unfold normPairs normEntries
  have h1 := isort_map Prod.fst (fun a b : ProofEntry => bytesLe a.key b.key)
    (dedupLastBy (fun x : ProofEntry × Bytes => x.fst.key) ps)
  have h2 := dedupLastBy_map Prod.fst (fun e : ProofEntry => e.key) ps
  exact h1.trans (congrArg _ h2)

theorem normPairs_idem (ps : List (ProofEntry × Bytes)) : normPairs (normPairs ps) = normPairs ps := by
  unfold normPairs
  rw [dedupLastBy_of_pairwise _ _ ((isort_perm _ _).symm.pairwise (dedupLastBy_pairwise _ ps)
    (fun h => fun h' => h h'.symm))]
  exact isort_idem _ (fun a b => bytesLe_total a.1.key b.1.key) _

theorem mem_normPairs {ps : List (ProofEntry × Bytes)} {q : ProofEntry × Bytes}
    (h : q ∈ normPairs ps) : q ∈ ps := by
  unfold normPairs at h
  rw [mem_isort] at h
  exact (dedupLastBy_sublist _ ps).subset h

/-! ## Lengths -/

theorem concatAll_length_sublist {α : Type} {l l' : List (α × Bytes)} (h : l.Sublist l') :
    (concatAll (l.map Prod.snd)).length ≤ (concatAll (l'.map Prod.snd)).length := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => simp only [List.map_cons, concatAll, List.length_append]; omega
  | cons_cons a _ ih => simp only [List.map_cons, concatAll, List.length_append]; omega

theorem concatAll_length_perm {α : Type} {l l' : List (α × Bytes)} (h : l.Perm l') :
    (concatAll (l.map Prod.snd)).length = (concatAll (l'.map Prod.snd)).length := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.map_cons, concatAll, List.length_append]; omega
  | swap a b l => simp only [List.map_cons, concatAll, List.length_append]; omega
  | trans _ _ ih1 ih2 => omega

theorem normPairs_length (ps : List (ProofEntry × Bytes)) :
    (concatAll ((normPairs ps).map Prod.snd)).length ≤ (concatAll (ps.map Prod.snd)).length ∧
      (normPairs ps).length ≤ ps.length := by
  unfold normPairs
  constructor
  · rw [concatAll_length_perm (isort_perm _ _)]
    exact concatAll_length_sublist (dedupLastBy_sublist _ ps)
  · rw [(isort_perm _ _).length_eq]
    exact (dedupLastBy_sublist _ ps).length_le

theorem concatAll_borsh_length : ∀ (l : List Bytes),
    (concatAll (l.map borshBytes)).length = 4 * l.length + (l.map List.length).foldl (· + ·) 0
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, concatAll, List.length_append, borshBytes, u32, leN_length,
      List.foldl_cons, List.length_cons]
    rw [concatAll_borsh_length vs, foldl_add_shift _ (0 + v.length)]
    omega

theorem encTr_length (t : Transition) :
    (encTr t).length = t.blockHash.length + 1 + 4 + 4 * t.values.length +
      (t.values.map List.length).foldl (· + ·) 0 + t.postStateRoot.length := by
  simp only [encTr, encList, List.length_append, u8, u32, leN_length, concatAll_borsh_length]
  omega

theorem normVals_nodup (vals q : List Bytes) : (normVals vals q).Nodup := by
  unfold normVals
  exact (isort_perm _ _).symm.nodup (by
    have := dedupLastBy_pairwise id (q.filterMap (storeGet (mkStore vals)))
    exact this.imp (fun h => h))

theorem mem_normVals {vals q : List Bytes} {x : Bytes} (hx : x ∈ normVals vals q) : x ∈ vals := by
  unfold normVals at hx
  rw [mem_isort] at hx
  have := mem_dedupLastBy id _ x hx
  rw [List.mem_filterMap] at this
  obtain ⟨y, -, hy⟩ := this
  exact (storeGet_some_hash hy).2

theorem normVals_length (vals q : List Bytes) : (normVals vals q).length ≤ vals.length :=
  List.Nodup.length_le_of_subset (normVals_nodup vals q) (fun _ hx => mem_normVals hx)

/-- Well-formed transitions (what `pTransition` guarantees). -/
def TrWf (t : Transition) : Prop :=
  t.blockHash.length = 32 ∧ t.postStateRoot.length = 32 ∧ t.values.length < 4294967296 ∧
    ∀ v ∈ t.values, v.length < 4294967296

theorem zeroHash_length : zeroHash.length = 32 := by simp [zeroHash]

theorem trWf_norm {t t' : Transition} (h : TrWf t) (hb : t'.blockHash = zeroHash)
    (hp : t'.postStateRoot = t.postStateRoot) (hv : ∃ q, t'.values = normVals t.values q) :
    TrWf t' ∧ (encTr t').length ≤ (encTr t).length := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨q, hq⟩ := hv
  have l1 := normVals_length t.values q
  have l2 := sum_normVals_le t.values q
  refine ⟨⟨by rw [hb, zeroHash_length], by rw [hp, h2], by rw [hq]; omega,
    fun v hv => h4 v (mem_normVals (hq ▸ hv))⟩, ?_⟩
  rw [encTr_length, encTr_length, hb, hp, hq, zeroHash_length, h1]
  omega

theorem normMain_wf (K : List (List Nat)) (R : Bytes) {t : Transition} (h : TrWf t) :
    TrWf (normMain K R t) ∧ (encTr (normMain K R t)).length ≤ (encTr t).length :=
  trWf_norm h rfl rfl ⟨_, rfl⟩

theorem normT_wf (r : Bytes) {t : Transition} (h : TrWf t) :
    TrWf (normT r t) ∧ (encTr (normT r t)).length ≤ (encTr t).length :=
  trWf_norm h rfl rfl ⟨_, rfl⟩

theorem normImpl_wf : ∀ (r : Bytes) (ts : List Transition), (∀ t ∈ ts, TrWf t) →
    (∀ t ∈ normImpl r ts, TrWf t) ∧
      (concatAll ((normImpl r ts).map encTr)).length ≤ (concatAll (ts.map encTr)).length
  | _, [], _ => ⟨by simp [normImpl], Nat.le_refl _⟩
  | r, t :: ts, h => by
    obtain ⟨w1, l1⟩ := normT_wf r (h t List.mem_cons_self)
    obtain ⟨w2, l2⟩ := normImpl_wf t.postStateRoot ts (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [normImpl, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact w1
      · exact w2 x hx
    · simp only [normImpl, List.map_cons, concatAll, List.length_append]
      omega

theorem pTransition_wf {bs r : Bytes} {t : Transition} (h : pTransition bs = .ok (t, r)) : TrWf t :=
  let ⟨_, a, b, c, d⟩ := pTransition_inv h; ⟨a, b, c, d⟩

theorem pTransition_encW (t : Transition) (x : Bytes) (h : TrWf t) :
    pTransition (encTr t ++ x) = .ok (t, x) :=
  pTransition_enc t x h.1 h.2.1 h.2.2.1 h.2.2.2

theorem segs_enc {α : Type} {f : α → Bytes} : ∀ (ps : List (α × Bytes)), (∀ q ∈ ps, q.2 = f q.1) →
    ps.map Prod.snd = (ps.map Prod.fst).map f
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.map_cons, h q List.mem_cons_self,
      segs_enc ps (fun q' hq => h q' (List.mem_cons_of_mem _ hq))]

/-- Implicit transitions: their bytes are their encodings. -/
theorem pVecTr_inv {w : String} {bs r : Bytes} {ts : List Transition}
    (h : pVec w pTransition bs = .ok (ts, r)) :
    bs = encList encTr ts ++ r ∧ ts.length < 4294967296 ∧ ∀ t ∈ ts, TrWf t := by
  unfold pVec at h
  obtain ⟨⟨n, m⟩, h1, h⟩ := bind_ok' h
  obtain ⟨b1, b2⟩ := lift_readLE_inv (n := 4) h1
  obtain ⟨ps, -, hm, he, hk⟩ := segs_pMany cf_pTransition n h
  have hq : ∀ q ∈ ps, q.2 = encTr q.1 := by
    intro q hq
    have := (pTransition_inv (by rw [hk q hq []] : pTransition (q.2 ++ []) = .ok (q.1, []))).1
    simpa using this
  have hn : n = ts.length := (pMany_length h).symm
  refine ⟨?_, by rw [← hn]; simpa using b2, fun t ht => ?_⟩
  · rw [b1, he, segs_enc ps hq, hm, encList, u32, hn]; simp
  · rw [← hm] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact pTransition_wf (hk q hq [])
where
  pMany_length {α : Type} {p : P α} : ∀ {n : Nat} {bs r : Bytes} {vs : List α},
      pMany p n bs = .ok (vs, r) → vs.length = n
    | 0, _, _, _, h => by
      simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
    | n + 1, _, _, _, h => by
      simp only [pMany] at h
      obtain ⟨⟨a, m⟩, -, h⟩ := bind_ok' h
      dsimp only at h
      obtain ⟨⟨as, m2⟩, h2, h⟩ := bind_ok' h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [pMany_length h2]

/-- **The normaliser on bytes.** For a decodable state witness `sw` (any keys `K` and
root `R`), `normSW` succeeds; its output decodes to the normal form `normW K R s`, is no
longer than `sw`, and is a fixed point of `normSW`. -/
theorem normSW_spec {sw : Bytes} {s : StateWitnessD1} (hs : decodeStateWitnessD1 sw = .ok s)
    (K : List (List Nat)) (R : Bytes) :
    ∃ c, normSW K R sw = .ok c ∧ decodeStateWitnessD1 c = .ok (normW K R s) ∧
      c.length ≤ sw.length ∧ normSW K R c = .ok c := by
  unfold decodeStateWitnessD1 at hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hmax
  obtain ⟨⟨t, b1⟩, h1, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i ht
  have ht1 : t = 1 := by simpa using ht
  subst ht1
  obtain ⟨⟨eid, b2⟩, h2, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨⟨ib, ci⟩, b3⟩, h3, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨main, b4⟩, h4, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨entries, b5⟩, h5, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨arh, b6⟩, h6, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨txs, b7⟩, h7, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨impl, b8⟩, h8, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨ntxs, b9⟩, h9, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hemp
  have hb9 : b9 = [] := by simpa using hemp
  subst hb9
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  subst hs
  -- the header
  have h3' := h3
  unfold pChunkHeader at h3'
  obtain ⟨⟨tg, m1⟩, g1, h3'⟩ := bind_ok' h3'
  dsimp only at h3'
  split at h3'
  · cases h3'
  rename_i htg
  have htg2 : tg = 2 := by simpa using htg
  subst htg2
  obtain ⟨⟨ci', m2⟩, g2, h3'⟩ := bind_ok' h3'
  dsimp only at h3'
  obtain ⟨⟨hv, m3⟩, g3, h3'⟩ := bind_ok' h3'
  dsimp only at h3'
  obtain ⟨⟨sg, m4⟩, g4, h3'⟩ := bind_ok' h3'
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3'
  obtain ⟨⟨hib, hci⟩, hr⟩ := h3'
  subst m4; subst ci'
  obtain ⟨A1, e1, k1⟩ := cfk (cf_pU8 _) h1
  obtain ⟨A2, e2, k2⟩ := cfk (cf_pHash _) h2
  obtain ⟨T, eT, kT⟩ := cfk (cf_pU8 _) g1
  obtain ⟨I, eI, kI⟩ := cfk cf_pChunkInner g2
  obtain ⟨H, eH, hH8⟩ := pU64_split g3
  obtain ⟨S, eS, hS65⟩ := pSignature_split g4
  have hib' : I = ib := by rw [← hib, eI, consumed_app]
  subst hib'
  have kH : ∀ x, pChunkHeader (T ++ (I ++ (zeros8 ++ (sig0 ++ x)))) = .ok ((I, ci), x) := by
    intro x
    unfold pChunkHeader
    rw [kT]
    simp only [ok_bind]
    show (if ((2 : Nat) != 2) = true then _ else _) = _
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [kI]
    simp only [ok_bind]
    rw [consumed_app, pU64_zeros8, ok_bind, pSignature_sig0, ok_bind]
    rfl
  -- main transition, entries, tail
  obtain ⟨e4, hmw⟩ : b3 = encTr main ++ b4 ∧ TrWf main :=
    ⟨(pTransition_inv h4).1, pTransition_wf h4⟩
  have h5' := h5
  unfold pVec at h5'
  obtain ⟨⟨n, m5⟩, g5, h5'⟩ := bind_ok' h5'
  obtain ⟨e5a, hn32⟩ := lift_readLE_inv (n := 4) g5
  obtain ⟨ps, hseg, hmap, e5b, hk5⟩ := segs_pMany cf_pEntry n h5'
  have hnl : n = ps.length := by
    rw [← (pVecTr_inv.pMany_length h5'), ← hmap, List.length_map]
  obtain ⟨AA, e6, k6⟩ := cfk (cf_pHash _) h6
  obtain ⟨AN, e7, k7⟩ := cfk (cf_pVec _ cf_pTxD1) h7
  obtain ⟨e8, himpl32, himplw⟩ := pVecTr_inv h8
  -- the normal form
  obtain ⟨hmainNw, hmainNl⟩ := normMain_wf K R hmw
  obtain ⟨himplNw, himplNl⟩ := normImpl_wf main.postStateRoot impl himplw
  obtain ⟨hesl, hesn⟩ := normPairs_length ps
  have hes32 : (normPairs ps).length < 4294967296 := by
    have : ps.length < 256 ^ 4 := hnl ▸ hn32
    omega
  have hesk : ∀ q ∈ normPairs ps, ∀ x, pEntry (q.2 ++ x) = .ok (q.1, x) :=
    fun q hq => hk5 q (mem_normPairs hq)
  obtain ⟨c, hc⟩ : ∃ c, c = A1 ++ (A2 ++ (T ++ (I ++ (zeros8 ++ (sig0 ++ (encTr (normMain K R main) ++
    (u32 (normPairs ps).length ++ (concatAll ((normPairs ps).map Prod.snd) ++ (AA ++ (AN ++
    (encList encTr (normImpl main.postStateRoot impl) ++ b8))))))))))) := ⟨_, rfl⟩
  have hsw : sw = A1 ++ (A2 ++ (T ++ (I ++ (H ++ (S ++ (encTr main ++
      (u32 n ++ (concatAll (ps.map Prod.snd) ++ (AA ++ (AN ++
      (encList encTr impl ++ b8))))))))))) := by
    rw [e1, e2, eT, eI, eH, eS, e4, e5a, e5b, e6, e7, e8, u32]; (try simp)
  have hlen : c.length ≤ sw.length := by
    rw [hsw]
    rw [hc]
    simp only [List.length_append, encList, u32, leN_length, zeros8, sig0, List.length_replicate,
      List.length_cons, hH8, normImpl_length]
    omega
  have hrun : normSW K R sw = .ok c := by
    unfold normSW
    rw [h1, ok_bind]; dsimp only
    rw [h2, ok_bind]; dsimp only
    rw [g1, ok_bind]; dsimp only
    rw [g2, ok_bind]; dsimp only
    rw [g3, ok_bind]; dsimp only
    rw [g4, ok_bind]; dsimp only
    rw [h4, ok_bind]; dsimp only
    rw [g5, ok_bind]; dsimp only
    rw [hseg, ok_bind]; dsimp only
    rw [h6, ok_bind]; dsimp only
    rw [h7, ok_bind]; dsimp only
    rw [h8, ok_bind]; dsimp only
    have c1 : consumed sw m2 = A1 ++ (A2 ++ (T ++ I)) := by
      rw [e1, e2, eT, eI,
        show A1 ++ (A2 ++ (T ++ (I ++ m2))) = (A1 ++ (A2 ++ (T ++ I))) ++ m2 by simp, consumed_app]
    have c2 : consumed b5 b7 = AA ++ AN := by
      rw [e6, e7, show AA ++ (AN ++ b7) = (AA ++ AN) ++ b7 by simp, consumed_app]
    rw [c1, c2, hc]
    simp only [List.append_assoc]
    rfl
  have hpv : ∀ X, pVec "source_receipt_proofs" pEntry (u32 (normPairs ps).length ++
      (concatAll ((normPairs ps).map Prod.snd) ++ X)) = .ok (normEntries entries, X) := by
    intro X
    unfold pVec
    rw [pU32_ok _ _ _ hes32, ok_bind]
    dsimp only
    rw [pMany_concat _ _ hesk, normPairs_map, hmap]
  have hiv : ∀ X, pVec "implicit_transitions" pTransition
      (encList encTr (normImpl main.postStateRoot impl) ++ X) =
        .ok (normImpl main.postStateRoot impl, X) := fun X =>
    pVec_ok "implicit_transitions" pTransition encTr _ X (by rw [normImpl_length]; exact himpl32)
      (fun x hx r => pTransition_encW x r (himplNw x hx))
  refine ⟨c, hrun, ?_, hlen, ?_⟩
  · have hmax' : ¬ lenT c > MAX_WITNESS := by
      rw [lenT_eq'] at hmax ⊢; omega
    unfold decodeStateWitnessD1
    dsimp only
    rw [if_neg hmax', hc]
    rw [k1, ok_bind]
    dsimp only
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [k2, ok_bind]
    dsimp only
    rw [kH, ok_bind]
    dsimp only
    rw [pTransition_encW _ _ hmainNw, ok_bind]
    dsimp only
    rw [hpv, ok_bind]
    dsimp only
    rw [k6, ok_bind]
    dsimp only
    rw [k7, ok_bind]
    dsimp only
    rw [hiv, ok_bind]
    dsimp only
    rw [h9, ok_bind]
    dsimp only
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  · subst hc
    have cs4 : ∀ (a b d e y : Bytes), consumed (a ++ (b ++ (d ++ (e ++ y)))) y = a ++ (b ++ (d ++ e)) :=
      fun a b d e y => by rw [show a ++ (b ++ (d ++ (e ++ y))) = (a ++ (b ++ (d ++ e))) ++ y by simp,
        consumed_app]
    have cs2 : ∀ (a b y : Bytes), consumed (a ++ (b ++ y)) y = a ++ b :=
      fun a b y => by rw [show a ++ (b ++ y) = (a ++ b) ++ y by simp, consumed_app]
    unfold normSW
    rw [k1, ok_bind]; dsimp only
    rw [k2, ok_bind]; dsimp only
    rw [kT, ok_bind]; dsimp only
    rw [kI, ok_bind]; dsimp only
    rw [pU64_zeros8, ok_bind]; dsimp only
    rw [pSignature_sig0, ok_bind]; dsimp only
    rw [pTransition_encW _ _ hmainNw, ok_bind]; dsimp only
    rw [pU32_ok _ _ _ hes32, ok_bind]; dsimp only
    rw [segs_concat _ _ hesk, ok_bind]; dsimp only
    rw [k6, ok_bind]; dsimp only
    rw [k7, ok_bind]; dsimp only
    rw [hiv, ok_bind]; dsimp only
    rw [normPairs_idem, normMain_post, normMain_idem, normImpl_idem, cs4, cs2]
    simp only [List.append_assoc]
    rfl

end ReexecV3D1
