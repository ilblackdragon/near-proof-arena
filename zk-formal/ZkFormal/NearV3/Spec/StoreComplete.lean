import ZkFormal.NearV3.Spec.Occs

/-!
# ZkFormal.NearV3.Spec.StoreComplete — hash-consed records for any accepted store

Completeness direction of `StoreBuildStmt` (V3-D0-DESIGN §3.3, §6.2).  From the
relation's partial trie `T = partialTrie ws root keys` we build **one record per
distinct revealed node digest** (merging what the different occurrences of a
digest reveal) and one value record per distinct revealed value, ids sorted by
a rank so that children have larger ids (`cid > N`).

Hypothesis `StoreDag T` (the D0 condition proposed as **A6** in
`docs/zk-formal/STATUS-V3-STORE.md`):
* the merged digest graph of `T` is acyclic, given as a rank function that
  increases from every revealed node to every revealed child digest;
* no revealed value has the digest of a revealed node.
Both hold on every witness unless SHA-256 has a cycle / a value-node digest
coincidence among the revealed entries; without them a strict-`uniq` AIR
cannot be complete (§ "Why A6" in the status note).

`storeComplete`: the records are a `RootedDag` with pairwise-distinct entry
digests (`DigestsDistinct`, hence `HashFunctional`), their root digest is
`root`, every read key is revealed within fuel and looks up exactly as in the
relation's trie, and the store they denote is no larger than `ws`
(`storeBytes ≤ Σ |ws|`).
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-! ## Lists -/

def dedup : List Bytes → List Bytes
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup : ∀ {l : List Bytes} {x : Bytes}, x ∈ dedup l ↔ x ∈ l
  | [], _ => by simp [dedup]
  | y :: ys, x => by
    simp only [dedup]
    split
    · rename_i h
      rw [mem_dedup]; simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h'); · exact mem_dedup.1 h
        exact h'
    · simp [mem_dedup]

theorem nodup_dedup : ∀ (l : List Bytes), (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: ys => by
    simp only [dedup]
    split
    · exact nodup_dedup ys
    · rename_i h; exact List.nodup_cons.2 ⟨h, nodup_dedup ys⟩

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, hn, hi => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy he => hn.1 ?_, nodup_map_of_inj f xs hn.2 (fun a ha b hb => hi a (by simp [ha]) b (by simp [hb]))⟩
    have := hi y (by simp [hy]) x (by simp) he
    subst this; exact hy

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup → l.Nodup
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    exact List.nodup_cons.2 ⟨fun hx => h.1 x hx rfl, nodup_of_map f xs h.2⟩

theorem sum_erase {x : Bytes} : ∀ {ws : List Bytes}, x ∈ ws →
    (ws.map List.length).sum = x.length + ((ws.erase x).map List.length).sum
  | [], h => by simp at h
  | y :: ys, h => by
    by_cases e : y = x
    · subst e; simp
    · have hx : x ∈ ys := by simpa [List.mem_cons, Ne.symm e] using h
      simp only [List.map_cons, List.sum_cons, List.erase_cons, beq_iff_eq, e, ↓reduceIte]
      rw [sum_erase hx]; omega

theorem sum_le_of_nodup_sub : ∀ (l ws : List Bytes), l.Nodup → (∀ x ∈ l, x ∈ ws) →
    (l.map List.length).sum ≤ (ws.map List.length).sum
  | [], _, _, _ => by simp
  | x :: xs, ws, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ ws := hs x (by simp)
    rw [sum_erase hx]
    have ih := sum_le_of_nodup_sub xs (ws.erase x) hn.2 (fun y hy => by
      have hyx : y ≠ x := fun e => hn.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hyx).2 (hs y (by simp [hy])))
    simp only [List.map_cons, List.sum_cons]; omega

/-! ## The construction -/

section Construction

variable (T : PTrie) (rk : Bytes → Nat) (τ : Nat)

/-- Distinct revealed node digests. -/
def digs : List Bytes := dedup ((occs T).map PTrie.hashOf)

/-- Digests sorted by rank: the record ids. -/
def Ds : List Bytes := (digs T).mergeSort (fun a b => decide (rk a ≤ rk b))

/-- Distinct revealed values: the value records. -/
def Vs : List Bytes := dedup (valsOf T)

def idx (d : Bytes) : Nat := (Ds T rk).idxOf d
def vidx (v : Bytes) : Nat := (Vs T).idxOf v

/-- The first occurrence of a digest. -/
def canon (d : Bytes) : PTrie := ((occs T).find? (fun o => o.hashOf == d)).getD (.hash d)

def kid3 (c : PTrie) : Kid3 :=
  if c.hashOf ∈ digs T then .node (idx T rk c.hashOf) else .hash c.hashOf

def vslot3 (sl : Slot) : VSlot3 :=
  match (Vs T).find? (fun v => sha256 v == slotHash sl && v.length == sl.len) with
  | some v => .val (vidx T v)
  | none => .ref sl.len (slotHash sl)

def kids3 : Kids → List Kid3
  | .nil => []
  | .none r => .none :: kids3 r
  | .some c r => kid3 T rk c :: kids3 r

def rec3 : PTrie → Rec3
  | .leaf k sl m => .leaf k (vslot3 T sl) m
  | .ext k c m => .ext k (kid3 T rk c) m
  | .branch bv cs m => .branch (bv.map (vslot3 T)) (kids3 T rk cs) m
  | .hash _ => .leaf [] (.ref 0 []) 0

def nsOf : List NodeRec3 := (Ds T rk).map fun d => ⟨τ, rec3 T rk (canon T d)⟩
def vsOf : List ValRec3 := (Vs T).map fun v => ⟨τ, v⟩

end Construction

/-- **A6**: the merged revealed digest graph is acyclic (a rank increases along
every revealed parent → revealed child digest) and no revealed value has the
digest of a revealed node. -/
def StoreDag (T : PTrie) (rk : Bytes → Nat) : Prop :=
  (∀ o ∈ occs T, ∀ c ∈ children o, c.hashOf ∈ digs T → rk o.hashOf < rk c.hashOf) ∧
  (∀ v ∈ valsOf T, sha256 v ∉ digs T)

section Proofs

variable {T : PTrie} {rk : Bytes → Nat} {τ : Nat} {s : Store}

theorem mem_digs {d : Bytes} : d ∈ digs T ↔ ∃ o ∈ occs T, o.hashOf = d := by
  simp [digs, mem_dedup]

theorem mem_Ds {d : Bytes} : d ∈ Ds T rk ↔ d ∈ digs T := by simp [Ds]

theorem nodup_Ds : (Ds T rk).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (nodup_dedup _)

theorem Ds_length : (nsOf T rk τ).length = (Ds T rk).length := by simp [nsOf]

theorem idx_lt {d : Bytes} (h : d ∈ digs T) : idx T rk d < (Ds T rk).length :=
  List.idxOf_lt_length_of_mem (mem_Ds.2 h)

theorem Ds_idx {d : Bytes} (h : d ∈ digs T) : (Ds T rk)[idx T rk d]? = some d := by
  rw [List.getElem?_eq_getElem (idx_lt h)]
  exact congrArg some (List.getElem_idxOf (idx_lt h))

theorem idx_get {n : Nat} {d : Bytes} (h : (Ds T rk)[n]? = some d) : idx T rk d = n := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact nodup_Ds.idxOf_getElem n hn

theorem ns_get {n : Nat} : (nsOf T rk τ)[n]? = ((Ds T rk)[n]?).map fun d => ⟨τ, rec3 T rk (canon T d)⟩ := by
  simp [nsOf]

theorem idx_order {d e : Bytes} (hd : d ∈ digs T) (he : e ∈ digs T) (h : rk d < rk e) :
    idx T rk d < idx T rk e := by
  have hp : (Ds T rk).Pairwise (fun a b => decide (rk a ≤ rk b) = true) :=
    List.pairwise_mergeSort (le := fun a b => decide (rk a ≤ rk b))
      (fun a b c hab hbc => by simp at hab hbc ⊢; omega) (fun a b => by simp; omega) (digs T)
  rw [List.pairwise_iff_getElem] at hp
  have h1 := idx_lt (rk := rk) hd
  have h2 := idx_lt (rk := rk) he
  have g1 : (Ds T rk)[idx T rk d] = d := List.getElem_idxOf h1
  have g2 : (Ds T rk)[idx T rk e] = e := List.getElem_idxOf h2
  rcases Nat.lt_trichotomy (idx T rk d) (idx T rk e) with hlt | heq | hgt
  · exact hlt
  · exfalso
    have a1 := Ds_idx (rk := rk) hd
    have a2 := Ds_idx (rk := rk) he
    rw [heq, a2] at a1
    have : d = e := (Option.some.inj a1).symm
    subst this; omega
  · exfalso
    have := hp _ _ h2 h1 hgt
    rw [g1, g2] at this
    simp at this; omega

theorem canon_spec {d : Bytes} (h : d ∈ digs T) : canon T d ∈ occs T ∧ (canon T d).hashOf = d := by
  unfold canon
  cases hf : (occs T).find? (fun o => o.hashOf == d) with
  | none =>
    obtain ⟨o, ho, rfl⟩ := mem_digs.1 h
    have := List.find?_eq_none.1 hf o ho; simp at this
  | some o =>
    simp only [Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem mem_Vs {v : Bytes} : v ∈ Vs T ↔ v ∈ valsOf T := mem_dedup

theorem vs_get {v : Bytes} (h : v ∈ Vs T) : (vsOf T τ)[vidx T v]? = some ⟨τ, v⟩ := by
  have hl := List.idxOf_lt_length_of_mem h
  simp only [vsOf, vidx, List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem_idxOf hl,
    Option.map_some]

theorem valOf_vidx {v : Bytes} (h : v ∈ Vs T) : valOf (vsOf T τ) (vidx T v) = v := by
  simp [valOf, vs_get h]

/-! ### Hypothesis bundle -/

structure CHyp (s : Store) (T : PTrie) (rk : Bytes → Nat) : Prop where
  wf : T.wf = true
  stored : Stored s T
  node : isNode T = true
  dag : StoreDag T rk

theorem CHyp.occ_found (H : CHyp s T rk) {o : PTrie} (ho : o ∈ occs T) : Found s (nodeEnc o) :=
  stored_found (occs_stored s T H.stored o ho) (occs_isNode T o ho)

theorem CHyp.val_found (H : CHyp s T rk) {v : Bytes} (hv : v ∈ valsOf T) : Found s v := by
  obtain ⟨o, ho, hv'⟩ := List.mem_flatMap.1 hv
  exact stored_ownVals (occs_stored s T H.stored o ho) v hv'

/-- Two occurrences with the same digest have the same preimage. -/
theorem CHyp.enc_eq (H : CHyp s T rk) {o o' : PTrie} (ho : o ∈ occs T) (ho' : o' ∈ occs T)
    (h : o.hashOf = o'.hashOf) : nodeEnc o = nodeEnc o' := by
  apply found_inj (H.occ_found ho) (H.occ_found ho')
  rw [← hashOf_eq_enc o (occs_isNode T o ho), ← hashOf_eq_enc o' (occs_isNode T o' ho'), h]

theorem CHyp.val_inj (H : CHyp s T rk) {v v' : Bytes} (hv : v ∈ valsOf T) (hv' : v' ∈ valsOf T)
    (h : sha256 v = sha256 v') : v = v' :=
  found_inj (H.val_found hv) (H.val_found hv') h

/-! ### Value slots -/

theorem vslot3_spec (H : CHyp s T rk) (sl : Slot) (hok : slotOk sl = true) :
    (slot3 (vsOf T τ) (vslot3 T sl)).valueRef = sl.valueRef ∧ (vslot3 T sl).wf (vsOf T τ) ∧
    ∀ sl', sl'.len = sl.len → slotHash sl' = slotHash sl → (∀ v, sl' = .val v → v ∈ valsOf T) →
      SlotRefines sl' (slot3 (vsOf T τ) (vslot3 T sl)) := by
  unfold vslot3
  cases hf : (Vs T).find? (fun v => sha256 v == slotHash sl && v.length == sl.len) with
  | some v =>
    have hv : v ∈ Vs T := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hsh, hln⟩ := hp
    simp only [slot3, valOf_vidx hv]
    refine ⟨?_, ?_, ?_⟩
    · rw [valueRef_eq sl]; simp [Slot.valueRef, hsh, hln]
    · simp only [VSlot3.wf, valOf_vidx hv, hln]; exact slot_len_lt sl hok
    · intro sl' hl hh hv'
      cases sl' with
      | val v' =>
        have hv'' := hv' v' rfl
        have hh' : sha256 v' = slotHash sl := hh
        have : v' = v := H.val_inj hv'' (mem_Vs.1 hv) (by rw [hh', hsh])
        subst this; exact Or.inl rfl
      | ref len h =>
        refine Or.inr ⟨v, ?_, rfl⟩
        have hl' : len = sl.len := hl
        have hh' : h = slotHash sl := hh
        rw [hl', hh', ← hln, ← hsh]
  | none =>
    simp only [slot3]
    refine ⟨by rw [valueRef_eq sl]; rfl, ⟨slot_len_lt sl hok, slotHash_len sl hok⟩, ?_⟩
    intro sl' hl hh hv'
    cases sl' with
    | val v' =>
      exfalso
      have := List.find?_eq_none.1 hf v' (mem_Vs.2 (hv' v' rfl))
      have hl' : v'.length = sl.len := hl
      have hh' : sha256 v' = slotHash sl := hh
      simp [hh', hl'] at this
    | ref len h =>
      have hl' : len = sl.len := hl
      have hh' : h = slotHash sl := hh
      subst hl' hh'; exact Or.inl rfl

/-! ### Records -/

theorem kid3_cases (c : PTrie) :
    (c.hashOf ∈ digs T ∧ kid3 T rk c = .node (idx T rk c.hashOf)) ∨
    (c.hashOf ∉ digs T ∧ kid3 T rk c = .hash c.hashOf) := by
  unfold kid3; split
  · exact Or.inl ⟨by assumption, rfl⟩
  · exact Or.inr ⟨by assumption, rfl⟩

theorem kids3_mem : ∀ (cs : Kids) (k : Kid3), k ∈ kids3 T rk cs → k = .none ∨ ∃ c ∈ kidsList cs, k = kid3 T rk c
  | .nil, k, h => by simp [kids3] at h
  | .none r, k, h => by
    simp only [kids3, List.mem_cons] at h
    rcases h with rfl | h; · exact Or.inl rfl
    rcases kids3_mem r k h with h | ⟨c, hc, rfl⟩; · exact Or.inl h
    exact Or.inr ⟨c, by simpa [kidsList] using hc, rfl⟩
  | .some c r, k, h => by
    simp only [kids3, List.mem_cons] at h
    rcases h with rfl | h; · exact Or.inr ⟨c, by simp [kidsList], rfl⟩
    rcases kids3_mem r k h with h | ⟨c', hc, rfl⟩; · exact Or.inl h
    exact Or.inr ⟨c', by simp [kidsList, hc], rfl⟩

theorem kid3_mem_kids3 : ∀ (cs : Kids) (c : PTrie), c ∈ kidsList cs → kid3 T rk c ∈ kids3 T rk cs
  | .nil, c, h => by simp [kidsList] at h
  | .none r, c, h => by simp only [kids3, List.mem_cons]; exact Or.inr (kid3_mem_kids3 r c (by simpa [kidsList] using h))
  | .some d r, c, h => by
    simp only [kidsList, List.mem_cons] at h
    simp only [kids3, List.mem_cons]
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (kid3_mem_kids3 r c h)

theorem kid3_mem (o c : PTrie) (hc : c ∈ children o) : kid3 T rk c ∈ (rec3 T rk o).kids := by
  cases o with
  | hash => simp [children] at hc
  | leaf => simp [children] at hc
  | ext k c' m => simp [children] at hc; subst hc; simp [rec3, Rec3.kids]
  | branch v cs m => exact kid3_mem_kids3 cs c hc

theorem rec3_kids {o : PTrie} {i : Nat} (h : Kid3.node i ∈ (rec3 T rk o).kids) :
    ∃ c ∈ children o, c.hashOf ∈ digs T ∧ i = idx T rk c.hashOf := by
  have key : ∀ c, Kid3.node i = kid3 T rk c → c.hashOf ∈ digs T ∧ i = idx T rk c.hashOf := by
    intro c hk
    rcases kid3_cases (T := T) (rk := rk) c with ⟨hd, he⟩ | ⟨_, he⟩
    · rw [he] at hk; exact ⟨hd, Kid3.node.inj hk⟩
    · rw [he] at hk; cases hk
  cases o with
  | hash => simp [rec3, Rec3.kids] at h
  | leaf => simp [rec3, Rec3.kids] at h
  | ext k c m =>
    simp only [rec3, Rec3.kids, List.mem_singleton] at h
    exact ⟨c, by simp [children], key c h⟩
  | branch v cs m =>
    simp only [rec3, Rec3.kids] at h
    rcases kids3_mem cs _ h with h' | ⟨c, hc, he⟩; · cases h'
    exact ⟨c, hc, key c he⟩

theorem vslot3_val {sl : Slot} {i : Nat} (h : vslot3 T sl = .val i) : ∃ v ∈ Vs T, i = vidx T v := by
  unfold vslot3 at h
  split at h
  · rename_i v hf; cases h; exact ⟨v, List.mem_of_find?_eq_some hf, rfl⟩
  · cases h

theorem rec3_vids {o : PTrie} {i : Nat} (h : i ∈ (rec3 T rk o).vids) : ∃ v ∈ Vs T, i = vidx T v := by
  cases o with
  | hash => simp [rec3, Rec3.vids] at h
  | ext => simp [rec3, Rec3.vids] at h
  | leaf k sl m =>
    simp only [rec3] at h
    cases hv : vslot3 T sl with
    | ref => rw [hv] at h; simp [Rec3.vids] at h
    | val j => rw [hv] at h; simp [Rec3.vids] at h; subst h; exact vslot3_val hv
  | branch bv cs m =>
    simp only [rec3] at h
    cases bv with
    | none => simp [Rec3.vids] at h
    | some sl =>
      cases hv : vslot3 T sl with
      | ref => simp [hv, Rec3.vids] at h
      | val j => simp [hv, Rec3.vids] at h; subst h; exact vslot3_val hv

theorem kids3_length : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → (kids3 T rk cs).length = n
  | .nil, n, h => by simp [Kids.wf] at h; simp [kids3, h]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [kids3, kids3_length r _ h.2]; omega
  | .some _ r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [kids3, kids3_length r _ h.2]; omega

theorem kidsList_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → ∀ c ∈ kidsList cs, c.wf = true
  | .nil, _, _, c, h => by simp [kidsList] at h
  | .none r, n, hw, c, h => kidsList_wf r _ (wf_kids_none hw) c (by simpa [kidsList] using h)
  | .some d r, n, hw, c, h => by
    simp only [kidsList, List.mem_cons] at h
    rcases h with rfl | h
    · exact (wf_kids_some hw).1
    · exact kidsList_wf r _ (wf_kids_some hw).2 c h

theorem kid3_wf {c : PTrie} (hc : c.wf = true) : (kid3 T rk c).wf ∧ kid3 T rk c ≠ .none := by
  rcases kid3_cases (T := T) (rk := rk) c with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he]
  · exact ⟨trivial, by simp⟩
  · exact ⟨hashOf_len_of_wf c hc, by simp⟩

theorem rec3_wf (H : CHyp s T rk) {o : PTrie} (ho : o ∈ occs T) : (rec3 T rk o).wf (vsOf T τ) := by
  have hw := occs_wf T H.wf o ho
  cases o with
  | hash => exact absurd (occs_isNode T _ ho) (by simp [isNode])
  | leaf k sl m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    exact ⟨h1, h4, (vslot3_spec (τ := τ) H sl h2).2.1, h3⟩
  | ext k c m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    have hk := kid3_wf (T := T) (rk := rk) h2
    exact ⟨h1, h4, hk.2, hk.1, h3⟩
  | branch bv cs m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    refine ⟨kids3_length cs 16 h2, ?_, ?_, h3⟩
    · intro sl hsl
      cases bv with
      | none => simp at hsl
      | some sl0 =>
        simp at hsl; subst hsl
        exact (vslot3_spec (τ := τ) H sl0 (by simpa using h1)).2.1
    · intro k hk
      rcases kids3_mem cs k hk with rfl | ⟨c, hc, rfl⟩
      · trivial
      · exact (kid3_wf (kidsList_wf cs 16 h2 c hc)).1

theorem ns_some {n : Nat} {nr : NodeRec3} (h : (nsOf T rk τ)[n]? = some nr) :
    ∃ d, (Ds T rk)[n]? = some d ∧ nr = ⟨τ, rec3 T rk (canon T d)⟩ := by
  rw [ns_get] at h
  cases hd : (Ds T rk)[n]? with
  | none => simp [hd] at h
  | some d => simp [hd] at h; exact ⟨d, rfl, h.symm⟩

theorem Ds_mem {n : Nat} {d : Bytes} (h : (Ds T rk)[n]? = some d) : d ∈ digs T :=
  mem_Ds.1 (List.mem_of_getElem? h)

theorem inInst_idx {d : Bytes} (hd : d ∈ digs T) : InInst (nsOf T rk τ) τ (idx T rk d) :=
  ⟨_, by rw [ns_get, Ds_idx hd]; rfl, rfl⟩

/-- The records form a rooted DAG, acyclic by id order. -/
theorem rooted (H : CHyp s T rk) : RootedDag (nsOf T rk τ) (vsOf T τ) τ (idx T rk T.hashOf) where
  root_inst := inInst_idx (mem_digs.2 ⟨T, self_mem_occs H.node, rfl⟩)
  child := by
    intro n nr hnr ht c hc
    obtain ⟨d, hd, rfl⟩ := ns_some hnr
    obtain ⟨ch, hch, hdig, rfl⟩ := rec3_kids hc
    have hdm := Ds_mem hd
    obtain ⟨hco, hch'⟩ := canon_spec hdm
    have hr := H.dag.1 _ hco ch hch hdig
    rw [hch'] at hr
    refine ⟨?_, inInst_idx hdig⟩
    rw [← idx_get hd]; exact idx_order hdm hdig hr
  vals := by
    intro n nr hnr ht i hi
    obtain ⟨d, hd, rfl⟩ := ns_some hnr
    obtain ⟨v, hv, rfl⟩ := rec3_vids hi
    exact ⟨_, vs_get hv, rfl⟩
  wf := by
    intro n nr hnr ht
    obtain ⟨d, hd, rfl⟩ := ns_some hnr
    exact rec3_wf H (canon_spec (Ds_mem hd)).1

/-! ### Unfolding the records -/

theorem nodeTree3_isNode (vs : List ValRec3) (g : Nat → PTrie) (r : Rec3) : isNode (nodeTree3 vs g r) = true := by
  cases r <;> rfl

/-- The induction predicate: record `n` unfolds to a trie with the digest and
preimage of its canonical occurrence, refined by every occurrence of that digest. -/
def UP (T : PTrie) (rk : Bytes → Nat) (τ : Nat) (n : Nat) : Prop := ∀ d, (Ds T rk)[n]? = some d →
  (fullTree (nsOf T rk τ) (vsOf T τ) n).hashOf = d ∧
  nodeEnc (fullTree (nsOf T rk τ) (vsOf T τ) n) = nodeEnc (canon T d) ∧
  ∀ o ∈ occs T, o.hashOf = d → o.refinedBy (fullTree (nsOf T rk τ) (vsOf T τ) n)

theorem child_spec (ch : PTrie) (hih : ch.hashOf ∈ digs T → UP T rk τ (idx T rk ch.hashOf)) :
    (kidTree3 (fullTree (nsOf T rk τ) (vsOf T τ)) (kid3 T rk ch)).hashOf = ch.hashOf ∧
    ∀ c', c'.hashOf = ch.hashOf → (isNode c' = true → c' ∈ occs T) →
      c'.refinedBy (kidTree3 (fullTree (nsOf T rk τ) (vsOf T τ)) (kid3 T rk ch)) := by
  rcases kid3_cases (T := T) (rk := rk) ch with ⟨hd, he⟩ | ⟨hnd, he⟩ <;> rw [he] <;> simp only [kidTree3]
  · have u := hih hd ch.hashOf (Ds_idx hd)
    refine ⟨u.1, ?_⟩
    intro c' hc' hocc
    cases hn : isNode c' with
    | true => exact u.2.2 c' (hocc hn) hc'
    | false =>
      cases c' with
      | hash h => simp only [PTrie.refinedBy]; rw [u.1]; simpa [PTrie.hashOf] using hc'
      | _ => simp [isNode] at hn
  · refine ⟨rfl, ?_⟩
    intro c' hc' hocc
    cases hn : isNode c' with
    | true => exact absurd (mem_digs.2 ⟨c', hocc hn, hc'⟩) hnd
    | false =>
      cases c' with
      | hash h => simpa [PTrie.refinedBy, PTrie.hashOf] using hc'
      | _ => simp [isNode] at hn

theorem kidsOf3_cons_ne (g : Nat → PTrie) (k : Kid3) (r : List Kid3) (hk : k ≠ .none) :
    kidsOf3 g (k :: r) = .some (kidTree3 g k) (kidsOf3 g r) := by
  cases k with
  | none => exact absurd rfl hk
  | hash => rfl
  | node => rfl

theorem optHashes_nil {cs : Kids} (h : Kids.optHashes cs = []) : cs = .nil := by
  cases cs <;> simp_all [Kids.optHashes]

theorem kids_spec3 : ∀ (cs : Kids),
    (∀ ch ∈ kidsList cs, ch.hashOf ∈ digs T → UP T rk τ (idx T rk ch.hashOf)) →
    ∀ (cs' : Kids), Kids.optHashes cs' = Kids.optHashes cs → (∀ c ∈ kidsList cs', isNode c = true → c ∈ occs T) →
    Kids.hashes (kidsOf3 (fullTree (nsOf T rk τ) (vsOf T τ)) (kids3 T rk cs)) = Kids.hashes cs ∧
    (∀ i, kidsBitmap (kidsOf3 (fullTree (nsOf T rk τ) (vsOf T τ)) (kids3 T rk cs)) i = kidsBitmap cs i) ∧
    Kids.refinedBy cs' (kidsOf3 (fullTree (nsOf T rk τ) (vsOf T τ)) (kids3 T rk cs))
  | .nil, _, cs', he, _ => by
    simp only [Kids.optHashes] at he
    rw [optHashes_nil he]
    simp [kids3, kidsOf3, Kids.hashes, kidsBitmap, Kids.refinedBy]
  | .none r, hih, cs', he, hocc => by
    cases cs' with
    | nil => simp [Kids.optHashes] at he
    | some _ _ => simp [Kids.optHashes] at he
    | none r' =>
      simp only [Kids.optHashes, List.cons.injEq, true_and] at he
      have ih := kids_spec3 r (fun ch hch => hih ch (by simpa [kidsList] using hch)) r' he
        (fun c hc => hocc c (by simpa [kidsList] using hc))
      simp only [kids3, kidsOf3, Kids.hashes, kidsBitmap, Kids.refinedBy]
      exact ⟨ih.1, fun i => ih.2.1 (i + 1), ih.2.2⟩
  | .some c r, hih, cs', he, hocc => by
    cases cs' with
    | nil => simp [Kids.optHashes] at he
    | none _ => simp [Kids.optHashes] at he
    | some c' r' =>
      simp only [Kids.optHashes, List.cons.injEq, Option.some.injEq] at he
      have ih := kids_spec3 r (fun ch hch => hih ch (by simp [kidsList, hch])) r' he.2
        (fun c hc => hocc c (by simp [kidsList, hc]))
      have hc := child_spec (τ := τ) c (hih c (by simp [kidsList]))
      have hne : kid3 T rk c ≠ .none := by
        rcases kid3_cases (T := T) (rk := rk) c with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> simp
      simp only [kids3, kidsOf3_cons_ne _ _ _ hne, Kids.hashes, kidsBitmap, Kids.refinedBy, hc.1]
      exact ⟨by rw [ih.1], fun i => by rw [ih.2.1], hc.2 c' he.1 (fun hn => hocc c' (by simp [kidsList]) hn), ih.2.2⟩

theorem unfold_spec (H : CHyp s T rk) : ∀ n, InInst (nsOf T rk τ) τ n → UP T rk τ n := by
  apply dag_induction (rooted H)
  intro n nr hnr ht ih d hd
  obtain ⟨d', hd', rfl⟩ := ns_some hnr
  rw [hd] at hd'; cases hd'
  have hdm := Ds_mem hd
  obtain ⟨hco, hch⟩ := canon_spec hdm
  have hih : ∀ ch ∈ children (canon T d), ch.hashOf ∈ digs T → UP T rk τ (idx T rk ch.hashOf) := by
    intro ch hc hdig
    apply ih
    have := kid3_mem (T := T) (rk := rk) _ ch hc
    rcases kid3_cases (T := T) (rk := rk) ch with ⟨_, he⟩ | ⟨hnd, _⟩
    · rw [he] at this; exact this
    · exact absurd hdig hnd
  rw [fullTree_unfold (rooted H) hnr rfl]
  -- occurrences of `d` share the canonical preimage, hence its skeleton
  have hsk : ∀ o ∈ occs T, o.hashOf = d → skelOf o = skelOf (canon T d) := fun o ho he =>
    skel_eq (occs_isNode T o ho) (occs_isNode T _ hco) (H.enc_eq ho hco (by rw [he, hch]))
  suffices hE : nodeEnc (nodeTree3 (vsOf T τ) (fullTree (nsOf T rk τ) (vsOf T τ)) (rec3 T rk (canon T d))) =
      nodeEnc (canon T d) ∧ ∀ o ∈ occs T, o.hashOf = d →
      o.refinedBy (nodeTree3 (vsOf T τ) (fullTree (nsOf T rk τ) (vsOf T τ)) (rec3 T rk (canon T d))) by
    refine ⟨?_, hE.1, hE.2⟩
    rw [hashOf_eq_enc _ (nodeTree3_isNode _ _ _), hE.1, ← hashOf_eq_enc _ (occs_isNode T _ hco), hch]
  have hcw := occs_wf T H.wf _ hco
  have hval : ∀ o ∈ occs T, ∀ v, v ∈ ownVals o → v ∈ valsOf T := fun o ho v hv => ownVals_sub ho hv
  generalize canon T d = oc at hco hch hcw hih hsk ⊢
  cases oc with
  | hash h => exact absurd (occs_isNode T _ hco) (by simp [isNode])
  | leaf k sl m =>
    have hok : slotOk sl = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hcw; exact hcw.1.1.2
    have hv := vslot3_spec (τ := τ) H sl hok
    refine ⟨by simp [rec3, nodeTree3, nodeEnc, hv.1], ?_⟩
    intro o ho he
    have hs := hsk o ho he
    have how := occs_wf T H.wf o ho
    rw [skel_leaf hcw] at hs
    cases o with
    | hash => exact absurd (occs_isNode T _ ho) (by simp [isNode])
    | ext => rw [skel_ext how] at hs; cases hs
    | branch bv => cases bv with
      | none => rw [skel_branch how] at hs; cases hs
      | some => rw [skel_branchV how] at hs; cases hs
    | leaf k' sl' m' =>
      rw [skel_leaf how] at hs
      simp only [PTrie.leaf.injEq, Slot.ref.injEq] at hs
      obtain ⟨rfl, ⟨hl, hh⟩, rfl⟩ := hs
      refine ⟨rfl, rfl, hv.2.2 sl' hl hh ?_⟩
      intro v hsv; subst hsv; exact hval _ ho v (by simp [ownVals, slotVal])
  | ext k c m =>
    have hc := child_spec (τ := τ) c (hih c (by simp [children]))
    refine ⟨by simp [rec3, nodeTree3, nodeEnc, hc.1], ?_⟩
    intro o ho he
    have hs := hsk o ho he
    have how := occs_wf T H.wf o ho
    rw [skel_ext hcw] at hs
    cases o with
    | hash => exact absurd (occs_isNode T _ ho) (by simp [isNode])
    | leaf => rw [skel_leaf how] at hs; cases hs
    | branch bv => cases bv with
      | none => rw [skel_branch how] at hs; cases hs
      | some => rw [skel_branchV how] at hs; cases hs
    | ext k' c' m' =>
      rw [skel_ext how] at hs
      simp only [PTrie.ext.injEq, PTrie.hash.injEq] at hs
      obtain ⟨rfl, hh, rfl⟩ := hs
      exact ⟨rfl, rfl, hc.2 c' hh (fun hn => child_occ ho (by simp [children]) hn)⟩
  | branch bv cs m =>
    have hkw : Kids.wf cs 16 = true := wf_branch hcw
    have hks := kids_spec3 (τ := τ) cs (fun ch hc => hih ch (by simpa [children] using hc)) cs rfl
      (fun c hc hn => child_occ hco (by simpa [children] using hc) hn)
    have hvs : ∀ sl, bv = some sl → slotOk sl = true := by
      intro sl e; subst e; simp only [PTrie.wf, Bool.and_eq_true] at hcw; simpa using hcw.1.1
    refine ⟨?_, ?_⟩
    · cases bv with
      | none => simp [rec3, nodeTree3, nodeEnc, hks.1, hks.2.1]
      | some sl => simp [rec3, nodeTree3, nodeEnc, hks.1, hks.2.1, (vslot3_spec (τ := τ) H sl (hvs sl rfl)).1]
    · intro o ho he
      have hs := hsk o ho he
      have how := occs_wf T H.wf o ho
      cases o with
      | hash => exact absurd (occs_isNode T _ ho) (by simp [isNode])
      | leaf =>
        rw [skel_leaf how] at hs
        cases bv with
        | none => rw [skel_branch hcw] at hs; cases hs
        | some => rw [skel_branchV hcw] at hs; cases hs
      | ext =>
        rw [skel_ext how] at hs
        cases bv with
        | none => rw [skel_branch hcw] at hs; cases hs
        | some => rw [skel_branchV hcw] at hs; cases hs
      | branch bv' cs' m' =>
        have hocc' : ∀ c ∈ kidsList cs', isNode c = true → c ∈ occs T :=
          fun c hc hn => child_occ ho (by simpa [children] using hc) hn
        cases bv with
        | none =>
          rw [skel_branch hcw] at hs
          cases bv' with
          | some => rw [skel_branchV how] at hs; cases hs
          | none =>
            rw [skel_branch how] at hs
            simp only [PTrie.branch.injEq, true_and] at hs
            obtain ⟨hk, rfl⟩ := hs
            have hk' := kids_spec3 (τ := τ) cs (fun ch hc => hih ch (by simpa [children] using hc)) cs'
              (skelKids_inj _ _ hk) hocc'
            exact ⟨rfl, trivial, hk'.2.2⟩
        | some sl =>
          rw [skel_branchV hcw] at hs
          cases bv' with
          | none => rw [skel_branch how] at hs; cases hs
          | some sl' =>
            rw [skel_branchV how] at hs
            simp only [PTrie.branch.injEq, Option.some.injEq, Slot.ref.injEq] at hs
            obtain ⟨⟨hl, hh⟩, hk, rfl⟩ := hs
            have hk' := kids_spec3 (τ := τ) cs (fun ch hc => hih ch (by simpa [children] using hc)) cs'
              (skelKids_inj _ _ hk) hocc'
            refine ⟨rfl, ?_, hk'.2.2⟩
            exact (vslot3_spec (τ := τ) H sl (hvs sl rfl)).2.2 sl' hl hh (fun v hsv => by
              subst hsv; exact hval _ ho v (by simp [ownVals, optSlotVal, slotVal]))

/-! ### The store -/

theorem filterMap_range_eq {α : Type} (g : Nat → Option α) (e : Nat → α) :
    ∀ n, (∀ i < n, g i = some (e i)) → (List.range n).filterMap g = (List.range n).map e
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.filterMap_append, List.map_append,
      filterMap_range_eq g e n (fun i hi => h i (by omega))]
    simp [h n (by omega)]

theorem F_enc (H : CHyp s T rk) {n : Nat} {d : Bytes} (hd : (Ds T rk)[n]? = some d) :
    nodeEnc (fullTree (nsOf T rk τ) (vsOf T τ) n) = nodeEnc (canon T d) ∧
    (fullTree (nsOf T rk τ) (vsOf T τ) n).hashOf = d :=
  have u := unfold_spec (τ := τ) H n ⟨_, by rw [ns_get, hd]; rfl, rfl⟩ d hd
  ⟨u.2.1, u.1⟩

theorem F_isNode (H : CHyp s T rk) {n : Nat} {d : Bytes} (hd : (Ds T rk)[n]? = some d) :
    isNode (fullTree (nsOf T rk τ) (vsOf T τ) n) = true := by
  rw [fullTree_unfold (rooted (τ := τ) H) (nr := ⟨τ, rec3 T rk (canon T d)⟩) (by rw [ns_get, hd]; rfl) rfl]
  exact nodeTree3_isNode _ _ _

theorem nodeEntries_eq : nodeEntries (nsOf T rk τ) (vsOf T τ) τ =
    (List.range (Ds T rk).length).map (fun n => nodeEnc (fullTree (nsOf T rk τ) (vsOf T τ) n)) := by
  unfold nodeEntries
  rw [Ds_length (τ := τ)]
  apply filterMap_range_eq
  intro i hi
  rw [ns_get, List.getElem?_eq_getElem hi]
  simp

theorem valEntries_eq : valEntries (vsOf T τ) τ = Vs T := by
  simp [valEntries, vsOf, List.filter_map, Function.comp_def]

theorem store_digests (H : CHyp s T rk) :
    (storeOf (nsOf T rk τ) (vsOf T τ) τ).map sha256 = Ds T rk ++ (Vs T).map sha256 := by
  rw [storeOf, List.map_append, nodeEntries_eq, valEntries_eq]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < (Ds T rk).length := by simpa using h1
    have hd : (Ds T rk)[i]? = some (Ds T rk)[i] := List.getElem?_eq_getElem hi
    simp only [List.getElem_map, List.getElem_range]
    rw [← hashOf_eq_enc _ (F_isNode (τ := τ) H hd), (F_enc (τ := τ) H hd).2]

/-- The record store has pairwise-distinct digests (the `uniq` obligation). -/
theorem digests_distinct (H : CHyp s T rk) : DigestsDistinct (storeOf (nsOf T rk τ) (vsOf T τ) τ) := by
  unfold DigestsDistinct
  rw [store_digests H, List.nodup_append]
  refine ⟨nodup_Ds, nodup_map_of_inj _ _ (nodup_dedup _)
    (fun x hx y hy he => H.val_inj (mem_Vs.1 hx) (mem_Vs.1 hy) he), ?_⟩
  intro a ha b hb e
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
  subst e
  exact H.dag.2 v (mem_Vs.1 hv) (mem_Ds.1 ha)

theorem store_sub {ws : List Bytes} (H : CHyp (mkStore ws) T rk) :
    ∀ e ∈ storeOf (nsOf T rk τ) (vsOf T τ) τ, e ∈ ws := by
  intro e he
  rw [storeOf, List.mem_append, nodeEntries_eq, valEntries_eq] at he
  have hF : Found (mkStore ws) e := by
    rcases he with he | he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
      rw [List.mem_range] at hi
      have hd : (Ds T rk)[i]? = some (Ds T rk)[i] := List.getElem?_eq_getElem hi
      rw [(F_enc (τ := τ) H hd).1]
      exact H.occ_found (canon_spec (Ds_mem hd)).1
    · exact H.val_found (mem_Vs.1 he)
  exact (storeGet_some hF).2

theorem store_bytes {ws : List Bytes} (H : CHyp (mkStore ws) T rk) :
    storeBytes (nsOf T rk τ) (vsOf T τ) τ ≤ (ws.map List.length).sum :=
  sum_le_of_nodup_sub _ ws (nodup_of_map sha256 _ (digests_distinct H)) (store_sub H)

end Proofs

/-! ## Depth along a refinement -/

mutual
theorem fdepth_refinedBy : ∀ (t₁ t₂ : PTrie) (k : List Nat), t₁.refinedBy t₂ → t₁.find k ≠ none →
    fdepth t₁ k = fdepth t₂ k
  | .hash _, _, k, _, h => absurd (find_hash_none _ k) h
  | .leaf _ _ _, t₂, k, hr, _ => by cases t₂ <;> simp_all [PTrie.refinedBy, fdepth]
  | .ext k c m, t₂, key, hr, hf => by
    cases t₂ with
    | ext k' c' m' =>
      obtain ⟨rfl, rfl, hc⟩ := hr
      simp only [fdepth]
      split
      · rename_i hp
        simp only [PTrie.find, hp, ↓reduceIte] at hf
        rw [fdepth_refinedBy c c' _ hc hf]
      · rfl
    | _ => simp [PTrie.refinedBy] at hr
  | .branch v cs m, t₂, key, hr, hf => by
    cases t₂ with
    | branch v' cs' m' =>
      cases key with
      | nil => simp [fdepth]
      | cons n r =>
        simp only [fdepth]
        rw [kfdepth_refinedBy cs cs' n r hr.2.2 (by simpa [PTrie.find] using hf)]
    | _ => simp [PTrie.refinedBy] at hr
theorem kfdepth_refinedBy : ∀ (cs cs' : Kids) (n : Nat) (r : List Nat), Kids.refinedBy cs cs' →
    Kids.find cs n r ≠ none → kfdepth cs n r = kfdepth cs' n r
  | .nil, cs', n, r, hr, _ => by cases cs' <;> simp_all [Kids.refinedBy, kfdepth]
  | .none a, cs', n, r, hr, hf => by
    cases cs' with
    | none a' =>
      cases n with
      | zero => simp [kfdepth]
      | succ n => simp only [kfdepth]; exact kfdepth_refinedBy a a' n r hr (by simpa [Kids.find] using hf)
    | _ => simp [Kids.refinedBy] at hr
  | .some c a, cs', n, r, hr, hf => by
    cases cs' with
    | some c' a' =>
      cases n with
      | zero => simp only [kfdepth]; exact fdepth_refinedBy c c' r hr.1 (by simpa [Kids.find] using hf)
      | succ n => simp only [kfdepth]; exact kfdepth_refinedBy a a' n r hr.2 (by simpa [Kids.find] using hf)
    | _ => simp [Kids.refinedBy] at hr
end

/-! ## Completeness -/

/-- **Completeness direction of `StoreBuildStmt`.** For any witness store `ws`
whose relation-built partial trie determines every read key and satisfies A6,
the hash-consed records of that trie are a rooted DAG with pairwise-distinct
digests, root digest `root`, every read key revealed within fuel and looked up
exactly as the relation does, and a store no larger than `ws`. -/
theorem storeComplete (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (τ : Nat)
    (rk : Bytes → Nat) (hroot : root.length = 32) (hne : keys ≠ [])
    (hread : ∀ k ∈ keys, (partialTrie ws root keys).find k ≠ none)
    (hdag : StoreDag (partialTrie ws root keys) rk) :
    ∃ (ns : List NodeRec3) (vs : List ValRec3) (r : Nat),
      RootedDag ns vs τ r ∧ DigestsDistinct (storeOf ns vs τ) ∧ HashFunctional (storeOf ns vs τ) ∧
      digest ns vs r = root ∧ PathsRevealed ns vs r keys ∧
      (∀ k ∈ keys, (fullTree ns vs r).find k = (partialTrie ws root keys).find k) ∧
      storeBytes ns vs τ ≤ (ws.map List.length).sum := by
  obtain ⟨hh, hw, hst, hdep⟩ := built_spec ws trieFuel root keys hroot
  have hT : partialTrie ws root keys = buildFor (mkStore ws) trieFuel root keys := rfl
  rw [← hT] at hh hw hst hdep
  generalize partialTrie ws root keys = T at hh hw hst hdep hread hdag ⊢
  have hnode : isNode T = true := by
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil keys hne
    have := hread k hk
    cases T with
    | hash h => exact absurd (find_hash_none h k) this
    | _ => rfl
  have H : CHyp (mkStore ws) T rk := ⟨hw, hst, hnode, hdag⟩
  have hrd : T.hashOf ∈ digs T := mem_digs.2 ⟨T, self_mem_occs hnode, rfl⟩
  have u := unfold_spec (τ := τ) H _ (inInst_idx hrd) T.hashOf (Ds_idx hrd)
  have href := u.2.2 T (self_mem_occs hnode) rfl
  have hfind : ∀ k ∈ keys, (fullTree (nsOf T rk τ) (vsOf T τ) (idx T rk T.hashOf)).find k = T.find k := by
    intro k hk
    have hf := hread k hk
    cases hx : T.find k with
    | none => exact absurd hx hf
    | some x => exact PTrie.find_refinedBy _ _ k x href hx
  refine ⟨nsOf T rk τ, vsOf T τ, idx T rk T.hashOf, rooted H, digests_distinct H,
    hashFunctional_of_nodup (digests_distinct H), ?_, ?_, hfind, store_bytes H⟩
  · unfold digest; rw [u.1, hh]
  · intro k hk
    refine ⟨by rw [hfind k hk]; exact hread k hk, ?_⟩
    rw [← fdepth_refinedBy _ _ k href (hread k hk)]
    exact hdep k

/-- Completeness, end to end: the record store rebuilds a trie that answers
every read key exactly like the relation's trie over the original store. -/
theorem storeComplete_rebuild (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (τ : Nat)
    (rk : Bytes → Nat) (hroot : root.length = 32) (hne : keys ≠ [])
    (hread : ∀ k ∈ keys, (partialTrie ws root keys).find k ≠ none)
    (hdag : StoreDag (partialTrie ws root keys) rk) :
    ∃ (ns : List NodeRec3) (vs : List ValRec3) (r : Nat),
      RootedDag ns vs τ r ∧ DigestsDistinct (storeOf ns vs τ) ∧
      storeBytes ns vs τ ≤ (ws.map List.length).sum ∧
      (partialTrie (storeOf ns vs τ) root keys).hashOf = root ∧
      ∀ k ∈ keys, (partialTrie (storeOf ns vs τ) root keys).find k = (partialTrie ws root keys).find k := by
  obtain ⟨ns, vs, r, hd, hdd, hf, hdig, hp, hfind, hsz⟩ :=
    storeComplete ws root keys τ rk hroot hne hread hdag
  have h := storeBuild ns vs τ r keys hf hd hp
  rw [hdig] at h
  exact ⟨ns, vs, r, hd, hdd, hsz, h.2.1, fun k hk => by rw [h.2.2 k hk, hfind k hk]⟩

/-- On any store, the relation's root-hash check is implied by construction. -/
theorem partialTrie_hashOf (ws : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hroot : root.length = 32) : (partialTrie ws root keys).hashOf = root :=
  (built_spec ws trieFuel root keys hroot).1

end ZkFormal.NearV3
