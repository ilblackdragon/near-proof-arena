import ZkFormal.Sha.Complete.Basic

/-!
# ZkFormal.Sha.Complete.Rows — the row structure of the honest trace

* `honestLog` bounds (`LogStmt`, `len_le_height`);
* `honestRows` as an explicit function of the row index inside each message
  (`msgRows_eq`);
* `step_at`: on every row `r < H`, (row `r`, row `(r+1) % H`) is one of the
  legal transitions `Step` (start → R0, Rj → Rj+1, R15 → D, D → R0 of the
  next block, last D → start/pad, pad → start/pad).
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen

/-! ## Height -/

theorem clog2_go_ge (n : Nat) : ∀ fuel acc, n ≤ 2 ^ (acc + fuel) → n ≤ 2 ^ clog2.go n fuel acc
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · assumption
    · exact clog2_go_ge n fuel (acc + 1) (by rw [show acc + 1 + fuel = acc + (fuel + 1) by omega]; exact h)

theorem clog2_go_le (n m : Nat) (hm : n ≤ 2 ^ m) : ∀ fuel acc, acc ≤ m → clog2.go n fuel acc ≤ m
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · exact h
    · next hn =>
      apply clog2_go_le n m hm fuel (acc + 1)
      have : acc ≠ m := fun e => hn (e ▸ hm)
      omega

theorem le_two_pow_self (n : Nat) : n ≤ 2 ^ n := Nat.le_of_lt (Nat.lt_two_pow_self)

theorem clog2_ge (n : Nat) : n ≤ 2 ^ clog2 n :=
  clog2_go_ge n n 0 (by simpa using le_two_pow_self n)

theorem clog2_le (n m : Nat) (hm : n ≤ 2 ^ m) : clog2 n ≤ m :=
  clog2_go_le n m hm n 0 (Nat.zero_le _)

theorem height_eq (msgs : List Msg) (t : Nat) :
    (honestTrace msgs).height t = 2 ^ honestLog msgs := rfl

theorem len_le_height (msgs : List Msg) (t : Nat) :
    (honestRows msgs).length ≤ (honestTrace msgs).height t := by
  rw [height_eq]
  exact Nat.le_trans (clog2_ge _) (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem logStmt : LogStmt := by
  intro msgs hok t
  refine ⟨Nat.le_max_left _ _, ?_⟩
  show max 1 (clog2 (honestRows msgs).length) ≤ 22
  have := clog2_le _ 22 hok.rows
  omega

/-! ## Messages as indexed rows -/

/-- Number of blocks of a message. -/
def nb (M : Msg) : Nat := (msgBlocks M.bytes).length

/-- Row `k` of message `M`. -/
def mrow (M : Msg) (k : Nat) : Row :=
  if k = 0 then .start M.id
  else if (k - 1) % 17 < 16 then .round ((k - 1) % 17) (blkOf M ((k - 1) / 17))
  else .digest (blkOf M ((k - 1) / 17))

theorem flatMap_range_map {α : Type} (m : Nat) (hm : 0 < m) (g : Nat → Nat → α) :
    ∀ n, (List.range n).flatMap (fun b => (List.range m).map (g b)) =
      (List.range (m * n)).map (fun k => g (k / m) (k % m))
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_map m hm g n,
      show m * (n + 1) = m * n + m by rw [Nat.mul_succ], List.range_add, List.map_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    simp only [Function.comp]
    rw [show (m * n + k) / m = n by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hk, Nat.zero_add],
      show (m * n + k) % m = k by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]]

theorem blockRows_eq (B : Blk) :
    (List.range 16).map (fun j => Row.round j B) ++ [Row.digest B] =
      (List.range 17).map (fun j => if j < 16 then Row.round j B else Row.digest B) := by
  rw [List.range_succ, List.map_append]
  congr 1

theorem msgRows_eq (M : Msg) : msgRows M = (List.range (1 + 17 * nb M)).map (mrow M) := by
  rw [Nat.add_comm, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [msgRows, blockRows_eq]
  rw [flatMap_range_map 17 (by decide) (fun b j => if j < 16 then Row.round j (blkOf M b) else Row.digest (blkOf M b))]
  congr 1

theorem nb_pos (M : Msg) : 1 ≤ nb M := by
  unfold nb msgBlocks
  have : 64 ≤ (ArenaCore.SHA256.pad M.bytes).length := by
    simp only [ArenaCore.SHA256.pad, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, List.length_map, ArenaCore.Bytes.beN_length]
    omega
  have hc : ∀ n (l : List Nat), (chunks n l).length = n := by
    intro n; induction n with
    | zero => intro l; rfl
    | succ n ih => intro l; simp [chunks, ih]
  rw [hc]; omega

/-! ## Transitions -/

/-- Inputs of a message the generator supports. -/
structure MOk (M : Msg) : Prop where
  bytes : ∀ x ∈ M.bytes, x < 256
  len : M.bytes.length < 2 ^ 25

/-- Legal (row, next row) pairs of the honest trace. -/
inductive Step : Row → Row → Prop
  | start (M : Msg) (hM : MOk M) : Step (.start M.id) (.round 0 (blkOf M 0))
  | round (M : Msg) (b j : Nat) (hM : MOk M) (hb : b < nb M) (hj : j < 15) :
      Step (.round j (blkOf M b)) (.round (j + 1) (blkOf M b))
  | r15 (M : Msg) (b : Nat) (hM : MOk M) (hb : b < nb M) :
      Step (.round 15 (blkOf M b)) (.digest (blkOf M b))
  | dnext (M : Msg) (b : Nat) (hM : MOk M) (hb : b + 1 < nb M) :
      Step (.digest (blkOf M b)) (.round 0 (blkOf M (b + 1)))
  | dlast (M : Msg) (b : Nat) (hM : MOk M) (hb : b + 1 = nb M) (X : Row)
      (hX : X = .pad ∨ ∃ id, X = .start id) : Step (.digest (blkOf M b)) X
  | pad (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) : Step .pad X

/-- Consecutive elements of `l` (default `.pad`) are related by `R`. -/
def Chain (R : Row → Row → Prop) (l : List Row) : Prop :=
  ∀ i, i + 1 < l.length → R (l.getD i .pad) (l.getD (i + 1) .pad)

theorem chain_map_range (R : Row → Row → Prop) (n : Nat) (f : Nat → Row)
    (h : ∀ k, k + 1 < n → R (f k) (f (k + 1))) : Chain R ((List.range n).map f) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : i < n),
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  exact h i hi

theorem chain_append (R : Row → Row → Prop) (l1 l2 : List Row) (h1 : Chain R l1)
    (h2 : Chain R l2)
    (hl : ∀ hne : l1 ≠ [], l2 ≠ [] → R (l1.getLast hne) (l2.getD 0 .pad)) :
    Chain R (l1 ++ l2) := by
  intro i hi
  simp only [List.length_append] at hi
  simp only [List.getD_eq_getElem?_getD]
  by_cases hA : i + 1 < l1.length
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left hA]
    have := h1 i hA
    simpa [List.getD_eq_getElem?_getD] using this
  · by_cases hB : i < l1.length
    · have e : i + 1 = l1.length := by omega
      rw [List.getElem?_append_left hB, List.getElem?_append_right (by omega), e, Nat.sub_self]
      have hne : l1 ≠ [] := by intro h; subst h; simp at hB
      have hne2 : l2 ≠ [] := by intro h; subst h; simp at hi; omega
      have := hl hne hne2
      rw [List.getLast_eq_getElem] at this
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have e2 : l1[l1.length - 1] = l1[i] := by congr 1; omega
      rw [e2] at this
      simpa [List.getD_eq_getElem?_getD] using this
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        show i + 1 - l1.length = i - l1.length + 1 by omega]
      have := h2 (i - l1.length) (by omega)
      simpa [List.getD_eq_getElem?_getD] using this

theorem mrow_step (M : Msg) (hM : MOk M) (k : Nat) (hk : k + 1 < 1 + 17 * nb M) :
    Step (mrow M k) (mrow M (k + 1)) := by
  unfold mrow
  by_cases h0 : k = 0
  · subst h0; simpa using Step.start M hM
  · rw [if_neg h0, if_neg (by omega : ¬ (k + 1 = 0))]
    have hq : (k - 1) / 17 < nb M := by omega
    by_cases hj : (k - 1) % 17 < 15
    · rw [if_pos (by omega), if_pos (by omega), show (k + 1 - 1) / 17 = (k - 1) / 17 by omega,
        show (k + 1 - 1) % 17 = (k - 1) % 17 + 1 by omega]
      exact Step.round M _ _ hM hq hj
    · by_cases hj' : (k - 1) % 17 = 15
      · rw [if_pos (by omega), if_neg (by omega), show (k + 1 - 1) / 17 = (k - 1) / 17 by omega, hj']
        exact Step.r15 M _ hM hq
      · rw [if_neg (by omega), if_pos (by omega), show (k + 1 - 1) / 17 = (k - 1) / 17 + 1 by omega,
          show (k + 1 - 1) % 17 = 0 by omega]
        exact Step.dnext M _ hM (by omega)

theorem mrow_last (M : Msg) (hM : MOk M) (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) :
    Step (mrow M (17 * nb M)) X := by
  have h1 := nb_pos M
  unfold mrow
  rw [if_neg (by omega), if_neg (by omega)]
  exact Step.dlast M _ hM (by omega) X hX

theorem honestRows_chain (msgs : List Msg) (hok : ∀ M ∈ msgs, MOk M) :
    Chain Step (honestRows msgs) := by
  induction msgs with
  | nil => intro i hi; simp [honestRows] at hi
  | cons M rest ih =>
    have hM := hok M (List.mem_cons_self ..)
    have ih' := ih (fun M' h => hok M' (List.mem_cons_of_mem _ h))
    show Chain Step (msgRows M ++ honestRows rest)
    refine chain_append _ _ _ ?_ ih' ?_
    · rw [msgRows_eq]; exact chain_map_range _ _ _ (mrow_step M hM)
    · intro hne _
      have : (msgRows M).getLast hne = mrow M (17 * nb M) := by
        simp only [msgRows_eq, List.getLast_eq_getElem, List.getElem_map, List.length_map,
          List.length_range, List.getElem_range]
        congr 1; omega
      rw [this]
      apply mrow_last M hM
      cases rest with
      | nil => left; rfl
      | cons M' rest' =>
        right; refine ⟨M'.id, ?_⟩
        show (msgRows M' ++ honestRows rest').getD 0 .pad = _
        simp [msgRows]

theorem honestRows_head (msgs : List Msg) :
    (honestRows msgs).getD 0 .pad = .pad ∨ ∃ id, (honestRows msgs).getD 0 .pad = .start id := by
  cases msgs with
  | nil => left; rfl
  | cons M rest =>
    right; refine ⟨M.id, ?_⟩
    show (msgRows M ++ honestRows rest).getD 0 .pad = _
    simp [msgRows]

theorem honestRows_last (msgs : List Msg) (hok : ∀ M ∈ msgs, MOk M) (hne : honestRows msgs ≠ [])
    (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) : Step ((honestRows msgs).getLast hne) X := by
  induction msgs with
  | nil => exact absurd rfl hne
  | cons M rest ih =>
    have hM := hok M (List.mem_cons_self ..)
    by_cases hr : honestRows rest = []
    · have e : honestRows (M :: rest) = msgRows M := by
        show msgRows M ++ honestRows rest = _; rw [hr, List.append_nil]
      have : (honestRows (M :: rest)).getLast hne = mrow M (17 * nb M) := by
        simp only [e, msgRows_eq, List.getLast_eq_getElem, List.getElem_map, List.length_map,
          List.length_range, List.getElem_range]
        congr 1; omega
      rw [this]; exact mrow_last M hM X hX
    · have e : (honestRows (M :: rest)).getLast hne = (honestRows rest).getLast hr := by
        show (msgRows M ++ honestRows rest).getLast _ = _
        exact List.getLast_append_of_ne_nil _ hr
      rw [e]; exact ih (fun M' h => hok M' (List.mem_cons_of_mem _ h)) hr

/-- Row `r` of the honest table. -/
def rowAt (msgs : List Msg) (r : Nat) : Row := (honestRows msgs).getD r .pad

theorem honestCell_eq (msgs : List Msg) (r c : Nat) :
    honestCell msgs r c = rowCell (rowAt msgs r) c := rfl

theorem mok_of (msgs : List Msg) (hok : MsgsOk msgs) : ∀ M ∈ msgs, MOk M :=
  fun M hM => ⟨hok.bytes M hM, hok.len M hM⟩

/-- **The transition structure**: every row and its cyclic successor form a `Step`. -/
theorem step_at (msgs : List Msg) (hok : MsgsOk msgs) (t r : Nat)
    (hr : r < (honestTrace msgs).height t) :
    Step (rowAt msgs r) (rowAt msgs ((r + 1) % (honestTrace msgs).height t)) := by
  have hm := mok_of msgs hok
  have hlen := len_le_height msgs t
  generalize hH : (honestTrace msgs).height t = H at hr hlen
  have hhead := honestRows_head msgs
  by_cases h1 : r + 1 < (honestRows msgs).length
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact honestRows_chain msgs hm r h1
  · have hX : rowAt msgs ((r + 1) % H) = .pad ∨ ∃ id, rowAt msgs ((r + 1) % H) = .start id := by
      by_cases h2 : r + 1 < H
      · left; rw [Nat.mod_eq_of_lt h2]; unfold rowAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      · rw [show r + 1 = H by omega, Nat.mod_self]; exact hhead
    by_cases h3 : r < (honestRows msgs).length
    · have hne : honestRows msgs ≠ [] := by intro h; rw [h] at h3; simp at h3
      have e : rowAt msgs r = (honestRows msgs).getLast hne := by
        unfold rowAt
        rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3,
          Option.getD_some]
        congr 1; omega
      rw [e]; exact honestRows_last msgs hm hne _ hX
    · have e : rowAt msgs r = .pad := by
        unfold rowAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [e]; exact Step.pad _ hX

theorem row0 (msgs : List Msg) : rowAt msgs 0 = .pad ∨ ∃ id, rowAt msgs 0 = .start id :=
  honestRows_head msgs

end ZkFormal.Sha.Complete
