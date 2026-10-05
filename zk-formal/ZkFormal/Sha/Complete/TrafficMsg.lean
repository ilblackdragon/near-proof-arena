import ZkFormal.Sha.Complete.Frame3

/-!
# ZkFormal.Sha.Complete.TrafficMsg — what each message's rows put on the buses

`rowRecvN row` / `rowDigN row` are the `(Id, pos, byte)` receives and the
digest provide of one honest row, on naturals.  Per message, the rows
receive exactly the message bytes (`msg_recv`) and provide exactly the
`sha256` digest when `dmult` (`msg_dig`).
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Sha.Gen

/-- Byte receives of a row: `(Id, position, byte)` for each data byte. -/
def rowRecvN : Row → List (List Nat)
  | .round j B =>
    if j < 4 then
      (List.range 16).filterMap fun q =>
        if 64 * B.idx + (16 * j + q) < B.len then
          some [B.id, 64 * B.idx + (16 * j + q), B.blk.getD (16 * j + q) 0]
        else none
    else []
  | _ => []

/-- Digest provide of a row. -/
def rowDigN : Row → List (List Nat)
  | .digest B =>
    if B.idx + 1 = B.nblk ∧ B.dmult = true then
      [[B.id, min B.len (64 * B.idx + 64)] ++
        (List.range 32).map fun p => B.hout (p / 4) / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8]
    else []
  | _ => []

/-! ## List plumbing -/

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem filterMap_congr' {α β : Type} {l : List α} {f g : α → Option β} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem flatMap_range_div {α : Type} (m : Nat) (hm : 0 < m) (g : Nat → Nat → List α) :
    ∀ n, (List.range (m * n)).flatMap (fun k => g (k / m) (k % m)) =
      (List.range n).flatMap (fun b => (List.range m).flatMap (g b))
  | 0 => by simp
  | n + 1 => by
    rw [show m * (n + 1) = m * n + m by rw [Nat.mul_succ], List.range_add, List.flatMap_append,
      flatMap_range_div m hm g n, List.range_succ, List.flatMap_append, List.flatMap_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    apply flatMap_congr'
    intro k hk
    rw [List.mem_range] at hk
    rw [show (m * n + k) / m = n by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hk, Nat.zero_add],
      show (m * n + k) % m = k by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]]

theorem flatMap_filterMap_range {α : Type} (m : Nat) (G : Nat → Option α) :
    ∀ n, (List.range n).flatMap (fun b => (List.range m).filterMap (fun k => G (m * b + k))) =
      (List.range (m * n)).filterMap G
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_filterMap_range m G n,
      show m * (n + 1) = m * n + m by rw [Nat.mul_succ], List.range_add, List.filterMap_append,
      List.filterMap_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

theorem filterMap_range_lt {α : Type} (N L : Nat) (h : L ≤ N) (g : Nat → α) :
    (List.range N).filterMap (fun k => if k < L then some (g k) else none) = (List.range L).map g := by
  rw [show N = L + (N - L) by omega, List.range_add, List.filterMap_append, List.filterMap_map]
  have e1 : (List.range L).filterMap (fun k => if k < L then some (g k) else none) = (List.range L).map g := by
    rw [← List.filterMap_eq_map]
    apply filterMap_congr'
    intro k hk; rw [List.mem_range] at hk; simp [hk]
  have e2 : (List.range (N - L)).filterMap ((fun k => if k < L then some (g k) else none) ∘ (L + ·)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro k _; simp
  rw [e1, e2, List.append_nil]

theorem chunks_flatten (n : Nat) (l : List Nat) (hl : l.length = 64 * n) : (chunks n l).flatten = l := by
  induction n generalizing l with
  | zero => simp at hl; subst hl; rfl
  | succ n ih =>
    simp only [chunks, List.flatten_cons]
    rw [ih _ (by simp [hl]; omega), List.take_append_drop]

/-! ## Byte receives of a message -/

theorem msgRows_flatMap (M : Msg) (X : Row → List (List Nat)) (hS : X (.start M.id) = []) :
    (msgRows M).flatMap X =
      (List.range (nb M)).flatMap fun b => (List.range 17).flatMap fun j =>
        X (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b)) := by
  rw [msgRows_eq, List.flatMap_map, Nat.add_comm, List.range_succ_eq_map, List.flatMap_cons,
    List.flatMap_map]
  rw [show mrow M 0 = .start M.id from rfl, hS, List.nil_append]
  refine Eq.trans (flatMap_congr' (g := fun k =>
      (fun b j => X (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) (k / 17) (k % 17)) ?_)
    (flatMap_range_div 17 (by decide)
      (fun b j => X (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) (nb M))
  intro k _
  simp only [mrow, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]

theorem msg_recv (M : Msg) :
    (msgRows M).flatMap rowRecvN = (List.range M.bytes.length).map fun p => [M.id, p, M.bytes.getD p 0] := by
  rw [msgRows_flatMap M rowRecvN rfl]
  have hblock : ∀ b, b < nb M → ((List.range 17).flatMap fun j =>
      rowRecvN (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) =
      (List.range 64).filterMap (fun k => (fun kk => if kk < M.bytes.length then
        some [M.id, kk, (ArenaCore.SHA256.pad M.bytes).getD kk 0] else none) (64 * b + k)) := by
    intro b hb
    rw [show 17 = 4 + 13 by rfl, List.range_add, List.flatMap_append, List.flatMap_map]
    have e2 : (List.range 13).flatMap (fun a => rowRecvN (if 4 + a < 16 then .round (4 + a) (blkOf M b)
        else .digest (blkOf M b))) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro j hj
      rw [List.mem_range] at hj
      split
      · simp only [rowRecvN]; rw [if_neg (by omega)]
      · rfl
    rw [e2, List.append_nil]
    have e1 : ((List.range 4).flatMap fun j =>
        rowRecvN (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) =
        (List.range 4).flatMap fun j => (List.range 16).filterMap fun q =>
          (fun k => if 64 * b + k < M.bytes.length then
            some [M.id, 64 * b + k, (blkOf M b).blk.getD k 0] else none) (16 * j + q) := by
      apply flatMap_congr'
      intro j hj
      rw [List.mem_range] at hj
      rw [if_pos (by omega)]
      simp only [rowRecvN, if_pos hj]
      rfl
    rw [e1, flatMap_filterMap_range 16 (fun k => if 64 * b + k < M.bytes.length then
            some [M.id, 64 * b + k, (blkOf M b).blk.getD k 0] else none) 4]
    apply filterMap_congr'
    intro k hk
    rw [List.mem_range] at hk
    simp only
    split
    · rw [blk_getD M b k hb hk]
    · rfl
  have e : ((List.range (nb M)).flatMap fun b => (List.range 17).flatMap fun j =>
      rowRecvN (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) =
      (List.range (nb M)).flatMap fun b => (List.range 64).filterMap (fun k =>
        (fun kk => if kk < M.bytes.length then
          some [M.id, kk, (ArenaCore.SHA256.pad M.bytes).getD kk 0] else none) (64 * b + k)) := by
    apply flatMap_congr'
    intro b hb
    exact hblock b (List.mem_range.mp hb)
  rw [e, flatMap_filterMap_range 64 (fun kk => if kk < M.bytes.length then
          some [M.id, kk, (ArenaCore.SHA256.pad M.bytes).getD kk 0] else none) (nb M),
    filterMap_range_lt _ _ (by have := nb_eq M; omega) (fun kk => [M.id, kk, (ArenaCore.SHA256.pad M.bytes).getD kk 0])]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [pad_getD_data _ _ hk]

end ZkFormal.Sha.Complete
