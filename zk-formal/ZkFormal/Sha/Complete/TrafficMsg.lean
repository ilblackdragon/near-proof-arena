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

/-! ## Digest provide of a message -/

theorem map_toNat_ofNat' (m : List Nat) (h : ∀ x ∈ m, x < 256) :
    (m.map UInt8.ofNat).map UInt8.toNat = m := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩
    have := h x (List.mem_cons_self ..)
    simp; omega

theorem beN4_map (x : Nat) :
    (ArenaCore.Bytes.beN 4 x).map UInt8.toNat = (List.range 4).map fun p => x / 2 ^ (8 * (3 - p)) % 2 ^ 8 := by
  simp only [ArenaCore.Bytes.beN, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, UInt8.toNat_ofNat']
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] <;> omega

theorem digest_map (h : List Nat) :
    (h.flatMap fun x => ArenaCore.Bytes.beN 4 x).map UInt8.toNat =
      (List.range (4 * h.length)).map fun p => h.getD (p / 4) 0 / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8 := by
  induction h with
  | nil => rfl
  | cons x t ih =>
    have e1 : (List.range 4).map (fun p => x / 2 ^ (8 * (3 - p)) % 2 ^ 8) =
        (List.range 4).map (fun p => (x :: t).getD (p / 4) 0 / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8) := by
      apply List.map_congr_left
      intro p hp
      rw [List.mem_range] at hp
      rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
      rfl
    have e2 : (List.range (4 * t.length)).map (fun p => t.getD (p / 4) 0 / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8) =
        ((List.range (4 * t.length)).map (4 + ·)).map
          (fun p => (x :: t).getD (p / 4) 0 / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      show _ = (x :: t).getD ((4 + p) / 4) 0 / 2 ^ (8 * (3 - (4 + p) % 4)) % 2 ^ 8
      rw [show (4 + p) / 4 = p / 4 + 1 by omega, show (4 + p) % 4 = p % 4 by omega]
      rfl
    rw [List.flatMap_cons, List.map_append, ih, beN4_map, List.length_cons,
      show 4 * (t.length + 1) = 4 + 4 * t.length by omega, List.range_add, List.map_append, e1, e2]

theorem foldl_all (M : Msg) :
    (msgBlocks M.bytes).foldl ArenaCore.SHA256.compress ArenaCore.SHA256.H0 =
      ArenaCore.SHA256.compress (blkOf M (nb M - 1)).hin (blkOf M (nb M - 1)).blk := by
  have h1 := nb_pos M
  have := hin_succ M (nb M - 1) (by omega)
  rw [show nb M - 1 + 1 = nb M by omega] at this
  rw [← this]
  show _ = ((msgBlocks M.bytes).take (nb M)).foldl _ _
  rw [List.take_of_length_le (l := msgBlocks M.bytes) (i := nb M) (Nat.le_refl _)]

theorem sha_msg (M : Msg) (hM : MOk M) :
    (ArenaCore.sha256 (M.bytes.map UInt8.ofNat)).map UInt8.toNat =
      (List.range 32).map fun p => (blkOf M (nb M - 1)).hout (p / 4) / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8 := by
  rw [Spec.sha256_eq_foldl _ (msgBlocks M.bytes)
    (fun c hc => chunks_len64 _ _ (pad_length _) c hc)
    (by rw [map_toNat_ofNat' _ hM.bytes]; exact (chunks_flatten _ _ (pad_length _)).symm),
    foldl_all M]
  show ((ArenaCore.SHA256.compress _ _).flatMap fun x => ArenaCore.Bytes.beN 4 x).map UInt8.toNat = _
  rw [digest_map, ArenaCore.SHA256.compress_length]
  apply List.map_congr_left
  intro p hp
  rw [List.mem_range] at hp
  rw [compress_getD _ _ (by omega)]

theorem msg_dig (M : Msg) (hM : MOk M) :
    (msgRows M).flatMap rowDigN =
      if M.dmult then [[M.id, M.bytes.length] ++ (ArenaCore.sha256 (M.bytes.map UInt8.ofNat)).map UInt8.toNat]
      else [] := by
  rw [msgRows_flatMap M rowDigN rfl]
  have hblock : ∀ b, ((List.range 17).flatMap fun j =>
      rowDigN (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) =
      rowDigN (.digest (blkOf M b)) := by
    intro b
    rw [List.range_succ, List.flatMap_append]
    have e : (List.range 16).flatMap (fun j =>
        rowDigN (if j < 16 then .round j (blkOf M b) else .digest (blkOf M b))) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro j hj
      rw [List.mem_range] at hj
      rw [if_pos hj]; rfl
    rw [e]
    simp
  rw [flatMap_congr' (fun b _ => hblock b)]
  have h1 := nb_pos M
  rw [show nb M = (nb M - 1) + 1 by omega, List.range_succ, List.flatMap_append]
  have e : (List.range (nb M - 1)).flatMap (fun b => rowDigN (.digest (blkOf M b))) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro b hb
    rw [List.mem_range] at hb
    simp only [rowDigN]
    split
    · next h => exact absurd h.1 (show ¬ (b + 1 = nb M) by omega)
    · rfl
  rw [e, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [rowDigN]
  have hl : (blkOf M (nb M - 1)).idx + 1 = (blkOf M (nb M - 1)).nblk := by
    show nb M - 1 + 1 = nb M; omega
  cases hd : M.dmult
  · rw [if_neg (by rintro ⟨-, h⟩; simp [hd] at h)]; rfl
  · rw [if_pos ⟨hl, by simp [hd]⟩, if_pos rfl]
    simp only [blkOf_id, blkOf_len, blkOf_idx, List.cons.injEq, and_true]
    rw [sha_msg M hM, show 64 * (nb M - 1) + 64 = 64 * nb M by omega,
      Nat.min_eq_left (by have := nb_eq M; omega)]

end ZkFormal.Sha.Complete
