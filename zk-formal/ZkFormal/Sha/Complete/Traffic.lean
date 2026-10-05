import ZkFormal.Sha.Complete.TrafficMsg
import ZkFormal.Sha.Complete.MultBits

/-! # Completeness: bus traffic of the honest table -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

/-! ## Counting -/

theorem foldr_inner {α : Type} (is : List α) (X : α → Nat) (acc : Nat) :
    is.foldr (fun i acc' => X i + acc') acc = (is.map X).sum + acc := by
  induction is with
  | nil => simp
  | cons i is ih => simp only [List.foldr_cons, ih, List.map_cons, List.sum_cons]; omega

theorem tableBusCount_eq (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat)
    (s : Bool) (m : List Fp) :
    tableBusCount is tr t pub b s m =
      ((List.range (tr.height t)).map fun r => (is.map fun i =>
        if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0).sum).sum := by
  unfold tableBusCount
  generalize List.range (tr.height t) = rs
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.foldr_cons, foldr_inner, ih, List.map_cons, List.sum_cons]

theorem sum_ite_count {α β : Type} [DecidableEq β] [BEq β] [LawfulBEq β] (l : List α) (v : α → β) (c : α → Prop)
    [DecidablePred c] (m : β) :
    (l.map fun q => if v q = m then (if c q then 1 else 0) else 0).sum =
      (l.filterMap fun q => if c q then some (v q) else none).count m := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, List.filterMap_cons, ih]
    by_cases hc : c q
    · simp only [hc, if_true, List.count_cons, beq_iff_eq]
      split <;> omega
    · simp [hc]

theorem multNat_one (b : Expr) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (msg : List Expr)
    (send : Bool) :
    ({ bus := bus, mult := [b], msg := msg, send := send } : Interaction).multNat tr t r pub =
      if b.eval tr t r pub = 1 then 1 else 0 := by
  show (if b.eval tr t r pub = 1 then 2 ^ 0 else 0) + 0 = _
  split <;> rfl

theorem range_flatMap_rows (L : List Row) (H : Nat) (hH : L.length ≤ H) (X : Row → List (List Nat))
    (hX : X .pad = []) : (List.range H).flatMap (fun r => X (L.getD r .pad)) = L.flatMap X := by
  rw [show H = L.length + (H - L.length) by omega, List.range_add, List.flatMap_append, List.flatMap_map]
  have e2 : (List.range (H - L.length)).flatMap (fun a => X (L.getD (L.length + a) .pad)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro r _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ L.length + r),
      Option.getD_none, hX]
  rw [e2, List.append_nil]
  have e1 : (List.range L.length).map (fun r => L.getD r .pad) = L := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  conv => rhs; rw [← e1]
  rw [List.flatMap_map]

/-! ## One row of the honest trace -/

section
variable (msgs : List Msg) (t r : Nat) (pub : List Fp)

theorem eval_c (c : Nat) : (E.c c).eval (honestTrace msgs) t r pub = Fp.ofNat (rowCell (rowAt msgs r) c) := rfl

theorem eval_of_zev (e : Expr) (n : Nat) (h : zev (henv msgs t r pub) e = (n : Int)) :
    e.eval (honestTrace msgs) t r pub = Fp.ofNat n := by
  rw [eval_honest, h, intCast_ofNat]

theorem ofNat_eq_one (n : Nat) (hn : n ≤ 1) : (Fp.ofNat n = 1) ↔ n = 1 := by
  constructor
  · intro h
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact absurd h (by decide)
    · rfl
  · rintro rfl; rfl

/-- Byte receives of row `r`, as field elements. -/
def recvF (bB _bD : Nat) : List (List Fp) :=
  (List.range 16).filterMap fun q =>
    if (E.c (colF q)).eval (honestTrace msgs) t r pub = 1 then
      some (({ bus := bB, mult := [E.c (colF q)], msg := [E.c colId, posE q, byteE q], send := false } :
        Interaction).msgVal (honestTrace msgs) t r pub)
    else none

/-- Digest provide of row `r`, as field elements. -/
def digF (_bB bD : Nat) : List (List Fp) :=
  if (E.c colDmult).eval (honestTrace msgs) t r pub = 1 then
    [({ bus := bD, mult := [E.c colDmult],
        msg := [E.c colId, E.c colNd] ++ (List.range 32).map digestByteE, send := true } :
      Interaction).msgVal (honestTrace msgs) t r pub]
  else []

theorem fsumC_round (nx : Row) (M : Msg) (b j : Nat) (f lst : Int) (p : Nat → Int) :
    zev (renv (.round j (blkOf M b)) nx f lst p) fSumC =
      if j < 4 then ((min 16 (M.bytes.length - (64 * b + 16 * j)) : Nat) : Int) else 0 := by
  unfold fSumC
  rw [zev_sum, List.map_map]
  have e : ((List.range 16).map ((zev (renv (.round j (blkOf M b)) nx f lst p)) ∘ fun q => E.c (colF q))) =
      (List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int) := by
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    simp only [Function.comp, zev_c, renv_cur, rowCell_round, r_F M b j q hq]
  rw [e]
  split
  · next hj =>
    have e2 : ((List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int)) =
        (List.range 16).map fun q => (((if (64 * b + 16 * j) + q < M.bytes.length then 1 else 0 : Nat)) : Int) := by
      apply List.map_congr_left
      intro q _
      rw [← Nat.add_assoc]; simp [hj]
    rw [e2, count_lt]
  · next hj =>
    have e2 : ((List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int)) =
        (List.range 16).map fun _ => ((0 : Nat) : Int) := by
      apply List.map_congr_left
      intro q _
      simp [hj]
    rw [e2, sum_zero_map]

theorem recvF_eq (hok : MsgsOk msgs) (hr : r < (honestTrace msgs).height t) (bB bD : Nat) :
    recvF msgs t r pub bB bD = (rowRecvN (rowAt msgs r)).map (List.map Fp.ofNat) := by
  have hc := curRow_of_step _ _ (step_at msgs hok t r hr)
  unfold recvF
  have key : ∀ q, q < 16 →
      (if (E.c (colF q)).eval (honestTrace msgs) t r pub = 1 then
        some (({ bus := bB, mult := [E.c (colF q)], msg := [E.c colId, posE q, byteE q], send := false } :
          Interaction).msgVal (honestTrace msgs) t r pub) else none) =
      if rowCell (rowAt msgs r) (colF q) = 1 then
        some [Fp.ofNat (rowCell (rowAt msgs r) colId), (posE q).eval (honestTrace msgs) t r pub,
          (byteE q).eval (honestTrace msgs) t r pub] else none := by
    intro q hq
    have hb1 := rowCell_bool (rowAt msgs r) (colF q) (by unfold colF; omega)
    rw [eval_c]
    by_cases h1 : rowCell (rowAt msgs r) (colF q) = 1
    · rw [if_pos ((ofNat_eq_one _ hb1).2 h1), if_pos h1]; rfl
    · rw [if_neg (fun h => h1 ((ofNat_eq_one _ hb1).1 h)), if_neg h1]
  rw [filterMap_congr' (fun q hq => key q (List.mem_range.mp hq))]
  have hZ : ∀ e : Expr, e.eval (honestTrace msgs) t r pub =
      ((zev (renv (rowAt msgs r) (rowAt msgs ((r + 1) % (honestTrace msgs).height t))
        (if r = 0 then 1 else 0) (if r + 1 = (honestTrace msgs).height t then 1 else 0)
        (fun i => ((pub.getD i 0).toNat : Int))) e : Int) : Fp) := by
    intro e; rw [eval_honest, henv_eq]
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hZ
  generalize (if r = 0 then 1 else 0 : Int) = f at hZ
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst at hZ
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p at hZ
  generalize rowAt msgs r = row at hc hZ ⊢
  have hnone : ∀ (row : Row), (∀ q, q < 16 → rowCell row (colF q) = 0) → rowRecvN row = [] →
      ((List.range 16).filterMap fun q => if rowCell row (colF q) = 1 then
        some [Fp.ofNat (rowCell row colId), (posE q).eval (honestTrace msgs) t r pub,
          (byteE q).eval (honestTrace msgs) t r pub] else none) =
        (rowRecvN row).map (List.map Fp.ofNat) := by
    intro row h0 hrow
    rw [hrow, List.map_nil, List.filterMap_eq_nil_iff]
    intro q hq
    rw [h0 q (List.mem_range.mp hq)]
    rfl
  cases hc with
  | round M b j hM hb hj =>
    by_cases hj4 : j < 4
    · have hrow : rowRecvN (.round j (blkOf M b)) = (List.range 16).filterMap fun q =>
          if 64 * b + (16 * j + q) < M.bytes.length then
            some [M.id, 64 * b + (16 * j + q), (blkOf M b).blk.getD (16 * j + q) 0] else none := by
        simp only [rowRecvN]; rw [if_pos hj4]; rfl
      rw [hrow, List.map_filterMap]
      apply filterMap_congr'
      intro q hq
      rw [List.mem_range] at hq
      rw [rowCell_round, r_F M b j q hq]
      by_cases hk : 64 * b + (16 * j + q) < M.bytes.length
      · have h1 : (if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0) = 1 :=
          if_pos ⟨hj4, hk⟩
        rw [h1, if_pos rfl, if_pos hk, Option.map_some]
        simp only [List.map_cons, List.map_nil, rowCell_round, rc_Id, blkOf_id]
        rw [hZ (posE q), hZ (byteE q), zev_byteE f lst p nx M b j q hM hb hj4 hq,
          blk_getD M b _ hb (by omega), intCast_ofNat]
        have hpos : zev (renv (.round j (blkOf M b)) nx f lst p) (posE q) =
            ((64 * b + (16 * j + q) : Nat) : Int) := by
          simp only [posE, zev_add, zev_sub, zev_c, zev_k, renv_cur, rowCell_round, r_Nd,
            fsumC_round nx M b j f lst p, if_pos hj4]
          omega
        rw [hpos, intCast_ofNat]
      · have h0 : (if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0) = 0 :=
          if_neg (fun h => hk h.2)
        rw [h0, if_neg (by decide), if_neg hk]
        rfl
    · apply hnone
      · intro q hq; rw [rowCell_round, r_F M b j q hq, if_neg (fun h => hj4 h.1)]
      · simp only [rowRecvN]; rw [if_neg hj4]
  | start M hM => exact hnone _ (fun q hq => by rw [rowCell_start, cell_F_start _ q hq]) rfl
  | digest M b hM hb => exact hnone _ (fun q hq => by rw [rowCell_digest, dc_F _ q hq]) rfl
  | pad => exact hnone _ (fun q _ => rfl) rfl

theorem digF_eq (hok : MsgsOk msgs) (hr : r < (honestTrace msgs).height t) (bB bD : Nat) :
    digF msgs t r pub bB bD = (rowDigN (rowAt msgs r)).map (List.map Fp.ofNat) := by
  have hc := curRow_of_step _ _ (step_at msgs hok t r hr)
  unfold digF
  have hb1 := cell_Dmult_le (rowAt msgs r)
  rw [eval_c]
  have hZ : ∀ e : Expr, e.eval (honestTrace msgs) t r pub =
      ((zev (renv (rowAt msgs r) (rowAt msgs ((r + 1) % (honestTrace msgs).height t))
        (if r = 0 then 1 else 0) (if r + 1 = (honestTrace msgs).height t then 1 else 0)
        (fun i => ((pub.getD i 0).toNat : Int))) e : Int) : Fp) := by
    intro e; rw [eval_honest, henv_eq]
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hZ
  generalize (if r = 0 then 1 else 0 : Int) = f at hZ
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst at hZ
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p at hZ
  generalize rowAt msgs r = row at hc hZ hb1 ⊢
  by_cases h1 : rowCell row colDmult = 1
  · rw [if_pos ((ofNat_eq_one _ hb1).2 h1)]
    cases hc with
    | digest M b hM hb =>
      rw [rowCell_digest, d_Dmult] at h1
      have hd : b + 1 = nb M ∧ M.dmult = true := by
        by_cases hn : b + 1 = nb M ∧ M.dmult = true
        · exact hn
        · rw [if_neg hn] at h1; exact absurd h1 (by decide)
      have hrow : rowDigN (.digest (blkOf M b)) =
          [[M.id, min M.bytes.length (64 * b + 64)] ++
            (List.range 32).map fun p => (blkOf M b).hout (p / 4) / 2 ^ (8 * (3 - p % 4)) % 2 ^ 8] := by
        simp only [rowDigN]
        rw [if_pos (show (blkOf M b).idx + 1 = (blkOf M b).nblk ∧ (blkOf M b).dmult = true from hd)]; rfl
      rw [hrow]
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.map_append, List.map_map,
        List.cons.injEq, and_true, List.cons_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [hZ, zev_c, renv_cur, rowCell_digest, dc_Id, intCast_ofNat]; rfl
      · rw [hZ, zev_c, renv_cur, rowCell_digest, d_Nd, intCast_ofNat]
      · apply List.map_congr_left
        intro q hq
        rw [List.mem_range] at hq
        simp only [Function.comp]
        rw [hZ, digestByteE, zev_bits_of _ _ (8 * (3 - q % 4)) 8
          (fun b' => bit ((blkOf M b).hout (q / 4)) (8 * (3 - q % 4) + b'))
          (fun b' hb' => by rw [zev_c, renv_cur, rowCell_digest, dc_St _ _ _ (by omega) (by omega)]),
          nbits_bit, intCast_ofNat]
    | round M b j hM hb hj => rw [rowCell_round, rc_Dmult] at h1; exact absurd h1 (by decide)
    | start M hM => rw [rowCell_start, sc_Dmult] at h1; exact absurd h1 (by decide)
    | pad => exact absurd h1 (by decide)
  · rw [if_neg (fun h => h1 ((ofNat_eq_one _ hb1).1 h))]
    cases hc with
    | digest M b hM hb =>
      rw [rowCell_digest, d_Dmult] at h1
      have hd : ¬ (b + 1 = nb M ∧ M.dmult = true) := fun h => h1 (by rw [if_pos h])
      simp only [rowDigN]
      rw [if_neg (show ¬ ((blkOf M b).idx + 1 = (blkOf M b).nblk ∧ (blkOf M b).dmult = true) from hd)]; rfl
    | _ => rfl

end

/-! ## Assembly -/

theorem count_zero (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) (s : Bool)
    (m : List Fp) (h : ∀ i ∈ is, ¬ (i.bus = b ∧ i.send = s)) : tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  have e : ∀ r, (is.map fun i =>
      if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0) =
      is.map fun _ => 0 := by
    intro r
    apply List.map_congr_left
    intro i hi
    rw [if_neg (fun h' => h i hi ⟨h'.1, h'.2.1⟩)]
  simp only [e]
  have : ∀ (l : List Interaction), (l.map fun _ => (0 : Nat)).sum = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  simp only [this]
  have : ∀ (l : List Nat), (l.map fun _ => (0 : Nat)).sum = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  exact this _

theorem mem_interactions (bB bD : Nat) (i : Interaction) (hi : i ∈ interactions bB bD) :
    (i.bus = bB ∧ i.send = false) ∨ (i.bus = bD ∧ i.send = true) := by
  simp only [interactions, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.mem_nil_iff, or_false] at hi
  rcases hi with ⟨q, _, rfl⟩ | rfl
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

theorem filter_dmult (msgs : List Msg) (x : Msg → List Nat) :
    msgs.flatMap (fun M => if M.dmult then [x M] else []) = (msgs.filter (·.dmult)).map x := by
  induction msgs with
  | nil => rfl
  | cons M rest ih =>
    simp only [List.flatMap_cons, ih, List.filter_cons]
    cases M.dmult <;> simp

theorem trafficStmt : TrafficStmt := by
  intro msgs hok t pub bB bD hne m
  have hm := mok_of msgs hok
  have hlen := len_le_height msgs t
  refine ⟨?_, count_zero _ _ _ _ _ _ _ ?_, ?_, count_zero _ _ _ _ _ _ _ ?_⟩
  · rw [tableBusCount_eq]
    have hrow : ∀ r ∈ List.range ((honestTrace msgs).height t),
        ((interactions bB bD).map fun i =>
          if i.bus = bB ∧ i.send = false ∧ i.msgVal (honestTrace msgs) t r pub = m then
            i.multNat (honestTrace msgs) t r pub else 0).sum =
        ((rowRecvN (rowAt msgs r)).map (List.map Fp.ofNat)).count m := by
      intro r hr
      rw [List.mem_range] at hr
      rw [← recvF_eq msgs t r pub hok hr bB bD]
      unfold interactions recvF
      rw [List.map_append, List.sum_append, List.map_map]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Ne.symm hne, false_and,
        if_false, Nat.add_zero]
      rw [← sum_ite_count]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp, true_and, multNat_one]
    rw [List.map_congr_left hrow]
    have e1 : (fun a => List.count m (List.map (List.map Fp.ofNat) (rowRecvN (rowAt msgs a)))) =
        List.count m ∘ (fun a => List.map (List.map Fp.ofNat) (rowRecvN (rowAt msgs a))) := rfl
    rw [e1, ← List.count_flatMap, ← List.map_flatMap]
    unfold rowAt
    rw [range_flatMap_rows _ _ hlen _ rfl]
    unfold honestRows
    rw [List.flatMap_assoc, flatMap_congr' (fun M _ => msg_recv M)]
    rfl
  · intro i hi ⟨h1, h2⟩
    rcases mem_interactions bB bD i hi with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h4] at h2; exact absurd h2 (by decide)
    · exact hne (h1.symm.trans h3)
  · rw [tableBusCount_eq]
    have hrow : ∀ r ∈ List.range ((honestTrace msgs).height t),
        ((interactions bB bD).map fun i =>
          if i.bus = bD ∧ i.send = true ∧ i.msgVal (honestTrace msgs) t r pub = m then
            i.multNat (honestTrace msgs) t r pub else 0).sum =
        ((rowDigN (rowAt msgs r)).map (List.map Fp.ofNat)).count m := by
      intro r hr
      rw [List.mem_range] at hr
      rw [← digF_eq msgs t r pub hok hr bB bD]
      unfold interactions digF
      rw [List.map_append, List.sum_append, List.map_map]
      have e0 : ((List.range 16).map ((fun i =>
          if i.bus = bD ∧ i.send = true ∧ i.msgVal (honestTrace msgs) t r pub = m then
            i.multNat (honestTrace msgs) t r pub else 0) ∘ fun q =>
          ({ bus := bB, mult := [E.c (colF q)], msg := [E.c colId, posE q, byteE q], send := false } :
            Interaction))).sum = 0 := by
        have : ∀ (l : List Nat), (l.map fun _ => (0 : Nat)).sum = 0 := by
          intro l; induction l with
          | nil => rfl
          | cons _ _ ih => simp [ih]
        rw [List.map_congr_left (g := fun _ => 0) (fun q _ => by
          simp only [Function.comp]; rw [if_neg (fun h => hne h.1)])]
        exact this _
      rw [e0, Nat.zero_add]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, true_and, multNat_one,
        Nat.add_zero]
      split
      · next h1 =>
        split
        · rw [List.count_cons, List.count_nil, if_pos (beq_iff_eq.mpr h1)]
        · rfl
      · next h1 =>
        split
        · rw [List.count_cons, List.count_nil, if_neg (fun h => h1 (beq_iff_eq.mp h))]
        · rfl
    rw [List.map_congr_left hrow]
    have e1 : (fun a => List.count m (List.map (List.map Fp.ofNat) (rowDigN (rowAt msgs a)))) =
        List.count m ∘ (fun a => List.map (List.map Fp.ofNat) (rowDigN (rowAt msgs a))) := rfl
    rw [e1, ← List.count_flatMap, ← List.map_flatMap]
    unfold rowAt
    rw [range_flatMap_rows _ _ hlen _ rfl]
    unfold honestRows
    rw [List.flatMap_assoc, flatMap_congr' (fun M hM => msg_dig M (hm M hM)), filter_dmult]
    rfl
  · intro i hi ⟨h1, h2⟩
    rcases mem_interactions bB bD i hi with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hne (h3.symm.trans h1)
    · rw [h4] at h2; exact absurd h2 (by decide)

end ZkFormal.Sha.Complete
