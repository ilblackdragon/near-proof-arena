import ZkFormal.Chacha.Complete.Copy
import ZkFormal.Chacha.Complete.Rows

/-!
# ZkFormal.Chacha.Complete.Bus — the honest environment, multiplicity bits, bus traffic

* `honest_env`: the integer environment of row `r` of the honest trace reads `rowAt r` and
  `rowAt ((r+1) % H)` (all honest cells are `< 2^16 < p`);
* `multBits`: the multiplicity bits `M kk` are `0/1`;
* `count_send` / `count_recv`: the table provides exactly `expected reqs` on `busChacha`
  (each with multiplicity one) and receives nothing.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen
open NearSpecV3

theorem cell_eq (reqs : List Req) (t r c : Nat) :
    (honestTrace reqs).cell t r c = Fp.ofNat (rowCell (rowAt reqs r) c) := rfl

theorem toNat_cell (reqs : List Req) (t r c : Nat) :
    ((honestTrace reqs).cell t r c).toNat = rowCell (rowAt reqs r) c := by
  rw [cell_eq, Fp.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (rowCell_lt _ _) (by decide))

theorem honest_env (reqs : List Req) (t r : Nat) (pub : List Fp) :
    HEnv (tenv (honestTrace reqs) t r pub) (rowAt reqs r)
      (rowAt reqs ((r + 1) % (honestTrace reqs).height t)) :=
  ⟨fun c => toNat_cell reqs t r c, fun c => toNat_cell reqs t _ c⟩

/-! ## Multiplicity bits -/

theorem ofNat_bit {n : Nat} (h : n ≤ 1) : Fp.ofNat n = 0 ∨ Fp.ofNat n = 1 := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem multBits (reqs : List Req) (busChacha t r : Nat) (pub : List Fp) :
    ∀ i ∈ interactions busChacha, ∀ b ∈ i.mult,
      b.eval (honestTrace reqs) t r pub = 0 ∨ b.eval (honestTrace reqs) t r pub = 1 := by
  intro i hi b hb
  obtain ⟨kk, hkk, rfl⟩ := List.mem_map.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have hk := List.mem_range.mp hkk
  show (honestTrace reqs).cell t r (colM kk) = 0 ∨ (honestTrace reqs).cell t r (colM kk) = 1
  rw [cell_eq, rowCell_M _ hk]
  exact ofNat_bit (mflag_le _ _)

/-! ## Messages of an `F` row -/

theorem outW_eq {R : Req} {i : Nat} (hi : i < 16) :
    outW R i = (chachaBlock R.key R.ctr)[i]! := by
  rw [chachaBlock_eq]
  simp [outW, fin, init, hi]

theorem eval_of_zev' {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr} {n : Nat}
    (h : zev (tenv tr t r pub) e = (n : Int)) : e.eval tr t r pub = Fp.ofNat n := by
  rw [eval_eq, h, intCast_ofNat]

/-- The message of output `kk` of an honest `F j` row. -/
theorem msg_F (reqs : List Req) (t r : Nat) (pub : List Fp) {R : Req} {j : Nat}
    (hX : rowAt reqs r = .f R j) (hR : ReqOk R) (hj : j < 4) {kk : Nat} (hk : kk < 4) :
    (outMsg kk).map (fun e => e.eval (honestTrace reqs) t r pub) =
      Sound.chachaMsg R.key R.ctr (4 * kk + j) ((chachaBlock R.key R.ctr)[4 * kk + j]!) := by
  have h := honest_env reqs t r pub
  rw [hX] at h
  unfold outMsg Sound.chachaMsg
  rw [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro q hq
    have hq' := List.mem_range.mp hq
    show (honestTrace reqs).cell t r (colK (q / 2) (q % 2)) = _
    rw [cell_eq, hX, rowCell_K _ (by omega) (Nat.mod_lt _ (by decide))]
    simp only [kWord, if_pos (show q / 2 < 8 by omega), limbN]
  · have hc := hR.2.2.1
    have hw := outW_eq (R := R) (show 4 * kk + j < 16 by omega)
    simp only [List.map_cons, List.map_nil]
    rw [eval_of_zev' (n := R.ctr) (by
          simp only [ctrE, zev_add, zev_smul, zK h (show 8 < 9 by decide) (show 0 < 2 by decide),
            zK h (show 8 < 9 by decide) (show 1 < 2 by decide)]
          simp [kWord, limbN]; omega),
      eval_of_zev' (n := 4 * kk + j) (by rw [idxE, f_selF h hj]; rfl),
      eval_of_zev' (n := (chachaBlock R.key R.ctr)[4 * kk + j]! % 65536) (by
        rw [zX h (by omega : kk < 6) (by decide)]
        simp only [xWord, if_pos hk, hw, limbN]; simp),
      eval_of_zev' (n := (chachaBlock R.key R.ctr)[4 * kk + j]! / 65536 % 65536) (by
        rw [zX h (by omega : kk < 6) (by decide)]
        simp only [xWord, if_pos hk, hw, limbN])]

/-! ## Counting -/

/-- Messages provided by a row. -/
def rowMsgs : Row → List (List Fp)
  | .f R j => fMsgs R j
  | _ => []

theorem foldr_add {α : Type} (g : α → Nat) (acc : Nat) :
    ∀ l : List α, l.foldr (fun i a => g i + a) acc = (l.map g).sum + acc
  | [] => by simp
  | x :: l => by simp [foldr_add g acc l]; omega

theorem count_filter_map {α : Type} (u : Nat → Bool) (g : Nat → α) [BEq α] (m : α) :
    ∀ l : List Nat, ((l.filter u).map g).count m =
      (l.map (fun kk => if u kk = true ∧ (g kk == m) = true then 1 else 0)).sum
  | [] => rfl
  | x :: l => by
    rw [List.filter_cons]
    by_cases hu : u x = true
    · rw [if_pos hu, List.map_cons, List.count_cons, count_filter_map u g m l, List.map_cons,
        List.sum_cons]
      by_cases hg : (g x == m) = true
      · simp only [hu, hg, true_and, if_true]; omega
      · simp only [hu, hg, true_and]; omega
    · rw [if_neg hu, count_filter_map u g m l, List.map_cons, List.sum_cons]
      simp only [hu, Bool.false_eq_true, false_and, if_false, Nat.zero_add]

theorem multNat_M (reqs : List Req) (busChacha t r kk : Nat) (pub : List Fp) (hk : kk < 4) :
    Interaction.multNat { bus := busChacha, mult := [E.c (colM kk)], msg := outMsg kk, send := true }
      (honestTrace reqs) t r pub = mflag (rowAt reqs r) kk := by
  simp only [Interaction.multNat, Interaction.multNat.go]
  show (if (honestTrace reqs).cell t r (colM kk) = 1 then 2 ^ 0 else 0) + 0 = _
  rw [cell_eq, rowCell_M _ hk]
  rcases (show mflag (rowAt reqs r) kk = 0 ∨ mflag (rowAt reqs r) kk = 1 by
    have := mflag_le (rowAt reqs r) kk; omega) with e | e <;> rw [e] <;> decide

/-- Sent count of one row. -/
theorem row_count (reqs : List Req) (hok : ∀ R ∈ reqs, ReqOk R) (busChacha t r : Nat) (pub : List Fp)
    (m : List Fp) :
    ((interactions busChacha).map fun i =>
      if i.bus = busChacha ∧ i.send = true ∧ i.msgVal (honestTrace reqs) t r pub = m then
        i.multNat (honestTrace reqs) t r pub else 0).sum = (rowMsgs (rowAt reqs r)).count m := by
  unfold interactions
  rw [List.map_map]
  rw [List.map_congr_left (g := fun kk =>
      if (outMsg kk).map (fun e => e.eval (honestTrace reqs) t r pub) = m then
        mflag (rowAt reqs r) kk else 0) (fun kk hkk => by
    have hk := List.mem_range.mp hkk
    simp only [Function.comp, Interaction.msgVal, true_and]
    rw [multNat_M reqs busChacha t r kk pub hk])]
  -- by row kind
  have hrow : (∃ R j, ReqOk R ∧ j < 4 ∧ rowAt reqs r = .f R j) ∨ (∀ kk, mflag (rowAt reqs r) kk = 0 ∧
      rowMsgs (rowAt reqs r) = []) := by
    by_cases hin : r < 86 * reqs.length
    · have hR := hok _ (getD_mem reqs (r / 86) (by omega))
      by_cases hf : 82 ≤ r % 86
      · left; refine ⟨_, r % 86 - 82, hR, by omega, ?_⟩
        rw [rowAt_blk _ _ hin, posRow_f _ hf]
      · right; intro kk; rw [rowAt_blk _ _ hin]
        unfold posRow
        split; · exact ⟨rfl, rfl⟩
        split; · exact ⟨rfl, rfl⟩
        rw [if_pos (by omega)]; exact ⟨rfl, rfl⟩
    · right; intro kk; rw [rowAt_pad _ _ (by omega)]; exact ⟨rfl, rfl⟩
  rcases hrow with ⟨R, j, hR, hj, hX⟩ | h0
  · rw [hX]
    show _ = (fMsgs R j).count m
    unfold fMsgs
    rw [count_filter_map]
    apply congrArg
    apply List.map_congr_left
    intro kk hkk
    have hk := List.mem_range.mp hkk
    have hX' := hX
    rw [← hX, msg_F reqs t r pub hX' hR hj hk, hX]
    simp only [mflag]
    by_cases hm : Sound.chachaMsg R.key R.ctr (4 * kk + j) ((chachaBlock R.key R.ctr)[4 * kk + j]!) = m
    · rw [if_pos hm]
      simp only [hm, beq_self_eq_true, and_true]
    · rw [if_neg hm]
      simp only [beq_iff_eq, hm, and_false, if_false]
  · rw [(h0 0).2]
    simp only [(h0 _).1, ite_self]
    rfl

theorem sum_rep0 : ∀ k : Nat, (List.replicate k 0).sum = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, List.sum_cons, sum_rep0 k]

theorem sum_map_zero {α : Type} : ∀ l : List α, (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_map_zero l]

theorem range_map_rowAt (reqs : List Req) (H : Nat) (hH : 86 * reqs.length ≤ H) :
    (List.range H).map (rowAt reqs) = honestRows reqs ++ List.replicate (H - 86 * reqs.length) .pad := by
  apply List.ext_getElem
  · simp [honestRows_length]; omega
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    unfold rowAt
    rw [List.getD_eq_getElem?_getD]
    by_cases hn : n < (honestRows reqs).length
    · rw [List.getElem_append_left hn, List.getElem?_eq_getElem hn]; rfl
    · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega)]
      simp

theorem block_msgs (R : Req) : (blockRows R).flatMap rowMsgs = (List.range 4).flatMap (fMsgs R) := by
  unfold blockRows
  rw [show 86 = 82 + 4 from rfl, List.range_add, List.map_append, List.flatMap_append]
  have h1 : ((List.range 82).map (posRow R)).flatMap rowMsgs = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro X hX
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hX
    have := List.mem_range.mp hk
    unfold posRow
    split; · rfl
    split; · rfl
    first | rfl | (rw [if_pos this]; rfl)
  rw [h1, List.nil_append, List.map_map, List.flatMap_map]
  congr 1
  funext j
  show rowMsgs (posRow R (82 + j)) = _
  rw [posRow_f R (by omega), show 82 + j - 82 = j by omega]
  rfl

theorem rows_msgs (reqs : List Req) : (honestRows reqs).flatMap rowMsgs = expected reqs := by
  unfold honestRows expected
  rw [List.flatMap_assoc]
  simp only [block_msgs]

/-- **Sent traffic**: exactly the expected messages. -/
theorem count_send (reqs : List Req) (hok : ∀ R ∈ reqs, ReqOk R) (busChacha t : Nat) (pub : List Fp)
    (m : List Fp) :
    tableBusCount (interactions busChacha) (honestTrace reqs) t pub busChacha true m =
      (expected reqs).count m := by
  unfold tableBusCount
  have hl := len_le_height reqs t
  generalize (honestTrace reqs).height t = H at hl ⊢
  simp only [foldr_add, Nat.add_zero]
  rw [List.map_congr_left (fun r _ => row_count reqs hok busChacha t r pub m)]
  have e : (List.range H).map (fun r => (rowMsgs (rowAt reqs r)).count m) =
      ((List.range H).map (rowAt reqs)).map (fun X => (rowMsgs X).count m) := by
    rw [List.map_map]; rfl
  rw [e, range_map_rowAt reqs H hl, ← rows_msgs, List.count_flatMap, List.map_append, List.sum_append]
  simp only [List.map_replicate]
  rw [show (rowMsgs Row.pad).count m = 0 from rfl, sum_rep0, Nat.add_zero]
  rfl

/-- **Received traffic**: none. -/
theorem count_recv (reqs : List Req) (busChacha t : Nat) (pub : List Fp) (m : List Fp) :
    tableBusCount (interactions busChacha) (honestTrace reqs) t pub busChacha false m = 0 := by
  unfold tableBusCount
  simp only [foldr_add, Nat.add_zero]
  have h0 : ∀ r, ((interactions busChacha).map fun i =>
      if i.bus = busChacha ∧ i.send = false ∧ i.msgVal (honestTrace reqs) t r pub = m then
        i.multNat (honestTrace reqs) t r pub else 0).sum = 0 := by
    intro r
    rw [List.map_congr_left (g := fun _ => 0) (fun i hi => by
      obtain ⟨kk, -, rfl⟩ := List.mem_map.mp hi
      simp)]
    exact sum_map_zero _
  rw [List.map_congr_left (fun r _ => h0 r)]
  exact sum_map_zero _

end ZkFormal.Chacha.Complete
