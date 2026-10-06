import ZkFormal.Chacha.Shuffle.Complete.Traffic

/-!
# ZkFormal.Chacha.Shuffle.Complete.Count — table-wide bus counts of the honest `shufV3` trace

`count_rows`: for every bus `b`, side and message `m`, `tableBusCount` is the sum of the counts
of `m` in the expected lists of the interactions on `b` with that side (`expectedIn`,
`memSends`, `memRecvs`, `expectedOut`, `expectedGen`, `expectedShuf`).  `memBal`: the
memory bus balances (`memSends` is a permutation of `memRecvs`).
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen

/-! ## List lemmas -/

theorem rev_perm {β : Type} (n : Nat) (f : Nat → β) :
    List.Perm ((List.range n).map (fun e => f (n - 1 - e))) ((List.range n).map f) := by
  have e : (List.range n).map (fun e => n - 1 - e) = (List.range n).reverse := by
    conv => rhs; rw [List.range_eq_range', List.reverse_range']
    apply List.map_congr_left; intro x _; omega
  have : (List.range n).map (fun e => f (n - 1 - e)) = ((List.range n).map (fun e => n - 1 - e)).map f := by
    rw [List.map_map]; rfl
  rw [this, e]
  exact (List.reverse_perm _).map f

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem range_last (n : Nat) (hn : 1 ≤ n) : List.range n = List.range (n - 1) ++ [n - 1] := by
  conv => lhs; rw [show n = (n - 1) + 1 by omega]
  exact List.range_succ

theorem count_ite {β : Type} [BEq β] (p : Prop) [Decidable p] (T : List β) (m : β) :
    (if p then T else []).count m = if p then T.count m else 0 := by
  split <;> simp

theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; omega

theorem sum_map_ite {α : Type} (p : Prop) [Decidable p] (f : α → Nat) (l : List α) :
    (l.map fun x => if p then f x else 0).sum = if p then (l.map f).sum else 0 := by
  by_cases h : p
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    induction l with
    | nil => rfl
    | cons x l ih => simp [ih]

theorem sum_rep0 : ∀ k : Nat, (List.replicate k 0).sum = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, List.sum_cons, sum_rep0 k]

theorem range_map_rowAt (insts : List SInst) (H : Nat) (hH : (honestRows insts).length ≤ H) :
    (List.range H).map (rowAt insts) =
      honestRows insts ++ List.replicate (H - (honestRows insts).length) Row.pad := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← rowAt_full insts (H - (honestRows insts).length) i, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl

/-- Summing a padding-free per-row list over the rows. -/
theorem sum_rows (insts : List SInst) (H : Nat) (hH : (honestRows insts).length ≤ H)
    (T : Row → List (List Fp)) (hT : T .pad = []) (m : List Fp) :
    ((List.range H).map fun r => (T (rowAt insts r)).count m).sum = ((honestRows insts).flatMap T).count m := by
  have e1 : ((List.range H).map fun r => (T (rowAt insts r)).count m) =
      ((List.range H).map (rowAt insts)).map (fun X => (T X).count m) := by
    rw [List.map_map]; rfl
  rw [e1, range_map_rowAt insts H hH, List.map_append, List.sum_append, List.map_replicate, hT,
    List.count_nil, sum_rep0, Nat.add_zero, List.count_flatMap]
  rfl

/-! ## Expected lists from the rows -/

theorem flat_in (insts : List SInst) (s0 : Nat) :
    List.Perm ((honestRowsFrom insts s0).flatMap tIn) (expectedIn insts) := by
  induction insts generalizing s0 with
  | nil => exact List.Perm.refl _
  | cons I Is ih =>
    rw [honestRowsFrom_cons, List.flatMap_append, instRows_flatMap]
    unfold expectedIn; rw [List.flatMap_cons]
    refine List.Perm.append ?_ (ih _)
    have : ((List.range I.L).flatMap fun e => tIn (.pos I s0 (I.L - 1 - e))) =
        (List.range I.L).map (fun e => inMsg I (I.L - 1 - e)) := by
      rw [← List.flatMap_singleton' ((List.range I.L).map _), List.flatMap_map]; rfl
    rw [this]; exact rev_perm I.L (inMsg I)

theorem flat_out (insts : List SInst) (s0 : Nat) :
    List.Perm ((honestRowsFrom insts s0).flatMap tOut) (expectedOut insts) := by
  induction insts generalizing s0 with
  | nil => exact List.Perm.refl _
  | cons I Is ih =>
    rw [honestRowsFrom_cons, List.flatMap_append, instRows_flatMap]
    unfold expectedOut; rw [List.flatMap_cons]
    refine List.Perm.append ?_ (ih _)
    have : ((List.range I.L).flatMap fun e => tOut (.pos I s0 (I.L - 1 - e))) =
        (List.range I.L).map (fun e => outMsg I (I.L - 1 - e)) := by
      rw [← List.flatMap_singleton' ((List.range I.L).map _), List.flatMap_map]; rfl
    rw [this]; exact rev_perm I.L (outMsg I)

theorem flat_gen (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (s0 : Nat) :
    List.Perm ((honestRowsFrom insts s0).flatMap tGen) (expectedGen insts) := by
  induction insts generalizing s0 with
  | nil => exact List.Perm.refl _
  | cons I Is ih =>
    rw [honestRowsFrom_cons, List.flatMap_append, instRows_flatMap]
    unfold expectedGen; rw [List.flatMap_cons]
    refine List.Perm.append ?_ (ih (fun I' h => hok I' (List.mem_cons_of_mem _ h)) _)
    have hL := (hok I List.mem_cons_self).L_pos
    have : ((List.range I.L).flatMap fun e => tGen (.pos I s0 (I.L - 1 - e))) =
        (List.range (I.L - 1)).map (fun e => (fun i => genStep I (i + 1)) (I.L - 1 - 1 - e)) := by
      rw [range_last I.L hL, List.flatMap_append, List.flatMap_singleton]
      simp only [tGen, show I.L - 1 - (I.L - 1) = 0 by omega, show ¬ (1 ≤ 0) by omega, ite_false,
        List.append_nil]
      rw [← List.flatMap_singleton' ((List.range (I.L - 1)).map _), List.flatMap_map]
      apply flatMap_congr'
      intro e he
      have := List.mem_range.mp he
      rw [iteT (by omega), show I.L - 1 - 1 - e + 1 = I.L - 1 - e by omega]
    rw [this]
    exact rev_perm (I.L - 1) (fun i => genStep I (i + 1))

theorem flat_shuf (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (s0 : Nat) :
    (honestRowsFrom insts s0).flatMap tShuf = expectedShuf insts := by
  induction insts generalizing s0 with
  | nil => rfl
  | cons I Is ih =>
    rw [honestRowsFrom_cons, List.flatMap_append, instRows_flatMap]
    unfold expectedShuf; rw [List.map_cons, ← List.singleton_append]
    rw [ih (fun I' h => hok I' (List.mem_cons_of_mem _ h)) _]
    congr 1
    have hL := (hok I List.mem_cons_self).L_pos
    rw [range_last I.L hL, List.flatMap_append, List.flatMap_singleton]
    simp only [tShuf, show I.L - 1 - (I.L - 1) = 0 by omega, ite_true]
    rw [List.flatMap_eq_nil_iff.mpr, List.nil_append]
    intro e he
    have := List.mem_range.mp he
    rw [iteF (by omega)]

theorem sends_split (X : Row) : (rowSendN X).map (List.map Fp.ofNat) = tMinit X ++ tMW2 X := by
  cases X with
  | pad => rfl
  | pos I s q =>
    simp only [rowSendN, sendN, tMinit, tMW2, List.map_cons]
    split <;> rfl

theorem recvs_split (X : Row) : (rowRecvN X).map (List.map Fp.ofNat) = tMR1 X ++ tMR2 X := by
  cases X with
  | pad => rfl
  | pos I s q =>
    simp only [rowRecvN, recvN, tMR1, tMR2, List.map_cons]
    split <;> rfl

theorem count_flatMap_app {α β : Type} [BEq β] (l : List α) (F G : α → List β) (m : β) :
    (l.flatMap F).count m + (l.flatMap G).count m = (l.flatMap fun x => F x ++ G x).count m := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.count_append]; omega

theorem memSends_count (insts : List SInst) (m : List Fp) :
    ((honestRows insts).flatMap tMinit).count m + ((honestRows insts).flatMap tMW2).count m =
      (memSends insts).count m := by
  rw [count_flatMap_app, memSends, List.map_flatMap]
  congr 2; funext X; rw [sends_split]

theorem memRecvs_count (insts : List SInst) (m : List Fp) :
    ((honestRows insts).flatMap tMR1).count m + ((honestRows insts).flatMap tMR2).count m =
      (memRecvs insts).count m := by
  rw [count_flatMap_app, memRecvs, List.map_flatMap]
  congr 2; funext X; rw [recvs_split]

/-! ## Table counts -/

/-- **Bus counts of the honest trace**, for every bus, side and message. -/
theorem count_rows (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : (honestRows insts).length ≤ 2 ^ maxLog) (B : Buses) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount B.is (honestTrace insts) t pub b s m =
      (if B.bin = b ∧ false = s then (expectedIn insts).count m else 0) +
      (if B.mem = b ∧ true = s then (memSends insts).count m else 0) +
      (if B.mem = b ∧ false = s then (memRecvs insts).count m else 0) +
      (if B.bout = b ∧ true = s then (expectedOut insts).count m else 0) +
      (if B.gen = b ∧ false = s then (expectedGen insts).count m else 0) +
      (if B.shuf = b ∧ true = s then (expectedShuf insts).count m else 0) := by
  rw [tableBusCount_eq, List.count_flatMap]
  have hl := len_le_height insts t
  have e : ((List.range ((honestTrace insts).height t)).map
      (List.count m ∘ fun r => rowTraffic B.is (honestTrace insts) t r pub b s)) =
      (List.range ((honestTrace insts).height t)).map fun r =>
        (if B.bin = b ∧ false = s then (tIn (rowAt insts r)).count m else 0) +
        (if B.mem = b ∧ true = s then (tMinit (rowAt insts r)).count m else 0) +
        (if B.mem = b ∧ false = s then (tMR1 (rowAt insts r)).count m else 0) +
        (if B.mem = b ∧ false = s then (tMR2 (rowAt insts r)).count m else 0) +
        (if B.mem = b ∧ true = s then (tMW2 (rowAt insts r)).count m else 0) +
        (if B.bout = b ∧ true = s then (tOut (rowAt insts r)).count m else 0) +
        (if B.gen = b ∧ false = s then (tGen (rowAt insts r)).count m else 0) +
        (if B.shuf = b ∧ true = s then (tShuf (rowAt insts r)).count m else 0) := by
    apply List.map_congr_left
    intro r hr
    simp only [Function.comp, rowTraffic_eq insts hok hrows t r pub (List.mem_range.mp hr) B b s,
      List.count_append, count_ite]
  rw [e]
  generalize (honestTrace insts).height t = H at hl
  simp only [sum_map_add, sum_map_ite]
  rw [sum_rows insts H hl tIn rfl, sum_rows insts H hl tMinit rfl, sum_rows insts H hl tMR1 rfl,
    sum_rows insts H hl tMR2 rfl, sum_rows insts H hl tMW2 rfl, sum_rows insts H hl tOut rfl,
    sum_rows insts H hl tGen rfl, sum_rows insts H hl tShuf rfl]
  have pin : List.Perm ((honestRows insts).flatMap tIn) (expectedIn insts) := flat_in insts 0
  have pout : List.Perm ((honestRows insts).flatMap tOut) (expectedOut insts) := flat_out insts 0
  have pgen : List.Perm ((honestRows insts).flatMap tGen) (expectedGen insts) := flat_gen insts hok 0
  rw [pin.count_eq, pout.count_eq, pgen.count_eq]
  rw [show (honestRows insts).flatMap tShuf = expectedShuf insts from flat_shuf insts hok 0]
  rw [← memSends_count, ← memRecvs_count]
  by_cases h1 : B.mem = b ∧ true = s
  · by_cases h2 : B.mem = b ∧ false = s
    · exact absurd (h1.2.trans h2.2.symm) (by decide)
    · simp only [iteT h1, iteF h2]; omega
  · by_cases h2 : B.mem = b ∧ false = s
    · simp only [iteF h1, iteT h2]; omega
    · simp only [iteF h1, iteF h2]

/-- **The memory bus balances inside the honest table.** -/
theorem memBal (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : (honestRows insts).length ≤ 2 ^ maxLog) (B : Buses) (hB : B.ok) (t : Nat) (pub : List Fp) :
    MemBal B (honestTrace insts) t pub := by
  intro m
  obtain ⟨h1, h2, h3, h4⟩ := hB
  rw [count_rows insts hok hrows, count_rows insts hok hrows]
  have hp : List.Perm (memSends insts) (memRecvs insts) :=
    (rows_perm insts 0 hok).map (List.map Fp.ofNat)
  simp only [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, ite_false,
    and_true, ite_true, Bool.false_eq_true, Bool.true_eq_false, and_false]
  have := hp.count_eq m
  omega

end ZkFormal.Chacha.Shuffle.Complete
