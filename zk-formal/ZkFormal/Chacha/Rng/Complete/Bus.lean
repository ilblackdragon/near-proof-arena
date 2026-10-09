import ZkFormal.Chacha.Rng.Complete.Cons

/-!
# ZkFormal.Chacha.Rng.Complete.Bus — the honest environment, multiplicity bits, bus traffic

* `honest_env`: the integer environment of row `r` of the honest trace reads `rowAt r` and
  `rowAt ((r+1) % H)` (all honest cells are `< 2^30 < p`);
* `multBits`: the multiplicity columns `a`, `acc` are `0/1`;
* `count_*`: the table receives exactly `expectedWords` on `busChacha` (one word per draw)
  and provides exactly `expectedGen` on `busGen` (one result per call), nothing else.
-/

namespace ZkFormal.Chacha.Rng.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table ZkFormal.Chacha.Rng.Gen
open NearSpecV3

theorem cell_eq (calls : List Call) (t r c : Nat) :
    (honestTrace calls).cell t r c = Fp.ofNat (rowCell (rowAt calls r) c) := rfl

theorem toNat_cell (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t r c : Nat) :
    ((honestTrace calls).cell t r c).toNat = rowCell (rowAt calls r) c := by
  rw [cell_eq, Fp.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (rowCell_lt (valid_rowAt calls hok r) c) (by decide))

theorem honest_env (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t r : Nat) (pub : List Fp) :
    HEnv (tenv (honestTrace calls) t r pub) (rowAt calls r)
      (rowAt calls ((r + 1) % (honestTrace calls).height t)) :=
  ⟨fun c => toNat_cell calls hok t r c, fun c => toNat_cell calls hok t _ c⟩

/-! ## Multiplicity bits -/

theorem ofNat_bit {v : Nat} (h : v ≤ 1) : Fp.ofNat v = 0 ∨ Fp.ofNat v = 1 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem multBits (calls : List Call) (busChacha busGen t r : Nat) (pub : List Fp) :
    ∀ i ∈ interactions busChacha busGen, ∀ b ∈ i.mult,
      b.eval (honestTrace calls) t r pub = 0 ∨ b.eval (honestTrace calls) t r pub = 1 := by
  intro i hi b hb
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb
  · show (honestTrace calls).cell t r colA = 0 ∨ (honestTrace calls).cell t r colA = 1
    rw [cell_eq]; exact ofNat_bit (rowCell_bool _ (by decide))
  · show (honestTrace calls).cell t r colAcc = 0 ∨ (honestTrace calls).cell t r colAcc = 1
    rw [cell_eq]; exact ofNat_bit (rowCell_bool _ (by decide))

/-! ## Messages -/

theorem eval_nat {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr} {v : Nat}
    (h : zev (tenv tr t r pub) e = (v : Int)) : e.eval tr t r pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

theorem keyMsg_eval (calls : List Call) (t r : Nat) (pub : List Fp) {C : Call} {d : Nat}
    (hX : rowAt calls r = .draw C d) :
    keyMsg.map (fun e => e.eval (honestTrace calls) t r pub) =
      (List.range 16).map (fun q => Fp.ofNat ((C.key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) % 65536)) := by
  unfold keyMsg
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  have hq' := List.mem_range.mp hq
  show (honestTrace calls).cell t r (colK (q / 2) (q % 2)) = _
  rw [cell_eq, hX]
  show Fp.ofNat (drawCell C d _) = _
  rw [g_K (g := drawCell C d) (fun _ => rfl) (by omega) (Nat.mod_lt _ (by decide))]
  rfl

section
open ZkFormal.Chacha.Table.E

/-- The `busChacha` message of a draw row. -/
theorem msg_recv (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t r : Nat) (pub : List Fp)
    {C : Call} {d : Nat} (hX : rowAt calls r = .draw C d) :
    (keyMsg ++ [c colCtr, idxE, c colVlo, c colVhi]).map (fun e => e.eval (honestTrace calls) t r pub) =
      wordMsg C d := by
  have h := honest_env calls hok t r pub
  rw [hX] at h
  have hg : ∀ x, (tenv (honestTrace calls) t r pub).cur x = drawCell C d x := h.cur
  unfold wordMsg Sound.chachaMsg
  rw [List.map_append, keyMsg_eval calls t r pub hX]
  congr 1
  simp only [List.map_cons, List.map_nil]
  rw [eval_nat (v := kOf C d / 16) (by rw [zev_c, hg, g_ctr (g := drawCell C d) (fun _ => rfl)]),
    eval_nat (v := kOf C d % 16) (by rw [idxE, znumC, gn_idx hg]),
    eval_nat (v := vlo C d) (by rw [zev_c, hg, g_vlo (g := drawCell C d) (fun _ => rfl)]),
    eval_nat (v := vhi C d) (by rw [zev_c, hg, g_vhi (g := drawCell C d) (fun _ => rfl)])]
  rfl

/-- The `busGen` message of the last draw row of a call. -/
theorem msg_gen (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (t r : Nat) (pub : List Fp)
    {C : Call} {d : Nat} (hX : rowAt calls r = .draw C d) (hd : d + 1 = nd C) :
    (keyMsg ++ [c colKs, nE, m2E, .add kE (k 1)]).map (fun e => e.eval (honestTrace calls) t r pub) =
      genOut C := by
  have h := honest_env calls hok t r pub
  rw [hX] at h
  have hv := valid_rowAt calls hok r
  rw [hX] at hv
  have hC : CallOk C := hv.1
  have hg : ∀ x, (tenv (honestTrace calls) t r pub).cur x = drawCell C d x := h.cur
  have hm := m2_last hC
  rw [show nd C - 1 = d by omega] at hm
  unfold genOut genMsg
  rw [List.map_append, keyMsg_eval calls t r pub hX]
  congr 1
  simp only [List.map_cons, List.map_nil]
  rw [eval_nat (v := C.kstart) (by rw [zev_c, hg, g_ks (g := drawCell C d) (fun _ => rfl)]),
    eval_nat (v := C.n) (by rw [nE, znumC, gn_N hg hC.2.2.2.1]),
    eval_nat (v := m2 C d) (by rw [m2E, znumC, gn_M2 hg hC.2.2.2.1]),
    eval_nat (v := kOf C d + 1) (by
      rw [zev_add, kE, zev_add, zev_smul, zev_c, hg, g_ctr (g := drawCell C d) (fun _ => rfl), idxE,
        znumC, gn_idx hg, zev_k]
      have := Nat.div_add_mod (kOf C d) 16
      omega),
    hm.1, hm.2]

theorem multNat_c {tr : Trace Fp} {t r : Nat} {pub : List Fp} (x bus : Nat) (msg : List Expr)
    (send : Bool) {v : Nat} (h : tr.cell t r x = Fp.ofNat v) (hv : v ≤ 1) :
    Interaction.multNat { bus := bus, mult := [c x], msg := msg, send := send } tr t r pub = v := by
  simp only [Interaction.multNat, Interaction.multNat.go]
  show (if tr.cell t r x = 1 then 2 ^ 0 else 0) + 0 = v
  rw [h]
  rcases (show v = 0 ∨ v = 1 by omega) with e | e <;> subst e <;> decide

end

/-! ## Counting -/

/-- Messages received on `busChacha` by a row. -/
def rowRecv : Row → List (List Fp)
  | .draw C d => [wordMsg C d]
  | .pad => []

/-- Messages provided on `busGen` by a row. -/
def rowGen : Row → List (List Fp)
  | .draw C d => if d + 1 = nd C then [genOut C] else []
  | .pad => []

theorem count_single (a m : List Fp) : [a].count m = if a = m then 1 else 0 := by
  rw [List.count_cons, List.count_nil]
  by_cases h : a = m <;> simp [h]

/-- One row's contribution to `tableBusCount`. -/
theorem row_sum (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (busChacha busGen t r : Nat)
    (pub : List Fp) (b : Nat) (send : Bool) (m : List Fp) :
    ((interactions busChacha busGen).map fun i =>
      if i.bus = b ∧ i.send = send ∧ i.msgVal (honestTrace calls) t r pub = m then
        i.multNat (honestTrace calls) t r pub else 0).sum =
    (if busChacha = b ∧ false = send then (rowRecv (rowAt calls r)).count m else 0) +
    (if busGen = b ∧ true = send then (rowGen (rowAt calls r)).count m else 0) := by
  have hv := valid_rowAt calls hok r
  simp only [interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  generalize hX : rowAt calls r = X at hv
  cases X with
  | pad =>
    rw [multNat_c (v := 0) _ _ _ _ (by rw [cell_eq, hX]; rfl) (by omega),
      multNat_c (v := 0) _ _ _ _ (by rw [cell_eq, hX]; rfl) (by omega)]
    simp [rowRecv, rowGen]
  | draw C d =>
    have hA : (honestTrace calls).cell t r colA = Fp.ofNat 1 := by
      rw [cell_eq, hX]; show Fp.ofNat (drawCell C d colA) = _
      rw [g_a (g := drawCell C d) (fun _ => rfl)]
    have hAcc : (honestTrace calls).cell t r colAcc = Fp.ofNat (accOf C d) := by
      rw [cell_eq, hX]; show Fp.ofNat (drawCell C d colAcc) = _
      rw [g_acc (g := drawCell C d) (fun _ => rfl)]
    rw [multNat_c (v := 1) _ _ _ _ hA (by omega),
      multNat_c (v := accOf C d) _ _ _ _ hAcc (by unfold accOf; split <;> omega)]
    simp only [Interaction.msgVal]
    simp only [msg_recv calls hok t r pub hX]
    simp only [rowRecv, rowGen, count_single]
    congr 1
    · by_cases h1 : busChacha = b ∧ false = send
      · rw [if_pos h1]; by_cases h2 : wordMsg C d = m
        · rw [if_pos ⟨h1.1, h1.2, h2⟩, if_pos h2]
        · rw [if_neg (fun h => h2 h.2.2), if_neg h2]
      · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1⟩)]
    · by_cases hd : d + 1 = nd C
      · simp only [msg_gen calls hok t r pub hX hd]
        simp only [accOf, if_pos hd, count_single]
        by_cases h1 : busGen = b ∧ true = send
        · rw [if_pos h1]; by_cases h2 : genOut C = m
          · rw [if_pos ⟨h1.1, h1.2, h2⟩, if_pos h2]
          · rw [if_neg (fun h => h2 h.2.2), if_neg h2]
        · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1⟩)]
      · simp [accOf, hd]

theorem foldr_add {α : Type} (g : α → Nat) (acc : Nat) :
    ∀ l : List α, l.foldr (fun i a => g i + a) acc = (l.map g).sum + acc
  | [] => by simp
  | x :: l => by simp [foldr_add g acc l]; omega

theorem range_map_rowAt (calls : List Call) (H : Nat) (hH : (honestRows calls).length ≤ H) :
    (List.range H).map (rowAt calls) =
      honestRows calls ++ List.replicate (H - (honestRows calls).length) Row.pad := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← rowAt_full calls (H - (honestRows calls).length) i, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl

theorem flatMap_single {α β : Type} (f : α → β) : ∀ l : List α, l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | x :: l => by simp [flatMap_single f l]

theorem pads_nil (f : Row → List (List Fp)) (hf : f .pad = []) (k : Nat) :
    (List.replicate k Row.pad).flatMap f = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro x hx
  rw [List.eq_of_mem_replicate hx, hf]

theorem rows_recv (calls : List Call) : (honestRows calls).flatMap rowRecv = expectedWords calls := by
  unfold honestRows expectedWords
  rw [List.flatMap_assoc]
  congr 1
  funext C
  unfold callRows
  rw [List.flatMap_map]
  exact flatMap_single (wordMsg C) _

theorem call_gen {C : Call} (hC : CallOk C) : (callRows C).flatMap rowGen = [genOut C] := by
  obtain ⟨t, ht, -⟩ := call_facts hC
  unfold callRows
  rw [ht, List.range_succ, List.map_append, List.flatMap_append]
  have h1 : ((List.range t).map (Row.draw C)).flatMap rowGen = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro X hX
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hX
    have := List.mem_range.mp hd
    simp only [rowGen, ht]
    rw [if_neg (by omega)]
  rw [h1, List.nil_append]
  simp [rowGen, ht]

theorem rows_gen (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) :
    (honestRows calls).flatMap rowGen = expectedGen calls := by
  induction calls with
  | nil => rfl
  | cons C cs ih =>
    rw [honestRows_cons, List.flatMap_append, call_gen (hok C List.mem_cons_self),
      ih (fun C' h => hok C' (List.mem_cons_of_mem _ h))]
    rfl

theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; omega

theorem sum_rep0 : ∀ k : Nat, (List.replicate k 0).sum = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, List.sum_cons, sum_rep0 k]

/-- `tableBusCount` as a sum of per-row contributions. -/
theorem count_rows (calls : List Call) (hok : ∀ C ∈ calls, CallOk C) (busChacha busGen t : Nat)
    (pub : List Fp) (b : Nat) (send : Bool) (m : List Fp) :
    tableBusCount (interactions busChacha busGen) (honestTrace calls) t pub b send m =
      (if busChacha = b ∧ false = send then (expectedWords calls).count m else 0) +
      (if busGen = b ∧ true = send then (expectedGen calls).count m else 0) := by
  unfold tableBusCount
  have hl := len_le_height calls t
  generalize (honestTrace calls).height t = H at hl ⊢
  simp only [foldr_add, Nat.add_zero]
  rw [List.map_congr_left (fun r _ => row_sum calls hok busChacha busGen t r pub b send m)]
  have e : ∀ (f : Row → List (List Fp)), (f .pad = []) →
      ((List.range H).map fun r => (f (rowAt calls r)).count m).sum =
        ((honestRows calls).flatMap f).count m := by
    intro f hf
    have e1 : ((List.range H).map fun r => (f (rowAt calls r)).count m) =
        ((List.range H).map (rowAt calls)).map (fun X => (f X).count m) := by
      rw [List.map_map]; rfl
    rw [e1, range_map_rowAt calls H hl, List.map_append, List.sum_append, List.map_replicate,
      hf, List.count_nil, sum_rep0, Nat.add_zero, List.count_flatMap]
    rfl
  rw [sum_map_add]
  by_cases h1 : busChacha = b ∧ false = send
  · simp only [if_pos h1]; rw [e rowRecv rfl, rows_recv]
    by_cases h2 : busGen = b ∧ true = send
    · simp only [if_pos h2]; rw [e rowGen rfl, rows_gen calls hok]
    · simp only [if_neg h2]; rw [sum_map_zero']
  · simp only [if_neg h1]; rw [sum_map_zero']
    by_cases h2 : busGen = b ∧ true = send
    · simp only [if_pos h2]; rw [e rowGen rfl, rows_gen calls hok]
    · simp only [if_neg h2]; rw [sum_map_zero']

end ZkFormal.Chacha.Rng.Complete
