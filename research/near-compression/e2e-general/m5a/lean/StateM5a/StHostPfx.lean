import StateM5a.StHostIf
import StateM5a.FieldRows2
import StateM5a.FieldWsb

/-!
# StateM5a.StHostPfx — B-T3 (finding B2-4): the HOST-fed key run hashes the **trie key**

`storage_write(key)` names the contract key; the working set is keyed by
`TrieKey::ContractData = 0x09 ‖ receiver ‖ 0x2c ‖ key`. `StbH`'s key run is now a prefix run from
the call context followed by the call's bytes (`StHostIf.StbH`): kinds `k0` (`0x09`), `kr` (a
receiver byte, looked up on `CTXB [j − 1, b]`), `kc` (`0x2c`, `CTXL [j − 1]`: its index is the
receiver's length), `kh` (`HOSTB`).

* **`prefix_run`** (decoded rows): if row 0 is not a `HOSTB` row, the kinds follow
  `k0 → kr* → kc → kh*` and the run does not end inside the prefix, and the lookups are answered by
  the receiver `recv` (`kr` at `j` ⇒ `b = recv[j − 1]`, `kc` at `j` ⇒ `j − 1 = |recv|`), then the
  run's bytes are `0x09 :: recv ++ 0x2c :: rest`, the `HOSTB` rows are exactly `j ≥ |recv| + 2`;
* **`stbh_row`** (from `StbH.constraints` on an active row): one kind, `k0 ⇒ j = 0 ∧ b = 9`,
  `kc ⇒ b = 44`, and the kind transitions inside a run;
* why row 0 is not a `HOSTB` row: `StwH` looks up `CTXL [pl − 2]` (so `pl = |recv| + 2 ≥ 2`) and
  its key descriptor starts at `kptr − pl`, so a `HOSTB` row `j` reads `kptr + j − pl`; lane A sends
  the call's `key_len = klen − pl` bytes at `kptr …` only (A-T1 `HostIf`), so `HOSTB` rows are
  `j ≥ pl` — the cross-table step, stated with lane A's contract (open, M6.4).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StHostPfx

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.FieldRows2

/-- A decoded `STBH` row's kind. -/
inductive Kind | k0 | kr | kc | kh
deriving DecidableEq

section Run
variable (n : Nat) (kind : Nat → Kind) (b : Nat → Nat) (recv : List Nat)

/-- The kind transitions of a run and its last row. -/
def Seq : Prop :=
  (∀ j, j + 1 < n → (kind j = .k0 ∨ kind j = .kr) → (kind (j + 1) = .kr ∨ kind (j + 1) = .kc)) ∧
  (∀ j, j + 1 < n → (kind j = .kc ∨ kind j = .kh) → kind (j + 1) = .kh) ∧
  (0 < n → kind (n - 1) ≠ .k0 ∧ kind (n - 1) ≠ .kr)

/-- The row facts and the context lookups. -/
def Lk : Prop :=
  (∀ j, j < n → kind j = .k0 → j = 0 ∧ b j = 9) ∧
  (∀ j, j < n → kind j = .kr → 1 ≤ j ∧ j - 1 < recv.length ∧ b j = recv.getD (j - 1) 0) ∧
  (∀ j, j < n → kind j = .kc → 1 ≤ j ∧ j - 1 = recv.length ∧ b j = 44)

theorem prefix_kinds (hS : Seq n kind) (hL : Lk n kind b recv) (h0 : 0 < n) (hk0 : kind 0 ≠ .kh) :
    recv.length + 2 ≤ n ∧ ∀ j, j < n →
      (j = 0 → kind j = .k0) ∧ (1 ≤ j → j ≤ recv.length → kind j = .kr) ∧
      (j = recv.length + 1 → kind j = .kc) ∧ (recv.length + 2 ≤ j → kind j = .kh) := by
  obtain ⟨s1, s2, s3⟩ := hS
  obtain ⟨l0, lr, lc⟩ := hL
  -- row 0 is the tag row
  have r0 : kind 0 = .k0 := by
    cases h : kind 0 with
    | k0 => rfl
    | kr => have := (lr 0 h0 h).1; omega
    | kc => have := (lc 0 h0 h).1; omega
    | kh => exact absurd h hk0
  -- rows `1 … m` with `m ≤ |recv|`: while the prefix lasts, `kind j ∈ {kr}` for `1 ≤ j ≤ |recv|`
  have pre : ∀ j, j < n → j ≤ recv.length + 1 → kind j = .k0 ∨ kind j = .kr ∨ (kind j = .kc ∧ j = recv.length + 1) := by
    intro j
    induction j with
    | zero => intro _ _; exact .inl r0
    | succ j ih =>
      intro hj hjl
      rcases ih (by omega) (by omega) with h | h | ⟨h, hj'⟩
      · rcases s1 j hj (.inl h) with h' | h'
        · exact .inr (.inl h')
        · exact .inr (.inr ⟨h', by have := (lc _ hj h').2.1; omega⟩)
      · rcases s1 j hj (.inr h) with h' | h'
        · exact .inr (.inl h')
        · exact .inr (.inr ⟨h', by have := (lc _ hj h').2.1; omega⟩)
      · omega
  -- the run reaches the separator
  have hn : recv.length + 2 ≤ n := by
    refine Classical.byContradiction fun hc => ?_
    have hl : n - 1 ≤ recv.length + 1 := by omega
    rcases pre (n - 1) (by omega) hl with h | h | ⟨h, he⟩
    · exact (s3 h0).1 h
    · exact (s3 h0).2 h
    · -- the separator row is the last: `n − 1 = |recv| + 1`, so `n = |recv| + 2`
      omega
  refine ⟨hn, fun j hj => ⟨fun e => e ▸ r0, fun h1 h2 => ?_, fun e => ?_, fun h2 => ?_⟩⟩
  · rcases pre j hj (by omega) with h | h | ⟨h, he⟩
    · have := (l0 j hj h).1; omega
    · exact h
    · omega
  · rcases pre j hj (by omega) with h | h | ⟨h, _⟩
    · have := (l0 j hj h).1; omega
    · have := (lr j hj h).2.1; omega
    · exact h
  · -- after the separator, every row is a `HOSTB` row
    have hsep : kind (recv.length + 1) = .kc := by
      rcases pre (recv.length + 1) (by omega) (by omega) with h | h | ⟨h, _⟩
      · have := (l0 _ (by omega) h).1; omega
      · have := (lr _ (by omega) h).2.1; omega
      · exact h
    have : ∀ k, recv.length + 2 + k < n → kind (recv.length + 2 + k) = .kh := by
      intro k
      induction k with
      | zero => intro hk; exact s2 _ (by omega) (.inl hsep)
      | succ k ih => intro hk; exact s2 _ (by omega) (.inr (ih (by omega)))
    have := this (j - (recv.length + 2)) (by omega)
    rwa [show recv.length + 2 + (j - (recv.length + 2)) = j by omega] at this

/-- **The key run's bytes are the trie key**: `0x09 ‖ receiver ‖ 0x2c ‖ the call's bytes`. -/
theorem prefix_run (hS : Seq n kind) (hL : Lk n kind b recv) (h0 : 0 < n) (hk0 : kind 0 ≠ .kh) :
    recv.length + 2 ≤ n ∧
    (List.range n).map b = [9] ++ recv ++ [44] ++
      (List.range (n - (recv.length + 2))).map (fun i => b (recv.length + 2 + i)) ∧
    ∀ j, j < n → (kind j = .kh ↔ recv.length + 2 ≤ j) := by
  obtain ⟨hn, hk⟩ := prefix_kinds n kind b recv hS hL h0 hk0
  obtain ⟨l0, lr, lc⟩ := hL
  refine ⟨hn, ?_, fun j hj => ⟨fun h => ?_, fun h => (hk j hj).2.2.2 h⟩⟩
  · rw [show n = (recv.length + 2) + (n - (recv.length + 2)) by omega, List.range_add, List.map_append,
      List.map_map, show recv.length + 2 + (n - (recv.length + 2)) - (recv.length + 2) = n - (recv.length + 2) by omega]
    congr 1
    · rw [show recv.length + 2 = (1 + recv.length) + 1 by omega, List.range_succ, List.range_add, List.map_append,
        List.map_append, List.map_map]
      have e0 : (List.range 1).map b = [9] := by
        simp only [List.range_one, List.map_cons, List.map_nil, (l0 0 h0 ((hk 0 h0).1 rfl)).2]
      have er : (List.range recv.length).map (b ∘ (1 + ·)) = recv := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, Function.comp]
        have hr := (lr (1 + i) (by simp at h1; omega) ((hk _ (by simp at h1; omega)).2.1 (by omega) (by simp at h1; omega))).2.2
        rw [hr, show 1 + i - 1 = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
      have ec : b (1 + recv.length) = 44 := (lc _ (by omega) ((hk _ (by omega)).2.2.1 (by omega))).2.2
      rw [e0, er]; simp [ec]
  · refine Classical.byContradiction fun hc => ?_
    rcases Nat.lt_or_ge j 1 with h1 | h1
    · rw [(hk j hj).1 (by omega)] at h; cases h
    · rcases Nat.lt_or_ge j (recv.length + 1) with h2 | h2
      · rw [(hk j hj).2.1 h1 (by omega)] at h; cases h
      · rw [(hk j hj).2.2.1 (by omega)] at h; cases h

end Run

/-! ## The row facts of `StbH` -/

local notation "P" => 2013265921

section Row
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}
  (hc : ∀ e ∈ StbH.constraints, ev tr t r pub e = 0)

theorem mem_x {e : Expr} (h : e ∈ ([.isTransition * StbH.nx "act" * (1 - StbH.c "last") * (StbH.nx "hid" - StbH.c "hid"),
   StbH.c "act" * (StbH.c "hid" - K HID_WRITE) * (StbH.c "hid" - K HID_REMOVE) * (StbH.c "hid" - K HID_WRITE_V),
   bool (StbH.c "k0"), bool (StbH.c "kr"), bool (StbH.c "kc"), bool (StbH.c "kh"),
   StbH.c "act" - (StbH.c "k0" + StbH.c "kr" + StbH.c "kc" + StbH.c "kh"),
   StbH.c "k0" * (StbH.c "b" - K TK_CONTRACT), StbH.c "kc" * (StbH.c "b" - K TK_SEP), StbH.c "k0" * StbH.c "j",
   Expr.isTransition * StbH.nx "act" * (1 - StbH.c "last") * StbH.c "k0" * (StbH.nx "k0" + StbH.nx "kh"),
   Expr.isTransition * StbH.nx "act" * (1 - StbH.c "last") * StbH.c "kr" * (StbH.nx "k0" + StbH.nx "kh"),
   Expr.isTransition * StbH.nx "act" * (1 - StbH.c "last") * StbH.c "kc" * (1 - StbH.nx "kh"),
   Expr.isTransition * StbH.nx "act" * (1 - StbH.c "last") * StbH.c "kh" * (1 - StbH.nx "kh"),
   StbH.c "act" * (StbH.c "hid" - K HID_WRITE) * (StbH.c "hid" - K HID_REMOVE) * (1 - StbH.c "kh"),
   StbH.c "last" * (StbH.c "k0" + StbH.c "kr")] : List Expr)) : e ∈ StbH.constraints :=
  List.mem_append_right _ h

include hc in
/-- **A tag row is row 0 of its run and holds `0x09`; a separator row holds `0x2c`.** -/
theorem stbh_tag (h0 : ev tr t r pub (StbH.c "k0") = 1) :
    ev tr t r pub (StbH.c "j") = 0 ∧ ev tr t r pub (StbH.c "b") = TK_CONTRACT := by
  refine ⟨FieldWsb.wsb_gate h0 (hc (StbH.c "k0" * StbH.c "j") (mem_x (by simp))), ?_⟩
  have := eq_of_sub (FieldWsb.wsb_gate h0 (hc (StbH.c "k0" * (StbH.c "b" - K TK_CONTRACT)) (mem_x (by simp))))
  rw [this, show K TK_CONTRACT = Expr.const TK_CONTRACT from rfl, ev_const]; rfl

include hc in
theorem stbh_sep (h0 : ev tr t r pub (StbH.c "kc") = 1) : ev tr t r pub (StbH.c "b") = TK_SEP := by
  have := eq_of_sub (FieldWsb.wsb_gate h0 (hc (StbH.c "kc" * (StbH.c "b" - K TK_SEP)) (mem_x (by simp))))
  rw [this, show K TK_SEP = Expr.const TK_SEP from rfl, ev_const]; rfl

include hc in
/-- **The last row of a run is not inside the prefix.** -/
theorem stbh_last (hl : ev tr t r pub (StbH.c "last") = 1) :
    ev tr t r pub (StbH.c "k0") = 0 ∧ ev tr t r pub (StbH.c "kr") = 0 := by
  have h := FieldWsb.wsb_gate hl (hc (StbH.c "last" * (StbH.c "k0" + StbH.c "kr")) (mem_x (by simp)))
  have b0 := ev_bool (hc _ (mem_x (by simp)) : ev tr t r pub (bool (StbH.c "k0")) = 0)
  have b1 := ev_bool (hc _ (mem_x (by simp)) : ev tr t r pub (bool (StbH.c "kr")) = 0)
  rw [ev_hadd] at h
  omega

end Row

#print axioms prefix_kinds
#print axioms prefix_run
#print axioms stbh_tag
#print axioms stbh_sep
#print axioms stbh_last

end StateM5a.StHostPfx
