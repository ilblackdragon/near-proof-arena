import ZkFormal.Chacha.Shuffle.Complete.Rows

/-!
# ZkFormal.Chacha.Shuffle.Complete.MemPerm — the honest memory traffic is balanced

Messages `[inst, position, stamp, value]` as lists of naturals.  Row `q` of an instance starting
at row `s` writes `sendN` (the input `[s, q, L, l[q]]`, and on a swap step `[s, js q, q, A_q[q]]`)
and reads `recvN` (`[s, q, lw q q, A_q[q]]`, and on a swap step
`[s, js q, lw q (js q), A_q[js q]]`).

`inst_perm`: per instance, the reads are a permutation of the writes.  Both lists are
duplicate-free and have the same elements: a read of position `x` at time `c` consumes the
write with stamp `lw c x` (the next older access of `x`, `lastW`), whose value is the value read
(`ShuffleSpec.fyBefore_get`); conversely the input write of `x` is consumed by the last read
of `x` and the write of step `w` by the read of `x` just before `w` (`top_read`, `prev_read`).
`rows_perm`: the same for the whole table.
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen

/-- Memory writes of row `q` (instance start `s`). -/
def sendN (I : SInst) (s q : Nat) : List (List Nat) :=
  [s, q, I.L, I.vals.getD q 0] ::
    (if I.isS2 q then [[s, I.js q, q, (I.arr q).getD q 0]] else [])

/-- Memory reads of row `q` (instance start `s`). -/
def recvN (I : SInst) (s q : Nat) : List (List Nat) :=
  [s, q, I.lw q q, (I.arr q).getD q 0] ::
    (if I.isS2 q then [[s, I.js q, I.lw q (I.js q), (I.arr q).getD (I.js q) 0]] else [])

def rowSendN : Row → List (List Nat)
  | .pos I s q => sendN I s q
  | .pad => []

def rowRecvN : Row → List (List Nat)
  | .pos I s q => recvN I s q
  | .pad => []

theorem nodup_flatMap_of {α β : Type} {f : α → List β} :
    ∀ {Q : List α}, Q.Nodup → (∀ q ∈ Q, (f q).Nodup) →
      (∀ q1 ∈ Q, ∀ q2 ∈ Q, q1 ≠ q2 → ∀ a ∈ f q1, ∀ b ∈ f q2, a ≠ b) → (Q.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | q :: Q, hQ, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    have hQ' := List.nodup_cons.mp hQ
    refine ⟨h1 q List.mem_cons_self,
      nodup_flatMap_of hQ'.2 (fun q' h => h1 q' (List.mem_cons_of_mem _ h))
        (fun q1 h1' q2 h2' => h2 q1 (List.mem_cons_of_mem _ h1') q2 (List.mem_cons_of_mem _ h2')), ?_⟩
    intro a ha b hb
    obtain ⟨q', hq', hb⟩ := List.mem_flatMap.mp hb
    exact h2 q List.mem_cons_self q' (List.mem_cons_of_mem _ hq') (fun e => hQ'.1 (e ▸ hq')) a ha b hb

theorem nodup_pair {α : Type} {a b : α} (h : a ≠ b) : [a, b].Nodup := by
  simp [List.nodup_cons, h]

section
variable {I : SInst} (hI : InstOk I) (s : Nat)
include hI

/-- A read of position `x` at time `c`. -/
def RdEv (I : SInst) (c x : Nat) : Prop := c < I.L ∧ (c = x ∨ (I.isS2 c = true ∧ I.js c = x))

omit hI in
theorem rdEv_le {c x : Nat} (h : RdEv I c x) : x ≤ c := by
  rcases h.2 with e | ⟨h1, h2⟩
  · omega
  · have := ((isS2_iff I c).mp h1).2; omega

/-- The value read is that of the next older access. -/
theorem read_val {c x : Nat} (hc : c < I.L) (hx : x ≤ c) :
    (lastW I.js (I.L - 1) c x = none → (I.arr c).getD x 0 = I.vals.getD x 0) ∧
    (∀ q', lastW I.js (I.L - 1) c x = some q' → (I.arr c).getD x 0 = (I.arr q').getD q' 0) := by
  have hL := hI.L_pos
  have hg := fyBefore_get I.js (I.L - 1) I.vals (by have : I.L = I.vals.length := rfl; omega) (hjs hI)
    (q := c) (x := x) (by omega) hx
  unfold SInst.arr
  simp only [List.getD_eq_getElem?_getD]
  constructor
  · intro h; rw [hg, h]
  · intro q' h; rw [hg, h]

theorem write_of_lastW {c x q' : Nat} (h : lastW I.js (I.L - 1) c x = some q') :
    c < q' ∧ q' < I.L ∧ I.isS2 q' = true ∧ I.js q' = x := by
  obtain ⟨a1, a2, a3, a4, -⟩ := lastW_some_spec h
  have := hI.L_pos
  exact ⟨a1, by omega, (isS2_iff I q').mpr ⟨by omega, by omega⟩, a3⟩

/-- Two reads of the same position at different times consume different writes. -/
theorem lw_lt {c1 c2 x : Nat} (h1 : RdEv I c1 x) (h2 : RdEv I c2 x) (hlt : c1 < c2) :
    I.lw c1 x < I.lw c2 x := by
  have hx1 := rdEv_le h1
  have hw : I.isS2 c2 = true ∧ I.js c2 = x := by
    rcases h2.2 with e | e
    · omega
    · exact e
  have hc2 := (isS2_iff I c2).mp hw.1
  have hgt := lw_gt hI h2.1 x
  unfold SInst.lw at hgt ⊢
  cases e : lastW I.js (I.L - 1) c1 x with
  | none =>
    exact absurd ⟨hw.2, by omega⟩ (lastW_none_spec e c2 hlt (by have := h2.1; omega))
  | some q' =>
    obtain ⟨-, -, -, -, a5⟩ := lastW_some_spec e
    have : q' ≤ c2 := by
      apply Nat.le_of_not_lt; intro hq
      exact a5 c2 hlt hq ⟨hw.2, by omega⟩
    show q' < _; omega

/-- The read tuple determines the read. -/
theorem rd_inj {c1 x1 c2 x2 : Nat} (h1 : RdEv I c1 x1) (h2 : RdEv I c2 x2)
    (he : [s, x1, I.lw c1 x1, (I.arr c1).getD x1 0] = [s, x2, I.lw c2 x2, (I.arr c2).getD x2 0]) :
    c1 = c2 ∧ x1 = x2 := by
  simp only [List.cons.injEq] at he
  obtain ⟨-, ex, el, -⟩ := he
  subst ex
  refine ⟨?_, rfl⟩
  rcases Nat.lt_trichotomy c1 c2 with h | h | h
  · have := lw_lt hI h1 h2 h; omega
  · exact h
  · have := lw_lt hI h2 h1 h; omega

/-- From any read of `x`, a read of `x` with no later write (it consumes the input). -/
theorem top_read {x : Nat} : ∀ n c, I.L - c ≤ n → RdEv I c x →
    ∃ c', RdEv I c' x ∧ lastW I.js (I.L - 1) c' x = none := by
  intro n
  induction n with
  | zero => intro c hn hc; have := hc.1; omega
  | succ n ih =>
    intro c hn hc
    cases e : lastW I.js (I.L - 1) c x with
    | none => exact ⟨c, hc, e⟩
    | some q' =>
      obtain ⟨a1, a2, a3, a4⟩ := write_of_lastW hI e
      exact ih q' (by omega) ⟨a2, Or.inr ⟨a3, a4⟩⟩

/-- From a read of `x` before the write of step `w`, the read of `x` consuming that write. -/
theorem prev_read {x w : Nat} (hw : w < I.L) (hw2 : I.isS2 w = true) (hwx : I.js w = x) :
    ∀ n c, w - c ≤ n → RdEv I c x → c < w → ∃ c', RdEv I c' x ∧ lastW I.js (I.L - 1) c' x = some w := by
  have hw' := (isS2_iff I w).mp hw2
  intro n
  induction n with
  | zero => intro c hn _ hc; omega
  | succ n ih =>
    intro c hn hc hcw
    cases e : lastW I.js (I.L - 1) c x with
    | none => exact absurd ⟨hwx, by omega⟩ (lastW_none_spec e w hcw (by omega))
    | some q' =>
      obtain ⟨-, -, -, -, a5⟩ := lastW_some_spec e
      obtain ⟨a1, a2, a3, a4⟩ := write_of_lastW hI e
      have hle : q' ≤ w := by
        apply Nat.le_of_not_lt; intro hq
        exact a5 w hcw hq ⟨hwx, by omega⟩
      by_cases eq : q' = w
      · subst eq; exact ⟨c, hc, e⟩
      · exact ih q' (by omega) ⟨a2, Or.inr ⟨a3, a4⟩⟩ (by omega)

/-! ## One instance -/

omit hI in
theorem mem_recv {a : List Nat} :
    a ∈ (List.range I.L).flatMap (fun e => recvN I s (I.L - 1 - e)) ↔
      ∃ c x, RdEv I c x ∧ a = [s, x, I.lw c x, (I.arr c).getD x 0] := by
  constructor
  · intro h
    obtain ⟨e, he, ha⟩ := List.mem_flatMap.mp h
    have he := List.mem_range.mp he
    unfold recvN at ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact ⟨_, _, ⟨by omega, Or.inl rfl⟩, ha⟩
    · by_cases hS : I.isS2 (I.L - 1 - e) = true
      · rw [iteT hS] at ha
        exact ⟨_, _, ⟨by omega, Or.inr ⟨hS, rfl⟩⟩, List.mem_singleton.mp ha⟩
      · rw [iteF hS] at ha; simp at ha
  · rintro ⟨c, x, ⟨hc, hcx⟩, rfl⟩
    apply List.mem_flatMap.mpr ⟨I.L - 1 - c, List.mem_range.mpr (by omega), ?_⟩
    rw [show I.L - 1 - (I.L - 1 - c) = c by omega]
    unfold recvN
    rcases hcx with rfl | ⟨hS, rfl⟩
    · exact List.mem_cons_self
    · rw [iteT hS]; exact List.mem_cons_of_mem _ List.mem_cons_self

omit hI in
theorem mem_send {a : List Nat} :
    a ∈ (List.range I.L).flatMap (fun e => sendN I s (I.L - 1 - e)) ↔
      (∃ x, x < I.L ∧ a = [s, x, I.L, I.vals.getD x 0]) ∨
      (∃ w, w < I.L ∧ I.isS2 w = true ∧ a = [s, I.js w, w, (I.arr w).getD w 0]) := by
  constructor
  · intro h
    obtain ⟨e, he, ha⟩ := List.mem_flatMap.mp h
    have he := List.mem_range.mp he
    unfold sendN at ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact Or.inl ⟨_, by omega, ha⟩
    · by_cases hS : I.isS2 (I.L - 1 - e) = true
      · rw [iteT hS] at ha
        exact Or.inr ⟨_, by omega, hS, List.mem_singleton.mp ha⟩
      · rw [iteF hS] at ha; simp at ha
  · rintro (⟨x, hx, rfl⟩ | ⟨w, hw, hS, rfl⟩)
    · apply List.mem_flatMap.mpr ⟨I.L - 1 - x, List.mem_range.mpr (by omega), ?_⟩
      rw [show I.L - 1 - (I.L - 1 - x) = x by omega]
      exact List.mem_cons_self
    · apply List.mem_flatMap.mpr ⟨I.L - 1 - w, List.mem_range.mpr (by omega), ?_⟩
      rw [show I.L - 1 - (I.L - 1 - w) = w by omega]
      unfold sendN; rw [iteT hS]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem nodup_recv : ((List.range I.L).flatMap (fun e => recvN I s (I.L - 1 - e))).Nodup := by
  have elem : ∀ e, e < I.L → ∀ a ∈ recvN I s (I.L - 1 - e),
      ∃ x, RdEv I (I.L - 1 - e) x ∧ a = [s, x, I.lw (I.L - 1 - e) x, (I.arr (I.L - 1 - e)).getD x 0] := by
    intro e he a ha
    unfold recvN at ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact ⟨_, ⟨by omega, Or.inl rfl⟩, ha⟩
    · by_cases hS : I.isS2 (I.L - 1 - e) = true
      · rw [iteT hS] at ha
        exact ⟨_, ⟨by omega, Or.inr ⟨hS, rfl⟩⟩, List.mem_singleton.mp ha⟩
      · rw [iteF hS] at ha; simp at ha
  apply nodup_flatMap_of List.nodup_range
  · intro e he
    have he := List.mem_range.mp he
    unfold recvN
    by_cases hS : I.isS2 (I.L - 1 - e) = true
    · rw [iteT hS]
      apply nodup_pair
      intro h
      have := (rd_inj hI s ⟨by omega, Or.inl rfl⟩ ⟨by omega, Or.inr ⟨hS, rfl⟩⟩ h).2
      have := ((isS2_iff I _).mp hS).2
      omega
    · rw [iteF hS]; exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro e1 h1 e2 h2 hne a ha b hb hab
    have h1 := List.mem_range.mp h1; have h2 := List.mem_range.mp h2
    obtain ⟨x1, r1, rfl⟩ := elem e1 h1 a ha
    obtain ⟨x2, r2, rfl⟩ := elem e2 h2 b hb
    have := (rd_inj hI s r1 r2 hab).1
    omega

omit hI in
theorem nodup_send : ((List.range I.L).flatMap (fun e => sendN I s (I.L - 1 - e))).Nodup := by
  have elem : ∀ e, e < I.L → ∀ a ∈ sendN I s (I.L - 1 - e),
      a = [s, I.L - 1 - e, I.L, I.vals.getD (I.L - 1 - e) 0] ∨
      (I.isS2 (I.L - 1 - e) = true ∧
        a = [s, I.js (I.L - 1 - e), I.L - 1 - e, (I.arr (I.L - 1 - e)).getD (I.L - 1 - e) 0]) := by
    intro e he a ha
    unfold sendN at ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact Or.inl ha
    · by_cases hS : I.isS2 (I.L - 1 - e) = true
      · rw [iteT hS] at ha; exact Or.inr ⟨hS, List.mem_singleton.mp ha⟩
      · rw [iteF hS] at ha; simp at ha
  apply nodup_flatMap_of List.nodup_range
  · intro e he
    have he := List.mem_range.mp he
    unfold sendN
    by_cases hS : I.isS2 (I.L - 1 - e) = true
    · rw [iteT hS]
      apply nodup_pair
      intro h
      simp only [List.cons.injEq] at h
      omega
    · rw [iteF hS]; exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro e1 h1 e2 h2 hne a ha b hb hab
    have h1 := List.mem_range.mp h1; have h2 := List.mem_range.mp h2
    subst hab
    rcases elem e1 h1 a ha with e | ⟨-, e⟩ <;> rcases elem e2 h2 a hb with e' | ⟨-, e'⟩ <;>
      (rw [e] at e'; simp only [List.cons.injEq] at e'; omega)

/-- **One instance**: the reads are a permutation of the writes. -/
theorem inst_perm :
    List.Perm ((List.range I.L).flatMap (fun e => sendN I s (I.L - 1 - e)))
      ((List.range I.L).flatMap (fun e => recvN I s (I.L - 1 - e))) := by
  rw [List.perm_ext_iff_of_nodup (nodup_send (I := I) s) (nodup_recv hI s)]
  intro a
  rw [mem_send (I := I) s, mem_recv (I := I) s]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨w, hw, hS, rfl⟩)
    · obtain ⟨c, hc, e⟩ := top_read hI (x := x) _ x (Nat.le_refl _) ⟨hx, Or.inl rfl⟩
      refine ⟨c, x, hc, ?_⟩
      rw [(read_val hI hc.1 (rdEv_le hc)).1 e]
      unfold SInst.lw; rw [e]; rfl
    · have hw' := (isS2_iff I w).mp hS
      obtain ⟨c, hc, e⟩ := prev_read hI hw hS rfl _ (I.js w) (Nat.le_refl _)
        ⟨by omega, Or.inl rfl⟩ hw'.2
      refine ⟨c, I.js w, hc, ?_⟩
      rw [(read_val hI hc.1 (rdEv_le hc)).2 w e]
      unfold SInst.lw; rw [e]; rfl
  · rintro ⟨c, x, hc, rfl⟩
    have hv := read_val hI hc.1 (rdEv_le hc)
    cases e : lastW I.js (I.L - 1) c x with
    | none =>
      left
      refine ⟨x, by have := rdEv_le hc; have := hc.1; omega, ?_⟩
      rw [hv.1 e]; unfold SInst.lw; rw [e]; rfl
    | some q' =>
      right
      obtain ⟨-, a2, a3, a4⟩ := write_of_lastW hI e
      refine ⟨q', a2, a3, ?_⟩
      rw [hv.2 q' e, a4]; unfold SInst.lw; rw [e]; rfl

end

/-! ## The whole table -/

theorem instRows_flatMap {f : Row → List (List Nat)} (I : SInst) (s : Nat) :
    (instRows I s).flatMap f = (List.range I.L).flatMap (fun e => f (.pos I s (I.L - 1 - e))) := by
  unfold instRows; rw [List.flatMap_map]

theorem rows_perm : ∀ (insts : List SInst) (s0 : Nat), (∀ I ∈ insts, InstOk I) →
    List.Perm ((honestRowsFrom insts s0).flatMap rowSendN) ((honestRowsFrom insts s0).flatMap rowRecvN)
  | [], _, _ => List.Perm.refl _
  | I :: Is, s0, hok => by
    rw [honestRowsFrom_cons, List.flatMap_append, List.flatMap_append, instRows_flatMap, instRows_flatMap]
    exact List.Perm.append (inst_perm (hok I List.mem_cons_self) s0)
      (rows_perm Is _ (fun I' h => hok I' (List.mem_cons_of_mem _ h)))

theorem full_perm (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I) (k : Nat) :
    List.Perm ((honestRows insts ++ List.replicate k Row.pad).flatMap rowSendN)
      ((honestRows insts ++ List.replicate k Row.pad).flatMap rowRecvN) := by
  have hp : ∀ f : Row → List (List Nat), f .pad = [] → (List.replicate k Row.pad).flatMap f = [] := by
    intro f hf
    rw [List.flatMap_eq_nil_iff]
    intro x hx
    rw [List.eq_of_mem_replicate hx, hf]
  rw [List.flatMap_append, List.flatMap_append, hp rowSendN rfl, hp rowRecvN rfl, List.append_nil,
    List.append_nil]
  exact rows_perm insts 0 hok

end ZkFormal.Chacha.Shuffle.Complete
