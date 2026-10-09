import ZkFormal.NearV3.Sched.Link.MemSeg

/-!
# ZkFormal.NearV3.Sched.Link.MemQ — memory consistency restricted to a set of addresses

`mem_chained` / `mem_reads_sim` need `InitOnce` and the time bound for **every** address. The
consistency argument only relates rows of one segment (one address), so both can be restricted
to an address predicate `Q` (stage B step 2: τ's addresses):

* `InitOnceQ Q`: at most one `INIT` message `(a, 0, 0, …)` per address `a` with `Q a`;
* `TimeQ Q`: active memory rows with a `Q` address have `t < 2^29`;
* `memOpsQ Q`: the ops of the non-`INIT` rows on `Q` addresses;
* **`mem_chainedQ`**: `Chained (memOpsQ Q) (memInit …)`;
* **`mem_reads_simQ`**: with `Frame`/`StepOk` on `memOpsQ Q` and the start state = the `INIT`
  values on `Q`, every op on a `Q` address reads the simulation.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- At most one `INIT` message `(a, 0, 0, …)` is sent on `SOP` per address `a` with `Q a`. -/
def InitOnceQ (AP : AirP) (tr : Trace Fp) (pub : List Fp) (Q : Nat → Bool) : Prop :=
  ∀ a : Fp, Q a.toNat = true → (sopSent AP tr pub).countP (fun m => m.take 3 == [a, 0, 0]) ≤ 1

/-- Active memory rows with a `Q` address have times `< 2^29`. -/
def TimeQ (tr : Trace Fp) (tm : Nat) (Q : Nat → Bool) : Prop :=
  ∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 → Q (cv tr tm r Mem.addr) = true →
    cv tr tm r Mem.t < 2 ^ 29

/-- The ops of the non-`INIT` rows on `Q` addresses. -/
def memOpsQ (tr : Trace Fp) (tm : Nat) (Q : Nat → Bool) : List MOp :=
  (memOps tr tm).filter fun o => Q o.a

theorem mem_memOpsQ {tm : Nat} {Q : Nat → Bool} {o : MOp} :
    o ∈ memOpsQ tr tm Q ↔ o ∈ memOps tr tm ∧ Q o.a = true := by
  simp [memOpsQ]

/-- **Segments of `Q` addresses are unique.** -/
theorem mem_seg_uniqueQ (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) {Q : Nat → Bool}
    (hI : InitOnceQ AP tr pub Q) :
    ∀ f1 f2, f1 < tr.height tm → f2 < tr.height tm → cv tr tm f1 Mem.fst = 1 → cv tr tm f2 Mem.fst = 1 →
      Q (cv tr tm f1 Mem.addr) = true → cv tr tm f1 Mem.addr = cv tr tm f2 Mem.addr → f1 = f2 := by
  have hL := mLocal_of hH hM
  intro f1 f2 h1 h2 hf1 hf2 hq he
  apply Classical.byContradiction
  intro hne
  let a := tr.cell tm f1 Mem.addr
  have i1 := Mem.init_row hL h1 hf1
  have i2 := Mem.init_row hL h2 hf2
  have ha2 : tr.cell tm f2 Mem.addr = a := (Mem.cell_eq_of_cv he).symm
  have hc := (List.Perm.countP_eq (fun m => m.take 3 == [a, 0, 0]) (mem_recv_perm hH hM)).symm
  have h2le := hI a hq
  rw [hc, memRecv, List.countP_filterMap] at h2le
  have := two_le_countP (p := fun r => ((if cv tr tm r Mem.act = 1 then some (Mem.opMsg tr tm pub r) else none).map
      (fun m => m.take 3 == [a, 0, 0])).getD false) List.nodup_range
    (List.mem_range.2 h1) (List.mem_range.2 h2) hne
    (by simp [i1.1, i1.2.2.2, a]) (by simp [i2.1, i2.2.2.2, ha2])
  omega

/-- **Time order** on a `Q` address. -/
theorem mem_seg_sortedQ (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    {Q : Nat → Bool} (hT : TimeQ tr tm Q)
    {r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r Mem.act = 1) (hf : cv tr tm r Mem.fst = 0)
    (hq : Q (cv tr tm r Mem.addr) = true) :
    1 ≤ r ∧ cv tr tm r Mem.tp = cv tr tm (r - 1) Mem.t ∧ cv tr tm (r - 1) Mem.t + 1 ≤ cv tr tm r Mem.t := by
  have hL := mLocal_of hH hM
  obtain ⟨h1, ha', hl'⟩ := Mem.seg_back hL hr ha hf
  have e : r - 1 + 1 = r := by omega
  have hn := Mem.row_next hL (r := r - 1) (by omega) ha' hl'
  rw [e] at hn
  have htp : cv tr tm r Mem.tp = cv tr tm (r - 1) Mem.t := hn.2.2.2.2.1
  refine ⟨h1, htp, ?_⟩
  have hprev := hT (r - 1) (by omega) ha' (by rw [← hn.2.2.1]; exact hq)
  have hmem : Mem.iTime ∈ AP.tables[tm]!.interactions := by rw [hM.tab]; exact Mem.iTime_mem
  have hmult : Mem.iTime.multNat tr tm r pub ≠ 0 := mult_iTime hL hr ha hf
  have hy : (Fp.ofNat (cv tr tm r Mem.tp + 1)).toNat = cv tr tm r Mem.tp + 1 := by
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega)]
  rcases cmp_sound_le hH hC hM.lt hr hmem rfl rfl hmult (Mem.iTime_msg tm r)
      (hT r hr ha hq) (by rw [hy]; omega) with ⟨-, h⟩ | ⟨h, -⟩
  · rw [hy] at h; exact (by rw [← htp]; exact h)
  · exact absurd (congrArg Fp.toNat h) (by simp [Fp.toNat_one, Fp.toNat_zero])

/-- **Times strictly increase along a segment of a `Q` address.** -/
theorem mem_seg_timeQ (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    {Q : Nat → Bool} (hT : TimeQ tr tm Q)
    {f r : Nat} (hr : r < tr.height tm)
    (hact : ∀ x, f ≤ x → x ≤ r → cv tr tm x Mem.act = 1)
    (hrest : ∀ x, f < x → x ≤ r → cv tr tm x Mem.fst = 0)
    (hq : ∀ x, f ≤ x → x ≤ r → Q (cv tr tm x Mem.addr) = true) :
    ∀ x y, f ≤ x → x < y → y ≤ r → cv tr tm x Mem.t + (y - x) ≤ cv tr tm y Mem.t := by
  intro x y hx hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    have hs := mem_seg_sortedQ hH hM hC hT (r := y + 1) (by omega) (hact (y + 1) (by omega) hy)
      (hrest (y + 1) (by omega) hy) (hq (y + 1) (by omega) hy)
    simp only [Nat.add_sub_cancel] at hs
    rcases Nat.lt_or_ge x y with h | h
    · have := ih h (by omega); omega
    · have : x = y := by omega
      subst this; omega

theorem memInit_eqQ {tm : Nat} {Q : Nat → Bool}
    (huniq : ∀ f1 f2, f1 < tr.height tm → f2 < tr.height tm → cv tr tm f1 Mem.fst = 1 →
      cv tr tm f2 Mem.fst = 1 → Q (cv tr tm f1 Mem.addr) = true →
      cv tr tm f1 Mem.addr = cv tr tm f2 Mem.addr → f1 = f2)
    {f : Nat} (hf : f < tr.height tm) (hff : cv tr tm f Mem.fst = 1) (hq : Q (cv tr tm f Mem.addr) = true) :
    memInit tr tm (cv tr tm f Mem.addr) = cv tr tm f Mem.v := by
  unfold memInit
  split
  · next f' hfind =>
    have hp := List.find?_some hfind
    have hm := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [huniq f' f hm hf hp.1 hff (by rw [hp.2]; exact hq) hp.2]
  · next hfind =>
    have := (List.find?_eq_none.1 hfind) f (List.mem_range.2 hf)
    simp [hff] at this

/-- **Memory ops on `Q` addresses are chained** from the `INIT` values. -/
theorem mem_chainedQ (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    {Q : Nat → Bool} (hI : InitOnceQ AP tr pub Q) (hT : TimeQ tr tm Q) :
    Chained (memOpsQ tr tm Q) (memInit tr tm) := by
  have hL := mLocal_of hH hM
  have huniq := mem_seg_uniqueQ hH hM hI
  intro o ho
  obtain ⟨ho, hoq⟩ := mem_memOpsQ.1 ho
  obtain ⟨r, hr, ha, hf, rfl⟩ := mem_memOps ho
  simp only at hoq
  obtain ⟨f, hfr, hff, hact, hrest⟩ := Mem.seg_of hL hr ha
  have hfr' : f < r := by
    rcases Nat.lt_or_ge f r with h | h
    · exact h
    · have : f = r := by omega
      subst this; omega
  have hfh : f < tr.height tm := by omega
  have hqf : Q (cv tr tm f Mem.addr) = true := by rw [← (hact r hfr (Nat.le_refl _)).2]; exact hoq
  have hmono := mem_seg_timeQ hH hM hC hT hr (fun x h1 h2 => (hact x h1 h2).1)
    (fun x h1 h2 => (hrest x h1 h2).1) (fun x h1 h2 => by rw [(hact x h1 h2).2]; exact hqf)
  have hbefore : ∀ o'' ∈ memOpsQ tr tm Q, o''.a = cv tr tm r Mem.addr → o''.t < cv tr tm r Mem.t →
      ∃ r'', f < r'' ∧ r'' < r ∧ o''.t = cv tr tm r'' Mem.t := by
    intro o'' ho'' hoa hot
    obtain ⟨ho'', -⟩ := mem_memOpsQ.1 ho''
    obtain ⟨r'', hr'', ha'', hf'', rfl⟩ := mem_memOps ho''
    simp only at hoa hot
    obtain ⟨f'', hf''r, hff'', hact'', hrest''⟩ := Mem.seg_of hL hr'' ha''
    have hqf'' : Q (cv tr tm f'' Mem.addr) = true := by
      rw [← (hact'' r'' hf''r (Nat.le_refl _)).2, hoa]; exact hoq
    have hff : f'' = f := huniq f'' f (by omega) hfh hff'' hff hqf'' (by
      rw [← (hact'' r'' hf''r (Nat.le_refl _)).2, hoa, (hact r hfr (Nat.le_refl _)).2])
    subst hff
    have hfr'' : f'' < r'' := by
      rcases Nat.lt_or_ge f'' r'' with h | h
      · exact h
      · have : f'' = r'' := by omega
        subst this; omega
    refine ⟨r'', hfr'', ?_, rfl⟩
    rcases Nat.lt_or_ge r'' r with h | h
    · exact h
    · exfalso
      rcases Nat.eq_or_lt_of_le h with e | e
      · subst e; omega
      · have := mem_seg_timeQ hH hM hC hT hr'' (fun x h1 h2 => (hact'' x h1 h2).1)
          (fun x h1 h2 => (hrest'' x h1 h2).1)
          (fun x h1 h2 => by rw [(hact'' x h1 h2).2]; exact hqf'') r r'' (by omega) e (Nat.le_refl _)
        omega
  have hs := mem_seg_sortedQ hH hM hC hT hr ha hf hoq
  obtain ⟨-, ha', hl'⟩ := Mem.seg_back hL hr ha hf
  have hn := Mem.row_next hL (r := r - 1) (by omega) ha' hl'
  rw [show r - 1 + 1 = r by omega] at hn
  have hvin : cv tr tm r Mem.vin = cv tr tm (r - 1) Mem.v := hn.2.2.2.1
  rcases Nat.eq_or_lt_of_le (show f ≤ r - 1 by omega) with e | e
  · right
    refine ⟨fun o'' ho'' hoa hot => ?_, ?_⟩
    · obtain ⟨r'', h1, h2, -⟩ := hbefore o'' ho'' hoa hot
      omega
    · show cv tr tm r Mem.vin = memInit tr tm (cv tr tm r Mem.addr)
      rw [hvin, ← e, (hact r hfr (Nat.le_refl _)).2, memInit_eqQ huniq hfh hff hqf]
  · left
    have hf1 := (hrest (r - 1) e (by omega)).1
    have hq1 : Q (cv tr tm (r - 1) Mem.addr) = true := by
      rw [(hact (r - 1) (by omega) (by omega)).2]; exact hqf
    refine ⟨_, mem_memOpsQ.2 ⟨memOps_mem (by omega) ha' hf1, hq1⟩, ?_, ?_, ?_, ?_⟩
    · show cv tr tm (r - 1) Mem.addr = cv tr tm r Mem.addr
      rw [(hact (r - 1) (by omega) (by omega)).2, (hact r hfr (Nat.le_refl _)).2]
    · show cv tr tm (r - 1) Mem.t < cv tr tm r Mem.t
      omega
    · intro o'' ho'' hoa hot
      obtain ⟨r'', h1, h2, ht⟩ := hbefore o'' ho'' hoa hot
      show o''.t ≤ cv tr tm (r - 1) Mem.t
      rw [ht]
      rcases Nat.eq_or_lt_of_le (show r'' ≤ r - 1 by omega) with e' | e'
      · subst e'; exact Nat.le_refl _
      · have := hmono r'' (r - 1) (by omega) e' (by omega); omega
    · exact hvin

/-- **Memory consistency on `Q` addresses.** -/
theorem mem_reads_simQ (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    {Q : Nat → Bool} (hI : InitOnceQ AP tr pub Q) (hT : TimeQ tr tm Q)
    {σ : Nat → Nat → Nat} (hF : Frame (memOpsQ tr tm Q) σ) (hS : StepOk (memOpsQ tr tm Q) σ)
    (h0 : ∀ a, Q a = true → σ 0 a = memInit tr tm a) : ∀ o ∈ memOpsQ tr tm Q, o.vin = σ o.t o.a := by
  -- the simulation patched to the `INIT` values off `Q`
  let σ' : Nat → Nat → Nat := fun t a => if Q a = true then σ t a else memInit tr tm a
  have hF' : Frame (memOpsQ tr tm Q) σ' := fun t a h => by
    simp only [σ']; split
    · exact hF t a h
    · rfl
  have hS' : StepOk (memOpsQ tr tm Q) σ' := fun t h o ho hot => by
    have hq := (mem_memOpsQ.1 ho).2
    have := hS t (fun o2 ho2 h2 => by
      have := h o2 ho2 h2; simp only [σ', (mem_memOpsQ.1 ho2).2, ite_true] at this; exact this) o ho hot
    simp only [σ', hq, ite_true]; exact this
  have h0' : ∀ a, σ' 0 a = memInit tr tm a := fun a => by
    simp only [σ']; split
    · next h => exact h0 a h
    · rfl
  intro o ho
  have := mem_consistent _ _ _ (mem_chainedQ hH hM hC hI hT) hF' hS' h0' o ho
  simp only [σ', (mem_memOpsQ.1 ho).2, ite_true] at this
  exact this

end ZkFormal.NearV3.Sched
