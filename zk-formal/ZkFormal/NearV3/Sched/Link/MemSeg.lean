import ZkFormal.NearV3.Sched.Link.MemBus
import ZkFormal.NearV3.Sched.Spec.MemCons

/-!
# ZkFormal.NearV3.Sched.Link.MemSeg — segments of the memory table inside a v2 AIR

* `cmp_sound_le`: the comparator contract also holds for `y ≤ 2^29` (needed for `y = tp + 1`);
* `Mem.seg_of`: every active row lies in a segment starting at an `INIT` row with the same address;
* **`mem_seg_unique`**: if every address has at most one `INIT` message `(a, 0, 0, …)` sent on
  `SOP` (`InitOnce`), two `INIT` rows have different addresses, and every active row lies in the
  segment of an `INIT` row of its address;
* **`mem_seg_sorted`**: with the comparator (`CmpOwn`) and times `< 2^29` on active rows, a
  non-`INIT` row has `tp = t` of the row above and `tp + 1 ≤ t`; `mem_seg_time`: times strictly
  increase along a segment;
* **`mem_chained`**: the ops of the non-`INIT` rows are `Chained` from the `INIT` values `memInit`,
  so `mem_consistent` applies given `Frame` and `StepOk` (`mem_reads_sim`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

/-! ## The comparator for `y ≤ 2^29` -/

namespace Cmp
open ZkFormal.Chacha.Table.E

theorem cmp_row_le {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : CLocal tr t pub) {r : Nat}
    (hr : r < tr.height t) (hX : cv tr t r colX < 2 ^ 29) (hY : cv tr t r colY ≤ 2 ^ 29) :
    (cv tr t r colB = 1 ∧ cv tr t r colY ≤ cv tr t r colX) ∨
      (cv tr t r colB = 0 ∧ cv tr t r colX < cv tr t r colY) := by
  have hB : cv tr t r colB ≤ 1 := hL.bool hr (by simp [constraints])
  have hD : ∀ j, j < nbits → cv tr t r (colD j) ≤ 1 := fun j hj =>
    hL.bool hr (by
      simp only [constraints, List.mem_append, List.mem_map, List.mem_range, List.mem_cons]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
  have hDlt : numv tr t r colD nbits < 2 ^ nbits := nbits_le_of hD
  have hz := hL.zc hr (e := mainC) (by simp [constraints])
  simp only [mainC, zev_sub, zev_add, zev_mul, zev_c, zev_k, zev_dE, cur_cv] at hz
  rw [show (2 : Nat) ^ nbits = 536870912 from rfl] at hDlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB with h | h <;> rw [h] at hz <;> push_cast at hz
  · have := hz (by omega) (by omega)
    right; exact ⟨h, by omega⟩
  · have := hz (by omega) (by omega)
    left; exact ⟨h, by omega⟩

end Cmp

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **Comparator contract**, `y ≤ 2^29`. -/
theorem cmp_sound_le (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SCMP) (hs : i.send = true)
    (hm : i.multNat tr t r pub ≠ 0) {x y b : Fp} (hmsg : i.msgVal tr t r pub = [x, y, b])
    (hx : x.toNat < 2 ^ 29) (hy : y.toNat ≤ 2 ^ 29) :
    (b = 1 ∧ y.toNat ≤ x.toNat) ∨ (b = 0 ∧ x.toNat < y.toNat) := by
  obtain ⟨r', hr', i', hi', -, -, hmsg', -⟩ := send_matched hH hC.lt hC.only hC.pub ht hr hi hb hs hm
  rw [hC.tab] at hi'
  simp only [Cmp.table, Cmp.interactions, List.mem_singleton] at hi'
  rw [hi', hmsg] at hmsg'
  simp only [Interaction.msgVal, Cmp.msg, List.map_cons, List.map_nil, List.cons.injEq] at hmsg'
  obtain ⟨ex, ey, eb, -⟩ := hmsg'
  have hL : Cmp.CLocal tr tc pub := by
    have := local_of_holdsP hH hC.lt; rw [hC.tab] at this; exact this
  have cx : cv tr tc r' Cmp.colX = x.toNat := by rw [← ex]; rfl
  have cy : cv tr tc r' Cmp.colY = y.toNat := by rw [← ey]; rfl
  have cb : tr.cell tc r' Cmp.colB = b := eb
  rcases Cmp.cmp_row_le hL hr' (by rw [cx]; exact hx) (by rw [cy]; exact hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, by rw [← cx, ← cy]; exact h2⟩
    rw [← cb]; unfold cv at h1; rw [← Fp.ofNat_toNat (tr.cell tc r' Cmp.colB), h1]; rfl
  · right
    refine ⟨?_, by rw [← cx, ← cy]; exact h2⟩
    rw [← cb]; unfold cv at h1; rw [← Fp.ofNat_toNat (tr.cell tc r' Cmp.colB), h1]; rfl

/-! ## Segments -/

namespace Mem

section
variable {tm : Nat}

/-- **Segment of a row.** Every active row `r` lies in a segment `[f, r]` starting at an `INIT`
row `f`; all its rows are active with the address of `f`. -/
theorem seg_of (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r act = 1) :
    ∃ f, f ≤ r ∧ cv tr tm f fst = 1 ∧
      (∀ x, f ≤ x → x ≤ r → cv tr tm x act = 1 ∧ cv tr tm x addr = cv tr tm f addr) ∧
      (∀ x, f < x → x ≤ r → cv tr tm x fst = 0 ∧ cv tr tm (x - 1) lst = 0) := by
  obtain ⟨f, hfr, hff, hact, hrest⟩ := seg_start hL r hr ha
  have hadd : ∀ d, f + d ≤ r → cv tr tm (f + d) addr = cv tr tm f addr := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have hl := (hrest (f + d + 1) (by omega) (by omega)).2
      simp only [Nat.add_sub_cancel] at hl
      have := (row_next hL (r := f + d) (by omega) (hact (f + d) (by omega) (by omega)) hl).2.2.1
      rw [show f + (d + 1) = f + d + 1 by omega, this, ih (by omega)]
  refine ⟨f, hfr, hff, fun x h1 h2 => ⟨hact x h1 h2, ?_⟩, hrest⟩
  have := hadd (x - f) (by omega)
  rwa [show f + (x - f) = x by omega] at this

theorem cell_eq_of_cv {r r' x y : Nat} (h : cv tr tm r x = cv tr tm r' y) :
    tr.cell tm r x = tr.cell tm r' y := Fp.ext h

end

end Mem

/-- At most one `INIT` message `(a, 0, 0, …)` per address `a` is sent on `SOP` (over all tables,
with multiplicity). -/
def InitOnce (AP : AirP) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ a : Fp, (sopSent AP tr pub).countP (fun m => m.take 3 == [a, 0, 0]) ≤ 1

theorem two_le_countP {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → p x = true → p y = true →
      2 ≤ l.countP p
  | [], _, _, _, hx, _, _, _, _ => by simp at hx
  | z :: l, hnd, x, y, hx, hy, hne, px, py => by
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    rcases List.mem_cons.1 hx with ex | ex <;> rcases List.mem_cons.1 hy with ey | ey
    · exact absurd (ex.trans ey.symm) hne
    · have h1 := List.countP_pos_iff.2 ⟨y, ey, py⟩
      have h2 : p z = true := ex ▸ px
      simp only [h2, ↓reduceIte]; omega
    · have h1 := List.countP_pos_iff.2 ⟨x, ex, px⟩
      have h2 : p z = true := ey ▸ py
      simp only [h2, ↓reduceIte]; omega
    · have := two_le_countP hnd.2 ex ey hne px py
      split <;> omega

/-- **Segments are unique per address.** -/
theorem mem_seg_unique (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) (hI : InitOnce AP tr pub) :
    (∀ f1 f2, f1 < tr.height tm → f2 < tr.height tm → cv tr tm f1 Mem.fst = 1 → cv tr tm f2 Mem.fst = 1 →
      cv tr tm f1 Mem.addr = cv tr tm f2 Mem.addr → f1 = f2) ∧
    (∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 →
      ∃ f, f ≤ r ∧ cv tr tm f Mem.fst = 1 ∧
        (∀ x, f ≤ x → x ≤ r → cv tr tm x Mem.act = 1 ∧ cv tr tm x Mem.addr = cv tr tm f Mem.addr) ∧
        (∀ x, f < x → x ≤ r → cv tr tm x Mem.fst = 0 ∧ cv tr tm (x - 1) Mem.lst = 0)) := by
  have hL := mLocal_of hH hM
  refine ⟨fun f1 f2 h1 h2 hf1 hf2 he => ?_, fun r hr ha => Mem.seg_of hL hr ha⟩
  apply Classical.byContradiction
  intro hne
  let a := tr.cell tm f1 Mem.addr
  have i1 := Mem.init_row hL h1 hf1
  have i2 := Mem.init_row hL h2 hf2
  have ha2 : tr.cell tm f2 Mem.addr = a := (Mem.cell_eq_of_cv he).symm
  have hc := (List.Perm.countP_eq (fun m => m.take 3 == [a, 0, 0]) (mem_recv_perm hH hM)).symm
  have h2le := hI a
  rw [hc, memRecv, List.countP_filterMap] at h2le
  have := two_le_countP (p := fun r => ((if cv tr tm r Mem.act = 1 then some (Mem.opMsg tr tm pub r) else none).map
      (fun m => m.take 3 == [a, 0, 0])).getD false) List.nodup_range
    (List.mem_range.2 h1) (List.mem_range.2 h2) hne
    (by simp [i1.1, i1.2.2.2, a]) (by simp [i2.1, i2.2.2.2, ha2])
  omega

/-! ## Time order -/

section
open ZkFormal.Chacha.Table.E

theorem Mem.iTime_msg (tm r : Nat) :
    Mem.iTime.msgVal tr tm r pub = [tr.cell tm r Mem.t, Fp.ofNat (cv tr tm r Mem.tp + 1), 1] := by
  have h1 : (Expr.add (c Mem.tp) (k 1)).eval tr tm r pub = Fp.ofNat (cv tr tm r Mem.tp + 1) :=
    Mem.ev_of (by simp only [zev_add, zev_c, zev_k, cur_cv]; push_cast; rfl)
  have h2 : (k 1).eval tr tm r pub = 1 := by
    rw [Mem.ev_of (v := 1) (by simp only [zev_k])]; rfl
  simp only [Mem.iTime, Interaction.msgVal, List.map_cons, List.map_nil, h1, h2]
  rfl

end

open ZkFormal.Chacha.Table.E in
theorem mult_iTime {tm : Nat} (hL : Mem.MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm)
    (ha : cv tr tm r Mem.act = 1) (hf : cv tr tm r Mem.fst = 0) : Mem.iTime.multNat tr tm r pub ≠ 0 := by
  have hs := (Mem.op_row hL hr ha hf).1
  apply Mem.multNat_ne_of (e := .add (c Mem.isRd) (c Mem.isGr)) rfl
  rw [Mem.ev_of (v := 1) (by simp only [zev_add, zev_c, cur_cv]; push_cast; omega)]
  rfl

/-- **Time order.** A non-`INIT` active row continues the row above (`tp` = its `t`), and
`tp + 1 ≤ t`. -/
theorem mem_seg_sorted (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    (hT : ∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 → cv tr tm r Mem.t < 2 ^ 29)
    {r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r Mem.act = 1) (hf : cv tr tm r Mem.fst = 0) :
    1 ≤ r ∧ cv tr tm r Mem.tp = cv tr tm (r - 1) Mem.t ∧ cv tr tm (r - 1) Mem.t + 1 ≤ cv tr tm r Mem.t := by
  have hL := mLocal_of hH hM
  obtain ⟨h1, ha', hl'⟩ := Mem.seg_back hL hr ha hf
  have e : r - 1 + 1 = r := by omega
  have hn := Mem.row_next hL (r := r - 1) (by omega) ha' hl'
  rw [e] at hn
  have htp : cv tr tm r Mem.tp = cv tr tm (r - 1) Mem.t := hn.2.2.2.2.1
  refine ⟨h1, htp, ?_⟩
  have hprev := hT (r - 1) (by omega) ha'
  have hmem : Mem.iTime ∈ AP.tables[tm]!.interactions := by rw [hM.tab]; exact Mem.iTime_mem
  have hmult : Mem.iTime.multNat tr tm r pub ≠ 0 := mult_iTime hL hr ha hf
  have hy : (Fp.ofNat (cv tr tm r Mem.tp + 1)).toNat = cv tr tm r Mem.tp + 1 := by
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega)]
  rcases cmp_sound_le hH hC hM.lt hr hmem rfl rfl hmult (Mem.iTime_msg tm r)
      (hT r hr ha) (by rw [hy]; omega) with ⟨-, h⟩ | ⟨h, -⟩
  · rw [hy] at h; exact (by rw [← htp]; exact h)
  · exact absurd (congrArg Fp.toNat h) (by simp [Fp.toNat_one, Fp.toNat_zero])

/-- **Times strictly increase along a segment.** -/
theorem mem_seg_time (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    (hT : ∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 → cv tr tm r Mem.t < 2 ^ 29)
    {f r : Nat} (hr : r < tr.height tm)
    (hact : ∀ x, f ≤ x → x ≤ r → cv tr tm x Mem.act = 1)
    (hrest : ∀ x, f < x → x ≤ r → cv tr tm x Mem.fst = 0) :
    ∀ x y, f ≤ x → x < y → y ≤ r → cv tr tm x Mem.t + (y - x) ≤ cv tr tm y Mem.t := by
  intro x y hx hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    have hs := mem_seg_sorted hH hM hC hT (r := y + 1) (by omega) (hact (y + 1) (by omega) hy)
      (hrest (y + 1) (by omega) hy)
    simp only [Nat.add_sub_cancel] at hs
    rcases Nat.lt_or_ge x y with h | h
    · have := ih h (by omega); omega
    · have : x = y := by omega
      subst this; omega

/-! ## Chained ops -/

/-- The ops of the non-`INIT` active memory rows. -/
def memOps (tr : Trace Fp) (tm : Nat) : List MOp :=
  (List.range (tr.height tm)).filterMap fun r =>
    if cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0 then
      some ⟨cv tr tm r Mem.addr, cv tr tm r Mem.t, cv tr tm r Mem.vin, cv tr tm r Mem.v⟩
    else none

/-- The `INIT` value of address `a`: `v` of the (first) `INIT` row of address `a`, 0 if none. -/
def memInit (tr : Trace Fp) (tm : Nat) (a : Nat) : Nat :=
  match (List.range (tr.height tm)).find? (fun f => cv tr tm f Mem.fst == 1 && cv tr tm f Mem.addr == a) with
  | some f => cv tr tm f Mem.v
  | none => 0

theorem memInit_eq {tm : Nat}
    (huniq : ∀ f1 f2, f1 < tr.height tm → f2 < tr.height tm → cv tr tm f1 Mem.fst = 1 →
      cv tr tm f2 Mem.fst = 1 → cv tr tm f1 Mem.addr = cv tr tm f2 Mem.addr → f1 = f2)
    {f : Nat} (hf : f < tr.height tm) (hff : cv tr tm f Mem.fst = 1) :
    memInit tr tm (cv tr tm f Mem.addr) = cv tr tm f Mem.v := by
  unfold memInit
  split
  · next f' hfind =>
    have hp := List.find?_some hfind
    have hm := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [huniq f' f hm hf hp.1 hff hp.2]
  · next hfind =>
    have := (List.find?_eq_none.1 hfind) f (List.mem_range.2 hf)
    simp [hff] at this

theorem mem_memOps {tm : Nat} {o : MOp} (h : o ∈ memOps tr tm) :
    ∃ r, r < tr.height tm ∧ cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0 ∧
      o = ⟨cv tr tm r Mem.addr, cv tr tm r Mem.t, cv tr tm r Mem.vin, cv tr tm r Mem.v⟩ := by
  obtain ⟨r, hr, hm⟩ := List.mem_filterMap.1 h
  by_cases hc : cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0
  · simp only [hc.1, hc.2, and_self, ↓reduceIte, Option.some.injEq] at hm
    exact ⟨r, List.mem_range.1 hr, hc.1, hc.2, hm.symm⟩
  · simp [hc] at hm

theorem memOps_mem {tm r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r Mem.act = 1)
    (hf : cv tr tm r Mem.fst = 0) :
    (⟨cv tr tm r Mem.addr, cv tr tm r Mem.t, cv tr tm r Mem.vin, cv tr tm r Mem.v⟩ : MOp) ∈ memOps tr tm :=
  List.mem_filterMap.2 ⟨r, List.mem_range.2 hr, by simp [ha, hf]⟩

/-- **Memory ops are chained** from the `INIT` values. -/
theorem mem_chained (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    (hI : InitOnce AP tr pub)
    (hT : ∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 → cv tr tm r Mem.t < 2 ^ 29) :
    Chained (memOps tr tm) (memInit tr tm) := by
  have hL := mLocal_of hH hM
  obtain ⟨huniq, hseg⟩ := mem_seg_unique hH hM hI
  intro o ho
  obtain ⟨r, hr, ha, hf, rfl⟩ := mem_memOps ho
  obtain ⟨f, hfr, hff, hact, hrest⟩ := hseg r hr ha
  have hfr' : f < r := by
    rcases Nat.lt_or_ge f r with h | h
    · exact h
    · have : f = r := by omega
      subst this; omega
  have hfh : f < tr.height tm := by omega
  have hmono := mem_seg_time hH hM hC hT hr (fun x h1 h2 => (hact x h1 h2).1)
    (fun x h1 h2 => (hrest x h1 h2).1)
  -- every op of the same address and an earlier time is above `r`, at most at `r − 1`
  have hbefore : ∀ o'' ∈ memOps tr tm, o''.a = cv tr tm r Mem.addr → o''.t < cv tr tm r Mem.t →
      ∃ r'', f < r'' ∧ r'' < r ∧ o''.t = cv tr tm r'' Mem.t := by
    intro o'' ho'' hoa hot
    obtain ⟨r'', hr'', ha'', hf'', rfl⟩ := mem_memOps ho''
    simp only at hoa hot
    obtain ⟨f'', hf''r, hff'', hact'', hrest''⟩ := hseg r'' hr'' ha''
    have hff : f'' = f := huniq f'' f (by omega) hfh hff'' hff (by
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
      · have := mem_seg_time hH hM hC hT hr'' (fun x h1 h2 => (hact'' x h1 h2).1)
          (fun x h1 h2 => (hrest'' x h1 h2).1) r r'' (by omega) e (Nat.le_refl _)
        omega
  have hs := mem_seg_sorted hH hM hC hT hr ha hf
  obtain ⟨-, ha', hl'⟩ := Mem.seg_back hL hr ha hf
  have hn := Mem.row_next hL (r := r - 1) (by omega) ha' hl'
  rw [show r - 1 + 1 = r by omega] at hn
  have hvin : cv tr tm r Mem.vin = cv tr tm (r - 1) Mem.v := hn.2.2.2.1
  rcases Nat.eq_or_lt_of_le (show f ≤ r - 1 by omega) with e | e
  · -- the row above is the `INIT` row: no earlier op of the address
    right
    refine ⟨fun o'' ho'' hoa hot => ?_, ?_⟩
    · obtain ⟨r'', h1, h2, -⟩ := hbefore o'' ho'' hoa hot
      omega
    · show cv tr tm r Mem.vin = memInit tr tm (cv tr tm r Mem.addr)
      rw [hvin, ← e, (hact r hfr (Nat.le_refl _)).2, memInit_eq huniq hfh hff]
  · -- the row above is the previous op
    left
    have hf1 := (hrest (r - 1) e (by omega)).1
    refine ⟨_, memOps_mem (by omega) ha' hf1, ?_, ?_, ?_, ?_⟩
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

/-- **Memory consistency** of the memory table: given a simulation `σ` starting at the `INIT`
values that changes an address only at its ops' times and steps correctly, every op reads `σ`. -/
theorem mem_reads_sim (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    (hI : InitOnce AP tr pub)
    (hT : ∀ r, r < tr.height tm → cv tr tm r Mem.act = 1 → cv tr tm r Mem.t < 2 ^ 29)
    {σ : Nat → Nat → Nat} (hF : Frame (memOps tr tm) σ) (hS : StepOk (memOps tr tm) σ)
    (h0 : ∀ a, σ 0 a = memInit tr tm a) : ∀ o ∈ memOps tr tm, o.vin = σ o.t o.a :=
  mem_consistent _ _ _ (mem_chained hH hM hC hI hT) hF hS h0

end ZkFormal.NearV3.Sched
