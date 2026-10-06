import ZkFormal.Chacha.Link
import ZkFormal.NearV3.Sched.Tables.Cmp
import ZkFormal.NearV3.Sched.Ids

/-!
# ZkFormal.NearV3.Sched.Link.Cmp — the comparator inside a v2 AIR

* `send_matched` (dual of lane v3-chacha's `recv_matched`): if one table `tc` is the only
  receiver on bus `b` and no public segment uses `b`, every active send on `b` equals an active
  receive of `tc`.
* **`cmp_sound`**: every active `SCMP` send `(x, y, b)` of any table with `x, y < 2^29` has
  `b = 1 ∧ y ≤ x` or `b = 0 ∧ x < y`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- **Sends are matched by receives of the unique receiving table.** -/
theorem send_matched {AP : AirP} {pub : List F} {tr : Trace F} (hH : HoldsP AP pub tr)
    {b tc : Nat} (htc : tc < AP.tables.length)
    (honly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus = b → i.send = true)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ b)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = b) (hs : i.send = true)
    (hm : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height tc ∧ ∃ i' ∈ AP.tables[tc]!.interactions, i'.bus = b ∧ i'.send = false ∧
      i'.msgVal tr tc r' pub = i.msgVal tr t r pub ∧ i'.multNat tr tc r' pub ≠ 0 := by
  have hbal := hH.balance b (i.msgVal tr t r pub)
  rw [pubCount_zero (fun seg hseg hbus => absurd hbus (hpub seg hseg)) _,
    pubCount_zero (fun seg hseg hbus => absurd hbus (hpub seg hseg)) _] at hbal
  have hsend : busCount AP.toAir tr pub b true (i.msgVal tr t r pub) ≠ 0 := by
    have h1 := tableBusCount_pos hr hi hm
    rw [hb, hs] at h1
    have h2 := busCount_go_ge tr pub b true (i.msgVal tr t r pub) AP.tables 0 t ht
    simp only [Nat.zero_add] at h2
    unfold busCount; omega
  have hrecv : busCount AP.toAir tr pub b false (i.msgVal tr t r pub) ≠ 0 := by omega
  obtain ⟨t', ht', hc⟩ := busCount_go_pos tr pub b false _ AP.tables 0 hrecv
  simp only [Nat.zero_add] at hc
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := exists_of_tableBusCount hc
  by_cases e : t' = tc
  · subst e; exact ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩
  · have := honly t' ht' e i' hi' hb'; rw [this] at hs'; simp at hs'

end

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- The comparator table is the only receiver on `SCMP`, no public segment uses it. -/
structure CmpOwn (AP : AirP) (tc : Nat) : Prop where
  lt : tc < AP.tables.length
  tab : AP.tables[tc]! = Cmp.table B_SCMP
  only : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus = B_SCMP → i.send = true
  pub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SCMP

/-- **Comparator contract.** -/
theorem cmp_sound (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SCMP) (hs : i.send = true)
    (hm : i.multNat tr t r pub ≠ 0) {x y b : Fp} (hmsg : i.msgVal tr t r pub = [x, y, b])
    (hx : x.toNat < 2 ^ 29) (hy : y.toNat < 2 ^ 29) :
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
  rcases Cmp.cmp_row hL hr' (by rw [cx]; exact hx) (by rw [cy]; exact hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, by rw [← cx, ← cy]; exact h2⟩
    rw [← cb]; unfold cv at h1; rw [← Fp.ofNat_toNat (tr.cell tc r' Cmp.colB), h1]; rfl
  · right
    refine ⟨?_, by rw [← cx, ← cy]; exact h2⟩
    rw [← cb]; unfold cv at h1; rw [← Fp.ofNat_toNat (tr.cell tc r' Cmp.colB), h1]; rfl

end ZkFormal.NearV3.Sched
