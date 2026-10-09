import ZkFormal.NearV3.Sched.Link.Cmp
namespace ZkFormal.NearV3.Candidates.ProcComparatorSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.NearV3.Sched
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- The comparator table is the only receiver on `SCMP`, no public segment uses it. -/
structure Own (AP : AirP) (tc bus : Nat) : Prop where
  lt : tc < AP.tables.length
  tab : AP.tables[tc]! = Cmp.table bus
  only : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus = bus → i.send = true
  pub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ bus

/-- **Comparator contract.** -/
theorem sound (hH : HoldsP AP pub tr) {tc bus : Nat} (hC : Own AP tc bus)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = bus) (hs : i.send = true)
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

/-- The prior-order bus uses the same checked comparator contract. Operand
bounds remain explicit until authenticated range providers discharge them. -/
theorem prior_ge (hH : HoldsP AP pub tr) {tc : Nat} (hC : Own AP tc 69)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus=69) (hs : i.send=true)
    (hm : i.multNat tr t r pub≠0) {x y : Fp}
    (hmsg : i.msgVal tr t r pub=[x,y,1])
    (hx : x.toNat<2^29) (hy : y.toNat<2^29) : y.toNat≤x.toNat := by
  rcases sound hH hC ht hr hi hb hs hm hmsg hx hy with h|h
  · exact h.2
  · have hne:(1 : Fp)≠0 := by decide +kernel
    exact False.elim (hne h.1)

end ZkFormal.NearV3.Candidates.ProcComparatorSound
