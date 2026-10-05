import ZkFormal.Near.Link.MemTime
import ZkFormal.Near.Link.Sha

/-!
# ZkFormal.Near.Link.Mem — offline memory checking on `MEM`

Each receipt reads the latest earlier write of its slot (`tprev_eq`), the
`acct` table's final read gets the last write (`tlast_eq`), and the payloads
agree (`mem_read`, `mem_final`).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem getD_lt {l : List Nat} (h : ∀ y ∈ l, y < P) (i : Nat) : l.getD i 0 < P := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp; unfold P; omega
  | some y => exact h y (List.mem_of_getElem? hi)

/-- The slot of receipt `r`. -/
def ksl (rs : RcptVs) (r : Nat) : Nat := (rs.getD r default).kslot

theorem ksl_eq {rs : RcptVs} {r : Nat} (hr : r < rs.length) : ksl rs r = rs[r].kslot := by
  simp [ksl, List.getD_eq_getElem?_getD, hr]

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem rcpt_wf_at {r : Nat} (hr : r < rs.length) : ∃ a b c, rs[r].Wf r a b c := by
  obtain ⟨toks, -, -, hw, -⟩ := rcptWf_at h.rcpt
  exact ⟨_, _, _, hw r hr⟩

theorem mem_perm : (memW (publicOf c) rs as).Perm (memR (publicOf c) rs as) := by
  have hp := perm h (b := B_MEM) (by decide) (by decide)
  rw [nearSends_mem, nearRecvs_mem] at hp
  have hrl := rs_length_le h
  have hraw : ∀ {r} (hr : r < rs.length) {y}, y ∈ rs[r].raw → y < P := fun hr y hy =>
    h.rcpt.canon _ (List.getElem_mem hr) y hy
  have hpre : ∀ a ∈ as, ∀ y ∈ a.pre, y < P := fun a ha y hy => h.acct.canon a ha y (by simp [hy])
  have hpost : ∀ a ∈ as, ∀ y ∈ a.post, y < P := fun a ha y hy => h.acct.canon a ha y (by simp [hy])
  have hlane : ∀ a ∈ as, ∀ (l : List Nat), (∀ y ∈ l, y < P) → ∀ i, ∀ y ∈ acctLane a l i, y < P := by
    intro a ha l hl i y hy
    simp only [acctLane, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact getD_lt hl i
    · exact getD_lt (hpre a ha) _
    · split
      · exact getD_lt (hpre a ha) _
      · unfold P; omega
  apply perm_nat _ _ hp
  · intro m hm
    rcases mem_memW.mp hm with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
    · obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
      intro y hy
      simp only [wrMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact w.small.1
      · unfold P; omega
      · unfold P; omega
      · have := getD_lt (l := rs[r].aft) (fun y hy => by have := w.aft8 y hy; unfold P; omega) i
        exact this
      · exact getD_lt (fun y hy => hraw hr (by simp [RcptV.raw, hy])) i
      · exact getD_lt (fun y hy => hraw hr (by simp [RcptV.raw, hy])) i
    · intro y hy
      simp only [awMsg, List.cons_append, List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact (h.acct.len a ha).2.2.1
      · unfold P; omega
      · unfold P; omega
      · exact hlane a ha _ (hpre a ha) i y hy
  · intro m hm
    rcases mem_memR hm with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
    · obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
      intro y hy
      simp only [rdMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact w.small.1
      · exact w.small.2
      · unfold P; omega
      all_goals exact getD_lt (fun y hy => hraw hr (by simp [RcptV.raw, hy])) i
    · intro y hy
      simp only [arMsg, List.cons_append, List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact (h.acct.len a ha).2.2.1
      · exact (h.acct.len a ha).2.2.2
      · unfold P; omega
      · exact hlane a ha _ (hpost a ha) i y hy

theorem memR_nodup : (memR (publicOf c) rs as).Nodup :=
  (mem_perm h).nodup_iff.mp (memW_nodup _ _ _ (vslot h).1)

theorem read_in_W {m : Msg} (hm : m ∈ memR (publicOf c) rs as) : m ∈ memW (publicOf c) rs as :=
  (mem_perm h).mem_iff.mpr hm

/-- Writes are determined by their key `(k, t, i)`. -/
theorem memW_key {m₁ m₂ : Msg} (h₁ : m₁ ∈ memW (publicOf c) rs as) (h₂ : m₂ ∈ memW (publicOf c) rs as)
    (hk : m₁.take 3 = m₂.take 3) : m₁ = m₂ := by
  have hnd := (vslot h).1
  rcases mem_memW.mp h₁ with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩ <;>
  rcases mem_memW.mp h₂ with ⟨r', hr', i', hi', rfl⟩ | ⟨a', ha', i', hi', rfl⟩
  · simp only [wrMsg, List.take, List.cons.injEq, and_true] at hk
    obtain ⟨-, e1, rfl⟩ := hk
    have : r = r' := by omega
    subst this; rfl
  · simp [wrMsg, awMsg, List.take] at hk
  · simp [wrMsg, awMsg, acctLane, List.take] at hk
  · simp only [awMsg, acctLane, List.cons_append, List.take, List.cons.injEq, and_true] at hk
    obtain ⟨e1, -, rfl⟩ := hk
    have := (acctOf_eq hnd ha).symm.trans (e1 ▸ acctOf_eq hnd ha')
    simp only [Option.some.injEq] at this; subst this; rfl

/-- Distinct receipts read different messages. -/
theorem rd_ne {r r' : Nat} (hr : r < rs.length) (hr' : r' < rs.length) (hne : r ≠ r') :
    rdMsg rs[r] 0 ≠ rdMsg rs[r'] 0 := by
  intro he
  have hnd := memR_nodup h
  unfold memR at hnd; rw [rcptRecvs_mem, List.nodup_append] at hnd
  have := Sound.flatMap_disj (fun p : RcptV × Nat => (List.range 16).map (rdMsg p.1 ·))
    (rs.zip (List.range rs.length)) r r' (rs[r], r) (rs[r'], r') (rdMsg rs[r] 0) hnd.1 hne
    (by rw [List.getElem?_eq_some_iff]; refine ⟨by simp [hr], ?_⟩; rw [List.getElem_zip]; simp)
    (by rw [List.getElem?_eq_some_iff]; refine ⟨by simp [hr'], ?_⟩; rw [List.getElem_zip]; simp)
    (List.mem_map.mpr ⟨0, by simp, rfl⟩)
  exact this (List.mem_map.mpr ⟨0, by simp, he.symm⟩)

theorem rd_ne_ar {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) :
    rdMsg rs[r] 0 ≠ arMsg a 0 := by
  intro he
  have hnd := memR_nodup h
  unfold memR at hnd; rw [List.nodup_append] at hnd
  refine hnd.2.2 _ ?_ _ ?_ he
  · rw [rcptRecvs_mem]
    exact List.mem_flatMap.mpr ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩, List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
  · rw [acctRecvs_mem]; exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨0, by simp, rfl⟩⟩

/-- A write time of slot `k`: `0`, or `r' + 1` for a receipt `r'` writing `k`. -/
theorem read_time {k t : Nat} {m : Msg} (hm : m ∈ memW (publicOf c) rs as) (hk : m.take 3 = [k, t, 0]) :
    t = 0 ∨ (∃ r', r' < rs.length ∧ ksl rs r' = k ∧ t = r' + 1) := by
  rcases mem_memW.mp hm with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · simp only [wrMsg, List.take, List.cons.injEq, and_true] at hk
    exact .inr ⟨r, hr, by rw [ksl_eq hr]; exact hk.1, hk.2.1.symm⟩
  · simp only [awMsg, acctLane, List.cons_append, List.take, List.cons.injEq, and_true] at hk
    exact .inl hk.2.1.symm

/-- **Each receipt reads the last earlier write of its slot.** -/
theorem tprev_eq : ∀ r (hr : r < rs.length), rs[r].tprev = lastW (ksl rs) rs[r].kslot r := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
    have hle := w.tprev_le
    have hin := read_in_W h (rd_mem_memR (pub := publicOf c) (as := as) hr (i := 0) (by decide))
    have htime := read_time h hin (k := rs[r].kslot) (t := rs[r].tprev) rfl
    have htL : rs[r].tprev ≤ lastW (ksl rs) rs[r].kslot r := by
      rcases htime with e | ⟨r', hr', hk, e⟩
      · omega
      · rw [e]; exact le_lastW _ _ r r' (by omega) hk
    apply Classical.byContradiction; intro hne
    have hlt' : rs[r].tprev < lastW (ksl rs) rs[r].kslot r := Nat.lt_of_le_of_ne htL hne
    rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, hr0, hk0, e⟩
    · omega
    obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (ksl rs) rs[r].kslot rs[r].tprev r0 (by omega) hk0
    have hr1 : r1 < rs.length := by omega
    have hL1 : lastW (ksl rs) rs[r].kslot r1 = rs[r].tprev := by
      apply lastW_eq_of _ _ _ r1 e1 e4
      rcases htime with e | ⟨r', -, hk, e⟩
      · exact .inl e
      · exact .inr ⟨by omega, by rw [e]; exact hk⟩
    have ht1 : rs[r1].tprev = rs[r].tprev := by
      rw [ih r1 (by omega) hr1, ← ksl_eq hr1, e3, hL1]
    have hin1 := read_in_W h (rd_mem_memR (pub := publicOf c) (as := as) hr1 (i := 0) (by decide))
    have hkey : (rdMsg rs[r] 0).take 3 = (rdMsg rs[r1] 0).take 3 := by
      simp only [rdMsg, List.take]; rw [ht1, ← ksl_eq hr1, e3]
    exact rd_ne h hr hr1 (by omega) (memW_key h hin hin1 hkey)

/-- **The acct table's final read gets the last write.** -/
theorem tlast_eq {a : AcctV} (ha : a ∈ as) : a.tlast = lastW (ksl rs) a.k rs.length := by
  have hin := read_in_W h (ar_mem_memR (pub := publicOf c) (rs := rs) ha (i := 0) (by decide))
  have htime := read_time h hin (k := a.k) (t := a.tlast) (by simp [arMsg, acctLane, List.take])
  have htL : a.tlast ≤ lastW (ksl rs) a.k rs.length := by
    rcases htime with e | ⟨r', hr', hk, e⟩
    · omega
    · rw [e]; exact le_lastW _ _ _ r' hr' hk
  apply Classical.byContradiction; intro hne
  have hlt' := Nat.lt_of_le_of_ne htL hne
  rcases lastW_cases (ksl rs) a.k rs.length with e | ⟨r0, hr0, hk0, e⟩
  · omega
  obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (ksl rs) a.k a.tlast r0 (by omega) hk0
  have hr1 : r1 < rs.length := by omega
  have hL1 : lastW (ksl rs) a.k r1 = a.tlast := by
    apply lastW_eq_of _ _ _ r1 e1 e4
    rcases htime with e | ⟨r', -, hk, e⟩
    · exact .inl e
    · exact .inr ⟨by omega, by rw [e]; exact hk⟩
  have ht1 : rs[r1].tprev = a.tlast := by
    rw [tprev_eq h r1 hr1, ← ksl_eq hr1, e3, hL1]
  have hin1 := read_in_W h (rd_mem_memR (pub := publicOf c) (as := as) hr1 (i := 0) (by decide))
  have hkey : (rdMsg rs[r1] 0).take 3 = (arMsg a 0).take 3 := by
    simp only [rdMsg, arMsg, acctLane, List.cons_append, List.take]; rw [ht1, ← ksl_eq hr1, e3]
  exact rd_ne_ar h hr1 ha (memW_key h hin1 hin hkey)

/-- The payload of a receipt's read. -/
theorem mem_read {r : Nat} (hr : r < rs.length) {i : Nat} (hi : i < 16) :
    (lastW (ksl rs) rs[r].kslot r = 0 → ∃ a ∈ as, a.k = rs[r].kslot ∧ rdMsg rs[r] i = awMsg a i) ∧
    (∀ r0, lastW (ksl rs) rs[r].kslot r = r0 + 1 →
      ∃ hr0 : r0 < rs.length, r0 < r ∧ rs[r0].kslot = rs[r].kslot ∧ rdMsg rs[r] i = wrMsg rs[r0] r0 i) := by
  have hin := read_in_W h (rd_mem_memR (pub := publicOf c) (as := as) hr hi)
  have ht := tprev_eq h r hr
  have hle := lastW_le (ksl rs) rs[r].kslot r
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_memW.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · simp only [rdMsg, wrMsg, List.cons.injEq] at he; omega
    · refine ⟨a, ha, ?_, ?_⟩
      · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; exact he.1.symm
      · rw [he]; simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; rw [he.2.2.1]
  · rcases mem_memW.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · have he' := he
      simp only [rdMsg, wrMsg, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      refine ⟨hr', by omega, he'.1.symm, ?_⟩
      rw [he, he'.2.2.1]
    · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; omega

/-- The payload of the acct table's final read. -/
theorem mem_final {a : AcctV} (ha : a ∈ as) {i : Nat} (hi : i < 16) :
    (lastW (ksl rs) a.k rs.length = 0 → arMsg a i = awMsg a i) ∧
    (∀ r0, lastW (ksl rs) a.k rs.length = r0 + 1 →
      ∃ hr0 : r0 < rs.length, rs[r0].kslot = a.k ∧ arMsg a i = wrMsg rs[r0] r0 i) := by
  have hin := read_in_W h (ar_mem_memR (pub := publicOf c) (rs := rs) ha hi)
  have ht := tlast_eq h ha
  have hnd := (vslot h).1
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_memW.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega
    · have hk : a.k = b.k := by
        simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; exact he.1
      have := (acctOf_eq hnd ha).symm.trans (hk ▸ acctOf_eq hnd hb)
      simp only [Option.some.injEq] at this; subst this
      rw [he]; simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he
      rw [he.2.2.1]
  · rcases mem_memW.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · have he' := he
      simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      refine ⟨hr', he'.1.symm, ?_⟩
      rw [he]; rw [he'.2.2.1]
    · simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega

end Hyp

end Link

end ZkFormal.Near
