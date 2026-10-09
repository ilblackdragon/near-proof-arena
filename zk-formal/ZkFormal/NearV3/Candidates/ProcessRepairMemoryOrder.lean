import ZkFormal.NearV3.Candidates.ProcessRepairMemoryNatural
import ZkFormal.Near.Link.Mem
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Link

structure Context (pub:List Fp) (rs:RcptVs) (as:List AcctV):Prop where
  permutation:(memW pub rs as).Perm (memR pub rs as)
  unique:(as.map (·.k)).Nodup
  previous:∀r,(hr:r<rs.length)→rs[r].tprev≤r

variable {pub:List Fp} {rs:RcptVs} {as:List AcctV} (h:Context pub rs as)
include h
theorem memR_nodup : (memR (pub) rs as).Nodup :=
  h.permutation.nodup_iff.mp (memW_nodup _ _ _ h.unique)

theorem read_in_W {m : Msg} (hm : m ∈ memR (pub) rs as) : m ∈ memW (pub) rs as :=
  h.permutation.mem_iff.mpr hm

/-- Writes are determined by their key `(k, t, i)`. -/
theorem memW_key {m₁ m₂ : Msg} (h₁ : m₁ ∈ memW (pub) rs as) (h₂ : m₂ ∈ memW (pub) rs as)
    (hk : m₁.take 3 = m₂.take 3) : m₁ = m₂ := by
  have hnd := h.unique
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
theorem read_time {k t : Nat} {m : Msg} (hm : m ∈ memW (pub) rs as) (hk : m.take 3 = [k, t, 0]) :
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
    have hle := h.previous r hr
    have hin := read_in_W h (rd_mem_memR (pub := pub) (as := as) hr (i := 0) (by decide))
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
    have hin1 := read_in_W h (rd_mem_memR (pub := pub) (as := as) hr1 (i := 0) (by decide))
    have hkey : (rdMsg rs[r] 0).take 3 = (rdMsg rs[r1] 0).take 3 := by
      simp only [rdMsg, List.take]; rw [ht1, ← ksl_eq hr1, e3]
    exact rd_ne h hr hr1 (by omega) (memW_key h hin hin1 hkey)

/-- **The acct table's final read gets the last write.** -/
theorem tlast_eq {a : AcctV} (ha : a ∈ as) : a.tlast = lastW (ksl rs) a.k rs.length := by
  have hin := read_in_W h (ar_mem_memR (pub := pub) (rs := rs) ha (i := 0) (by decide))
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
  have hin1 := read_in_W h (rd_mem_memR (pub := pub) (as := as) hr1 (i := 0) (by decide))
  have hkey : (rdMsg rs[r1] 0).take 3 = (arMsg a 0).take 3 := by
    simp only [rdMsg, arMsg, acctLane, List.cons_append, List.take]; rw [ht1, ← ksl_eq hr1, e3]
  exact rd_ne_ar h hr1 ha (memW_key h hin1 hin hkey)

/-- The payload of a receipt's read. -/
theorem mem_read {r : Nat} (hr : r < rs.length) {i : Nat} (hi : i < 16) :
    (lastW (ksl rs) rs[r].kslot r = 0 → ∃ a ∈ as, a.k = rs[r].kslot ∧ rdMsg rs[r] i = awMsg a i) ∧
    (∀ r0, lastW (ksl rs) rs[r].kslot r = r0 + 1 →
      ∃ hr0 : r0 < rs.length, r0 < r ∧ rs[r0].kslot = rs[r].kslot ∧ rdMsg rs[r] i = wrMsg rs[r0] r0 i) := by
  have hin := read_in_W h (rd_mem_memR (pub := pub) (as := as) hr hi)
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
  have hin := read_in_W h (ar_mem_memR (pub := pub) (rs := rs) ha hi)
  have ht := tlast_eq h ha
  have hnd := h.unique
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

end ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
