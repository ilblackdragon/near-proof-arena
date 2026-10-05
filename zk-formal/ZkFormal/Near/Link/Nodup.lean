import ZkFormal.Near.Link.Refunds

/-!
# ZkFormal.Near.Link.Nodup — `nodup_ok : NodupStmt`

`RIDS` makes the sort table's ids exactly the receipt ids (one entry per
receipt); they are strictly increasing, hence distinct.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem nodup_of_getElem {α : Type} :
    ∀ (l : List α), (∀ i j (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i] ≠ l[j]) → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodup_of_getElem t (fun i j hi hj hij =>
      h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega))⟩
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp ha
    exact h 0 (j + 1) (by simp) (by simp; omega) (by omega) (by simp [he])

theorem strict_of_succ (f : Nat → Nat) (n : Nat) (h : ∀ t, t + 1 < n → f t < f (t + 1)) :
    ∀ t1 t2, t1 < t2 → t2 < n → f t1 < f t2 := by
  intro t1 t2 h12 h2
  induction t2 with
  | zero => omega
  | succ t ih =>
    have := h t h2
    rcases Nat.lt_or_ge t1 t with hl | hl
    · have := ih hl (by omega); omega
    · have : t1 = t := by omega
      subst this; exact this

theorem rcptSends_rids (pub : List Fp) (rs : RcptVs) :
    rcptSends pub rs B_RIDS = (rs.zip (List.range rs.length)).flatMap
      fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] := by
  simp [rcptSends, B_RIDS, B_BYTES, B_KEYNIB, B_MEM]

theorem sortRecvs_rids (ids : List (Nat × List Nat)) :
    (sortTraffic ids).recvs B_RIDS =
      ids.flatMap fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] := by
  simp [sortTraffic]

theorem nodup_ok : NodupStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  have hrl := rs_length_le h
  have hp := perm h (b := B_RIDS) (by decide) (by decide)
  rw [nearSends_rids, nearRecvs_rids, rcptSends_rids, sortRecvs_rids] at hp
  have hpn := perm_nat ?_ ?_ hp
  rotate_left
  · intro m hm
    obtain ⟨⟨x, r⟩, hpr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hr, rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · unfold P; omega
    · simp at hi; unfold P; omega
    · exact getD_lt (fun y hy => h.rcpt.canon _ (List.getElem_mem hr) y (by simp [RcptV.raw, hy])) i
  · intro m hm
    obtain ⟨p, hpi, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact (h.sort.len p hpi).2
    · simp at hi; unfold P; omega
    · exact getD_lt (h.sort.canon p hpi) i
  -- rid bytes
  obtain ⟨hrcb, -⟩ := rc_digest h
  have hridb : ∀ r (hr : r < rs.length), Bytes8 rs[r].rid := fun r hr =>
    bytes8_of_sub hrcb (fun y hy => by
      simp only [rcMsg, List.mem_append, List.mem_flatMap]; right
      exact ⟨_, List.getElem_mem hr, by simp [RcptV.enc, hy]⟩)
  -- every sort entry is a receipt's id
  have hrev : ∀ p (hp : p < ids.length) j, j < 32 →
      ∃ hr : ids[p].1 < rs.length, ids[p].2.getD j 0 = rs[ids[p].1].rid.getD j 0 := by
    intro p hp j hj
    have hm2 : [ids[p].1, j, ids[p].2.getD j 0] ∈ ids.flatMap
        fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] :=
      List.mem_flatMap.mpr ⟨_, List.getElem_mem hp, List.mem_map.mpr ⟨j, by simp; omega, rfl⟩⟩
    obtain ⟨⟨x, r'⟩, hpr, hm3⟩ := List.mem_flatMap.mp (hpn.mem_iff.mpr hm2)
    obtain ⟨hr', rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨j', -, he'⟩ := List.mem_map.mp hm3
    simp only [List.cons.injEq] at he'
    obtain ⟨e1, rfl, e3⟩ := he'
    subst e1
    exact ⟨hr', e3.1.symm⟩
  -- each receipt has a sort entry carrying its id
  have hentry : ∀ r (hr : r < rs.length), ∃ p, ∃ hp : p < ids.length, ids[p].1 = r ∧
      ids[p].2 = rs[r].rid := by
    intro r hr
    have hm : [r, 0, rs[r].rid.getD 0 0] ∈ (rs.zip (List.range rs.length)).flatMap
        fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] :=
      List.mem_flatMap.mpr ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩,
        List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
    obtain ⟨q, hq, hm'⟩ := List.mem_flatMap.mp (hpn.mem_iff.mp hm)
    obtain ⟨i, -, he⟩ := List.mem_map.mp hm'
    simp only [List.cons.injEq] at he
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hq
    refine ⟨p, hpl, he.1, ?_⟩
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
    have hl1 : ids[p].2.length = 32 := (h.sort.len _ hq).1
    apply List.ext_getElem (by rw [hl1, w.lens.1])
    intro j hj1 hj2
    obtain ⟨_, e⟩ := hrev p hpl j (by omega)
    rw [← getD_eq_getElem _ 0 hj1, ← getD_eq_getElem _ 0 hj2, e]
    simp only [he.1]
  have hall : ∀ x ∈ ids, ∀ y ∈ x.2, y < 256 := by
    intro x hx y hy
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hl1 : ids[p].2.length = 32 := (h.sort.len _ hx).1
    obtain ⟨hr, e⟩ := hrev p hpl j (by omega)
    rw [← getD_eq_getElem _ 0 hj, e]
    exact getD_lt_of_bytes8 (hridb _ hr) _
  have hstrict := strict_of_succ
    (fun t => leNat ((ids.getD t (0, [])).2.map UInt8.ofNat)) ids.length
    (fun t ht => h.sort.incr t ht hall)
  -- distinct ids
  simp only [linkExt, List.map_map]
  apply nodup_of_getElem
  intro i j hi hj hij he
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map, Function.comp, RcptV.toReceipt] at he
  obtain ⟨p1, hp1, e11, e12⟩ := hentry i hi
  obtain ⟨p2, hp2, e21, e22⟩ := hentry j hj
  have hpne : p1 ≠ p2 := fun e => hij (by subst e; omega)
  have hf : ∀ p (hp : p < ids.length) r (hr : r < rs.length), ids[p].2 = rs[r].rid →
      leNat ((ids.getD p (0, [])).2.map UInt8.ofNat) = leNat (toBytes rs[r].rid) := by
    intro p hp r hr e
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, e]; rfl
  have f1 := hf p1 hp1 i hi e12
  have f2 := hf p2 hp2 j hj e22
  rw [he] at f1
  rcases Nat.lt_or_gt_of_ne hpne with hl | hl
  · have := hstrict p1 p2 hl hp2; omega
  · have := hstrict p2 p1 hl hp1; omega

end Link

end ZkFormal.Near
