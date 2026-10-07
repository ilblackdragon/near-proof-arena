import ZkFormal.NearV3.Rcpt.Extract.Srcp.PathItem

/-!
# The source-proof message counter cannot wrap

The counter starts at zero, increases only when a new segment begins, and is
constant elsewhere on active rows. Its natural value is at most the row index
and is positive on every segment row. Padding counter cells remain irrelevant.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Active rows have a bounded natural message counter, positive inside segments. -/
theorem counter_nat {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    ∃ n, n ≤ r ∧ tr.cell tt r q = Fp.ofNat n ∧ (tr.cell tt r sg = 1 → 0 < n) := by
  induction r with
  | zero =>
    have h0 := row0 hL hr
    refine ⟨0, by omega, h0.2.2.1, ?_⟩
    intro hs
    have he := (local_ hL hr).1
    rw [h0.1, hs] at he
    exact False.elim (by grind)
  | succ r ih =>
    have hr' : r < tr.height tt := by omega
    have ha' : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1 := by
      rcases isBool hL hr' (x := rt) (by simp [bools]) with ht | ht
      · rcases isBool hL hr' (x := sg) (by simp [bools]) with hs | hs
        · have hp := padStep hL hr ht hs
          rcases ha with ha | ha <;> simp_all
        · exact Or.inr hs
      · exact Or.inl ht
    obtain ⟨n, hn, hq, hp⟩ := ih hr' ha'
    have incr (he : tr.cell tt (r + 1) q = tr.cell tt r q + 1) :
        tr.cell tt (r + 1) q = Fp.ofNat (n + 1) := by
      rw [he, hq, show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add']
    rcases isBool hL hr' (x := rt) (by simp [bools]) with ht | ht
    · have hs : tr.cell tt r sg = 1 := by rcases ha' with h | h; simp_all; exact h
      rcases isBool hL hr' (x := sl) (by simp [bools]) with hl | hl
      · have he := (inSeg hL hr hs hl).2.2.2 q (by simp [segConst])
        exact ⟨n, by omega, he.trans hq, fun _ => hp hs⟩
      · rcases isBool hL hr (x := sg) (by simp [bools]) with hnsg | hnsg
        · have hnrt : tr.cell tt (r + 1) rt = 1 := by rcases ha with h | h; exact h; simp_all
          exact ⟨n, by omega, (afterSegRt hL hr hl hnrt).1.trans hq,
            fun h => False.elim (by rw [hnsg] at h; simpa using h)⟩
        · exact ⟨n + 1, by omega, incr (afterSegSg hL hr hl hnsg).2.2.1, by omega⟩
    · exact ⟨n + 1, by omega, incr (afterRoot hL hr ht).2.2.2.1, by omega⟩

/-- Canonical extraction recovers the natural counter, with no field wraparound. -/
theorem counter_bound {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    (tr.cell tt r q).toNat ≤ r ∧ (tr.cell tt r sg = 1 → 0 < (tr.cell tt r q).toNat) := by
  obtain ⟨n, hn, he, hp⟩ := counter_nat hL hr ha
  have hnP : n < P := by have := hP hL; omega
  rw [he, Fp.toNat_ofNat, Nat.mod_eq_of_lt hnP]
  exact ⟨hn, hp⟩

/-- Every source-message identifier is canonical in the field. -/
theorem counter_id_lt {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    msgId K_SRC (tr.cell tt r q).toNat < P := by
  have hc := (counter_bound hL hr ha).1
  have hH := height_le hL
  unfold msgId K_SRC P
  omega

/-- All non-SIZE path traffic, now with counter positivity discharged by the table. -/
theorem pathItem_traffic_closed {s : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0))
    (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range 64).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd) =
      (srcpItemMsgs (pathItem tr tt s d) bb sd).map Msg.toFp := by
  have hs : tr.cell tt s sg = 1 := by
    simpa using ((segRows hL hu hH hrt).2.2.2.2.2.2 0 (by omega)).1
  exact pathItem_traffic hL hu hH hrt hlf d hd
    ((counter_bound hL (by omega) (Or.inr hs)).2 hs) bb hb sd

end ZkFormal.NearV3.SrcpProof
