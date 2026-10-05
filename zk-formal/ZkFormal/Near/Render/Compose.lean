import ZkFormal.Near.Render.Statements

/-!
# ZkFormal.Near.Render.Compose — `RenderStmt` from the render obligations

`render_stmt : RenderObligations → RenderStmt` (no `sorry`): heights,
constraints and bits from the seven `LocalStmt`s; bus balance from the seven
`TrafficStmt`s (each table's `tableBusCount` is a count in its honest
traffic), the ten `BusStmt`s and `other_bus` (proved here: no honest traffic
on buses `≥ 10`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

section hi
set_option linter.unusedSimpArgs false
variable {b : Nat} (hb : 10 ≤ b)
include hb

/-- `b` is none of the ten buses. -/
theorem ne_buses : b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 2 ∧ b ≠ 3 ∧ b ≠ 4 ∧ b ≠ 5 ∧ b ≠ 6 ∧ b ≠ 7 ∧ b ≠ 8 ∧ b ≠ 9 := by
  omega

theorem nodeTraffic_hi (vs : List NodeS) (pub : List Fp) (s : Bool) :
    sel s (nodeTraffic vs pub) b = [] := by
  cases s <;> simp [sel, nodeTraffic, nodeSends, nodeRecvs, B_BYTES, B_PARENT, B_EDGE, B_DIGEST,
    B_VSLOT, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem walkTraffic_hi (ws : List WalkV) (s : Bool) : sel s (walkTraffic ws) b = [] := by
  cases s <;> simp [sel, walkTraffic, walkSends, walkRecvs, B_EDGE, B_FINAL, B_KEYNIB, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem rcptTraffic_hi (pub : List Fp) (rs : RcptVs) (s : Bool) :
    sel s (rcptTraffic pub rs) b = [] := by
  cases s <;> simp [sel, rcptTraffic, rcptSends, rcptRecvs, B_BYTES, B_KEYNIB, B_MEM, B_RIDS,
    B_MPOS, B_DIGEST, B_FINAL, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem acctTraffic_hi (as : List AcctV) (s : Bool) : sel s (acctTraffic as) b = [] := by
  cases s <;> simp [sel, acctTraffic, acctSends, acctRecvs, B_BYTES, B_MEM, B_VSLOT, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem mrkTraffic_hi (pub : List Fp) (v : MrkV) (s : Bool) : sel s (mrkTraffic pub v) b = [] := by
  cases s <;> simp [sel, mrkTraffic, mrkSends, mrkRecvs, B_BYTES, B_MPOS, B_DIGEST, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem sortTraffic_hi (ids : List (Nat × List Nat)) (s : Bool) : sel s (sortTraffic ids) b = [] := by
  cases s <;> simp [sel, sortTraffic, B_RIDS, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

theorem shaTraffic_hi (ms : List Render.Msg) (s : Bool) : sel s (shaTraffic ms) b = [] := by
  cases s <;> simp [sel, shaTraffic, B_BYTES, B_DIGEST, (ne_buses hb).1, (ne_buses hb).2.1, (ne_buses hb).2.2.1, (ne_buses hb).2.2.2.1,
    (ne_buses hb).2.2.2.2.1, (ne_buses hb).2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.1,
    (ne_buses hb).2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.1, (ne_buses hb).2.2.2.2.2.2.2.2.2]

/-- **No honest traffic on buses `≥ 10`.** -/
theorem other_bus (c : Claim) (e : Ext) (s : Bool) (m : List Fp) : hcount c e b s m = 0 := by
  simp [hcount, hc, htf, honestTraffic, shaTraffic_hi hb, nodeTraffic_hi hb, walkTraffic_hi hb,
    rcptTraffic_hi hb, acctTraffic_hi hb, mrkTraffic_hi hb, sortTraffic_hi hb, cnt]

end hi

theorem count_sel {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp} {tf : Traffic}
    (h : TableTraffic is tr t pub tf) (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount is tr t pub b s m = cnt (sel s tf b) m := by
  cases s
  · exact (h b m).2
  · exact (h b m).1

/-- **`RenderStmt` from the render obligations.** -/
theorem render_stmt (h : RenderObligations) : RenderStmt := by
  intro c e hg
  show Holds nearAir (publicOf c) (Render.render c.1 e)
  have L : ∀ t (ht : t < nearAir.tables.length),
      TableLocal nearAir.tables[t] (render c.1 e) t (publicOf c) := by
    intro t ht
    match t, ht with
    | 0, _ => exact h.shaL c e hg
    | 1, _ => exact h.nodeL c e hg
    | 2, _ => exact h.walkL c e hg
    | 3, _ => exact h.rcptL c e hg
    | 4, _ => exact h.acctL c e hg
    | 5, _ => exact h.mrkL c e hg
    | 6, _ => exact h.sortL c e hg
    | _ + 7, ht => exact absurd ht (by simp [nearAir_tables])
  have key : ∀ b s m, busCount nearAir (render c.1 e) (publicOf c) b s m = hcount c.1 e b s m := by
    intro b s m
    rw [busCount_near, count_sel (h.shaT c e hg), count_sel (h.nodeT c e hg),
      count_sel (h.walkT c e hg), count_sel (h.rcptT c e hg), count_sel (h.acctT c e hg),
      count_sel (h.mrkT c e hg), count_sel (h.sortT c e hg)]
    rfl
  refine ⟨fun t ht => ⟨(L t ht).log_ge, (L t ht).log_le⟩, fun t ht r hr e he => (L t ht).constr r hr e he,
    fun t ht r hr i hi b hb => (L t ht).bits r hr i hi b hb, ?_⟩
  intro b m
  rw [key, key]
  match b with
  | 0 => exact h.bytes c e hg m
  | 1 => exact h.digest c e hg m
  | 2 => exact h.parent c e hg m
  | 3 => exact h.vslot c e hg m
  | 4 => exact h.edge c e hg m
  | 5 => exact h.keynib c e hg m
  | 6 => exact h.final c e hg m
  | 7 => exact h.mem c e hg m
  | 8 => exact h.rids c e hg m
  | 9 => exact h.mpos c e hg m
  | b + 10 => rw [other_bus (by omega), other_bus (by omega)]

end ZkFormal.Near.Render
