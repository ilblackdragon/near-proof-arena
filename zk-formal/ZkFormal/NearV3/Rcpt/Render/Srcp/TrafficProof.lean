import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficSize

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- All honest rows produce exactly the semantic traffic, with silent padding. -/
theorem messages {bs : List SrcpB} (h : SrcpWf bs) (H : Nat) (hH : R bs ≤ H)
    (bb : Nat) (sd : Bool) :
    (List.range H).flatMap (fun r => rowN (cell bs r) bb sd) =
      if sd then (srcpTraffic bs).sends bb else (srcpTraffic bs).recvs bb := by
  by_cases hb : bb = B_SIZE
  · subst bb
    rw [size_messages h H hH]
    cases sd <;> rfl
  · rw [Near.Render.range_split hH, List.flatMap_append, active_messages h bb sd hb]
    have hz : ((List.range (H - R bs)).map (R bs + ·)).flatMap
        (fun r => rowN (cell bs r) bb sd) = [] := by
      rw [List.flatMap_map]
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      exact padding_messages bs (R bs + r) bb sd (by omega)
    rw [hz, List.append_nil]
    cases sd <;> simp [srcpTraffic, hb]

/-- The executable source-proof renderer realizes its complete bus contract. -/
theorem table_traffic {bs : List SrcpB} (h : SrcpWf bs)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hH : R bs ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    TableTraffic SrcpV3.interactions tr tt pub (srcpTraffic bs) := by
  have hall : ∀ bb sd,
      (List.range (tr.height tt)).flatMap (fun r => rowTraffic SrcpV3.interactions tr tt r pub bb sd) =
      (if sd then (srcpTraffic bs).sends bb else (srcpTraffic bs).recvs bb).map Msg.toFp := by
    intro bb sd
    rw [← messages h (tr.height tt) hH bb sd, List.map_flatMap]
    apply flatMap_congr'
    intro r hr
    exact row_traffic (cell bs r) (hc r (List.mem_range.mp hr)) (cell_bool_bound bs r) bb sd
  apply Near.Render.traffic_of
  · intro bb; rw [hall bb true]; exact List.Perm.refl _
  · intro bb; rw [hall bb false]; exact List.Perm.refl _

end ZkFormal.NearV3.Render.SrcpGen
