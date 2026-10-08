import ZkFormal.NearV3.Render.Ups.CompactExtract.Traffic
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
theorem rowTraffic_compact (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic compactInteractions tr t r pub b sd =
      (compactMsgs (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) b sd).map Msg.toFp := by
  unfold rowTraffic compactMsgs
  rw [List.map_flatMap]
  have hp : compactInteractions.all (fun i=>pureGate i && i.msg.all Expr.pure)=true := by
    have hs : compactInteractions ⊆ UpsV3.interactions := by decide +kernel
    apply List.all_eq_true.mpr
    intro i hi
    exact List.all_eq_true.mp interactions_pure i (hs hi)
  rw [List.all_eq_true] at hp
  apply UpsRows.flatMap_congr'
  intro i hi
  have hi' := hp i hi
  simp only [Bool.and_eq_true, List.all_eq_true] at hi'
  obtain ⟨hg, hm⟩ := hi'
  unfold pureGate at hg
  split at hg
  · rename_i g hgm
    by_cases hc : i.bus = b ∧ i.send = sd
    · rw [if_pos hc, if_pos hc, List.map_replicate]
      congr 1
      · simp only [Interaction.multNat, Interaction.multNat.go, hgm, uMult, Nat.pow_zero, Nat.add_zero]
        rw [eval_pure tr t r pub g hg]
      · simp only [Interaction.msgVal, Msg.toFp, List.map_map]
        apply List.map_congr_left; intro e he
        simp only [Function.comp, Fp.ofNat_toNat]
        exact eval_pure tr t r pub e (hm e he)
    · rw [if_neg hc, if_neg hc]; rfl
  · exact absurd hg (by simp)

variable {tr : Trace Fp} {pub : List Fp} {t : Nat}
section
variable (hL : TableLocal compactTable tr t pub)
include hL

theorem rowTraffic_eq {r : Nat} (hr : r<tr.height t) (b : Nat) (sd : Bool) :
    rowTraffic compactInteractions tr t r pub b sd=
      (uMsgs (rowC tr t r) (rowC tr t ((r+1)%tr.height t)) b sd).map Msg.toFp := by
  rw [rowTraffic_compact,compactMsgs_eq (noValue (rowOk hL hr) (rowC_lt tr t r))]

omit hL in
private theorem quiet_old {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hD : ∀x,D x<P)
    (ha : C act=0) (b : Nat) (sd : Bool) : uMsgs C D b sd=[] := by
  rw [←compactMsgs_eq (noValue ok hC)]
  exact quiet ok hC hD ha b sd
theorem viewTraffic {segs : List (Nat × Nat)} (hc : Consec 0 segs) (he : segEnd 0 segs ≤ tr.height t)
    (hs : ∀ p ∈ segs, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2)
    (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height t → actB tr t r = false) :
    TableTraffic compactInteractions tr t pub (upsTraffic (viewOf tr t segs)) := by
  have bound : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height t := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have all : ∀ sd b, (List.range (tr.height t)).flatMap (fun r => rowTraffic compactInteractions tr t r pub b sd) =
      ((viewOf tr t segs).flatMap (·.msgs b sd)).map Msg.toFp := by
    intro sd b
    rw [UpsRows.flatMap_congr' (fun r hr => rowTraffic_eq hL (List.mem_range.mp hr) b sd), ← List.map_flatMap]
    congr 1
    rw [flatMap_rows_segs (tr.height t) segs _ hc he (fun r h1 h2 => by
      have ha := hpad r h1 h2
      simp only [actB, decide_eq_false_iff_not] at ha
      have b0 := (kinds (rowOk hL (r := r) h2) (rowC_lt tr t r) (rowC_lt tr t _)).1
      exact quiet_old (rowOk hL (r := r) h2) (rowC_lt tr t r) (rowC_lt tr t _) (by omega) b sd)]
    simp only [viewOf, List.flatMap_map]
    apply UpsRows.flatMap_congr'; intro p hp
    simp only [UpsSeg.msgs, segOf_len]
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply UpsRows.flatMap_congr'; intro i hi; rw [List.mem_range] at hi
    rw [segOf_row tr t p hi, segOf_next tr t p (bound p hp) hi]
  intro b m
  refine ⟨?_, ?_⟩
  · rw [tableBusCount_eq, all true b]; rfl
  · rw [tableBusCount_eq, all false b]; rfl

/-- Full physical extraction: canonical compact segments and exact all-bus
traffic, including inactive padding and wraparound rows. -/
theorem physical_view_traffic : ∃v,Wf v ∧ TableTraffic compactInteractions tr t pub (upsTraffic v) := by
  obtain ⟨segs,hc,he,hs,hpad,hw⟩:=physical_view hL
  exact ⟨viewOf tr t segs,hw,viewTraffic hL hc he hs hpad⟩
end
end ZkFormal.NearV3.Render.UpsRelay.Extract
