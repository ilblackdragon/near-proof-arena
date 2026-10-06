import ZkFormal.V2.Np.Bus

/-!
# ZkFormal.V2.Np.Msg4 — the aux commitment round of v2

v1's `no_gpDiffer` shows, under vanishing constraints on the trace domain, that the
products of the send (receive) finals are the trace grand products of that side.  That
argument is per table and does not look at the bus equation.  Here it is restated as the two equalities
(`finals_gp`).  With them, `¬ BusFinalsFailP` gives the v2 grand-product equality including
the public products, i.e. `¬ GpDifferP`.
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

local notation "prm0" => Params.default

section
variable {AP : AirP}

/-- Under vanishing constraints, the finals' products are the trace grand products. -/
theorem finals_gp {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk AP.toAir prm0 l = true)
    (hfl : (finalsOf τ).length = ((layOf AP.toAir prm0 τ).map fun L => L.sendG + L.recvG).sum)
    (α γ : Fp8)
    (hz : ∀ t, t < AP.tables.length → ∀ r, r < 2 ^ (tl AP.toAir prm0 τ t).log →
      ∀ c ∈ csAt AP.toAir prm0 τ t α γ (omg (tl AP.toAir prm0 τ t).log ^ r), c = 0) :
    finSends AP prm0 τ = ((expand (busMsgs AP.toAir prm0 τ true)).map fun m => γ - fpL α m).prod ∧
    finRecvs AP prm0 τ = ((expand (busMsgs AP.toAir prm0 τ false)).map fun m => γ - fpL α m).prod := by
  obtain ⟨hlen, _, _, _⟩ := headerOk_facts hh
  have hlay : (layOf AP.toAir prm0 τ).length = AP.toAir.tables.length := by
    unfold layOf hdrOf; rw [hl]; simp [layout, hlen]
  have hside : ∀ t, t < AP.toAir.tables.length →
      ((finsOf AP.toAir prm0 τ t).take (tl AP.toAir prm0 τ t).sendG).prod =
        (((tableOf AP.toAir t).interactions.filter (fun i => i.send == true)).map (PhiT AP.toAir τ α γ t)).prod ∧
      ((finsOf AP.toAir prm0 τ t).drop (tl AP.toAir prm0 τ t).sendG).prod =
        (((tableOf AP.toAir t).interactions.filter (fun i => i.send == false)).map (PhiT AP.toAir τ α γ t)).prod := by
    intro t ht
    have tab := tabOk_of hl hh t ht
    have := table_side (tableOf AP.toAir t).interactions (finsOf AP.toAir prm0 τ t) (PhiT AP.toAir τ α γ t)
      (finsOf_length hl hh hfl t ht) (fun j hj => table_fins AP.toAir τ t α γ tab.hlog tab.haux
        (finsOf_length hl hh hfl t ht) (hz t ht) j hj)
    rw [tab.hsend, ← filter_send_eq, ← filter_recv_eq]
    exact this
  have hsplit := finals_split (fun L => L.sendG + L.recvG) (layOf AP.toAir prm0 τ) [] (finalsOf τ)
  simp only [List.nil_append] at hsplit
  have hmap : ∀ (F G : Nat → Fp8), (∀ t, t < AP.toAir.tables.length → F t = G t) →
      ((List.range (layOf AP.toAir prm0 τ).length).map F).prod = ((List.range AP.toAir.tables.length).map G).prod :=
    fun F G hFG => by rw [hlay]; congr 1; exact List.map_congr_left fun t ht => hFG t (List.mem_range.mp ht)
  have e1 : ∀ x : Fp8, 1 * x = x := fun x => by grind
  unfold finSends finRecvs finsSplit
  rw [hsplit, zip_range_map _ _ _ rfl, List.map_map, List.map_map, foldl_mul_prod, foldl_mul_prod]
  rw [e1, e1, hmap _ (fun t => (((tableOf AP.toAir t).interactions.filter (fun i => i.send == true)).map
      (PhiT AP.toAir τ α γ t)).prod) (fun t ht => ?_),
    hmap _ (fun t => (((tableOf AP.toAir t).interactions.filter (fun i => i.send == false)).map
      (PhiT AP.toAir τ α γ t)).prod) (fun t ht => ?_), ← gp_tables hl hh, ← gp_tables hl hh]
  · exact ⟨rfl, rfl⟩
  · show ((finsOf AP.toAir prm0 τ t).drop (tl AP.toAir prm0 τ t).sendG).foldl (· * ·) 1 = _
    rw [foldl_mul_prod, e1, (hside t ht).2]
  · show ((finsOf AP.toAir prm0 τ t).take (tl AP.toAir prm0 τ t).sendG).foldl (· * ·) 1 = _
    rw [foldl_mul_prod, e1, (hside t ht).1]

theorem gp_busMsgsP (τ : PTn) (α γ : Fp8) (s : Bool) :
    ((expand (busMsgsP AP prm0 τ s)).map fun m => γ - fpL α m).prod =
      ((expand (busMsgs AP.toAir prm0 τ s)).map fun m => γ - fpL α m).prod * pubGp AP τ α γ s := by
  unfold busMsgsP pubGp
  rw [expand_append, List.map_append, prod_append']

theorem no_gpDifferP {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk AP.toAir prm0 l = true)
    (hfl : (finalsOf τ).length = ((layOf AP.toAir prm0 τ).map fun L => L.sendG + L.recvG).sum)
    (α γ : Fp8)
    (hz : ∀ t, t < AP.tables.length → ∀ r, r < 2 ^ (tl AP.toAir prm0 τ t).log →
      ∀ c ∈ csAt AP.toAir prm0 τ t α γ (omg (tl AP.toAir prm0 τ t).log ^ r), c = 0)
    (hBF : ¬ BusFinalsFailP AP prm0 τ α γ) : ¬ GpDifferP AP prm0 τ α γ := by
  obtain ⟨hS, hR⟩ := finals_gp hl hh hfl α γ hz
  unfold BusFinalsFailP at hBF
  rw [hS, hR, Classical.not_not] at hBF
  unfold GpDifferP
  rw [gp_busMsgsP, gp_busMsgsP]
  exact fun h => h hBF

end

theorem msg4P : MsgAtP 4 := by
  intro AP prm hok τ m _ hs _ hE hst
  obtain ⟨⟨hprm, _, _⟩, _⟩ := hok
  subst hprm
  have hs' : Shaped (Vnp AP.toAir Params.default) (τ.push m) := (shaped_iff AP _ _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix AP.toAir _ τ).1 m hs'
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hsτ hne
  obtain ⟨l2, hl2, _, s4, h41, h42⟩ := push_fits hs' hne
  rw [hl] at hl2; cases hl2
  rw [hE, (sched_get l).2.2.1] at h41; cases h41
  obtain ⟨a4, b4, hm, ha4, hb4⟩ := fits_two h42
  cases hm
  obtain ⟨o, rfl⟩ := fits_oracle ha4
  obtain ⟨xs, rfl, hxs⟩ := fits_elems hb4
  have hel := elems_nil_E4 hsτ hE
  have hl' : (τ.push [PartV.oracle o, .elems xs]).header? = some l := by rw [header?_push _ _ hne]; exact hl
  have hfin : finalsOf (τ.push [PartV.oracle o, .elems xs]) = xs := by
    unfold finalsOf
    have : (τ.push [PartV.oracle o, .elems xs]).elems = τ.elems ++ [xs] := by
      simp [PT.push, PT.elems, List.flatMap_append]
    rw [this, hel]; rfl
  have hfl : (finalsOf (τ.push [PartV.oracle o, .elems xs])).length =
      ((layOf AP.toAir Params.default (τ.push [PartV.oracle o, .elems xs])).map fun L => L.sendG + L.recvG).sum := by
    rw [hfin, hxs]; unfold layOf hdrOf; rw [hl']; rfl
  have ho1 := shaped_oracles1 hsτ (by omega)
  have hO : OAgree 1 (τ.push [PartV.oracle o, .elems xs]) τ := (oAgree_push τ _ hne).mono ho1
  have hE' : (τ.push [PartV.oracle o, .elems xs]).entries.length = 5 := by rw [len_push, hE]
  simp only [StageP, hE] at hst
  simp only [StageP, hE', chals_push]
  refine Classical.byContradiction fun hno => ?_
  simp only [_root_.not_or, Classical.not_not] at hno
  obtain ⟨hC2, hCs, hBF⟩ := hno
  have hz : ∀ t, t < AP.tables.length → ∀ r, r < 2 ^ (tl AP.toAir Params.default (τ.push [PartV.oracle o, .elems xs]) t).log →
      ∀ c ∈ csAt AP.toAir Params.default (τ.push [PartV.oracle o, .elems xs]) t (τ.chals.getD 0 0) (τ.chals.getD 1 0)
        (omg (tl AP.toAir Params.default (τ.push [PartV.oracle o, .elems xs]) t).log ^ r), c = 0 :=
    fun t ht r hr c hc => Classical.byContradiction fun h0 => hCs ⟨t, ht, r, hr, c, hc, h0⟩
  rcases hst with h | h | h
  · exact h ((allClose_congr hO (Nat.le_refl 1)).mp (allClose_mono (by omega) hC2))
  · exact no_localFail hl' hh _ _ hz ((localFail_congr hO (Nat.le_refl 1)).mpr h)
  · exact no_gpDifferP hl' hh hfl _ _ hz hBF ((gpDifferP_congr AP _ hO (Nat.le_refl 1) _ _).mpr h)

end ZkFormal.V2.Np
