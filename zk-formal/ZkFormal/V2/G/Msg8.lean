import ZkFormal.V2.G.Msg4

/-!
# ZkFormal.V2.G.Msg8 — the OOD-values round of v2 under `NpOkPg`

Copy of `V2.Np.Msg8` at `pg g`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

variable {g : Nat}


theorem foldl_mul_map {α : Type} (f : α → Fp8) (L : List α) :
    L.foldl (fun acc x => acc * f x) 1 = (L.map f).prod := by
  have := List.foldl_map (f := f) (g := fun (a b : Fp8) => a * b) (l := L) (init := 1)
  rw [← this, foldl_mul_prod]
  grind

/-- The verifier's public product is L3's. -/
theorem pubProd_eq (AP : AirP) (τ : PTn) (α γ : Fp8) (s : Bool) :
    pubProd AP (pubT τ) α γ s = pubGp AP τ α γ s := by
  unfold pubProd pubGp
  rw [expand_pubBM, List.map_map, foldl_mul_map]
  rfl

theorem globalChecksP_true {AP : AirP} {prm : Params} {pub : List Fp} {lay : List TLayout}
    {ood : List (TOod Fp8)} {finals : List Fp8} {αfp γ αc z : Fp8}
    (h : globalChecksP (F := Fp) AP prm pub lay ood finals αfp γ αc z = true) :
    (∀ k (hk : k < (AP.tables.zip (lay.zip ood)).length),
      aliOk AP.toAir prm pub αfp γ αc z (AP.tables.zip (lay.zip ood))[k].1 (AP.tables.zip (lay.zip ood))[k].2.1
        (AP.tables.zip (lay.zip ood))[k].2.2
        ((finals.drop (((AP.tables.zip (lay.zip ood)).take k).map fun x => x.2.1.sendG + x.2.1.recvG).sum).take
          ((AP.tables.zip (lay.zip ood))[k].2.1.sendG + (AP.tables.zip (lay.zip ood))[k].2.1.recvG))) ∧
    (let fins := (lay.foldl (fun (acc : List (List Fp8) × List Fp8) L =>
        (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finals)).1
     let sends : List Fp8 := (fins.zip lay).map fun (f, L) => (f.take L.sendG).foldl (· * ·) 1
     let recvs : List Fp8 := (fins.zip lay).map fun (f, L) => (f.drop L.sendG).foldl (· * ·) 1
     sends.foldl (· * ·) 1 * pubProd AP pub αfp γ true = recvs.foldl (· * ·) 1 * pubProd AP pub αfp γ false) := by
  unfold globalChecksP at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun k hk => ?_, of_decide_eq_true h.2⟩
  have := fold_and (β := Air.Table × TLayout × TOod Fp8)
    (fun x fins => decide (aliOk AP.toAir prm pub αfp γ αc z x.1 x.2.1 x.2.2 fins))
    (fun x => x.2.1.sendG + x.2.1.recvG) _ (fun _ _ => rfl) _ _ _ h.1 k hk
  exact of_decide_eq_true this

theorem msg8P : MsgAtPg 8 := by
  intro AP prm hok τ m _ hs _ hE hst
  obtain ⟨⟨⟨g, hprm, hg1, hg3⟩, _, _⟩, _⟩ := hok
  subst hprm
  have hs' : Shaped (Vnp AP.toAir (pg g)) (τ.push m) := (shaped_iff AP _ _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix AP.toAir _ τ).1 m hs'
  obtain ⟨S⟩ := shape8 hsτ hE
  obtain ⟨l2, hl2, _, s8, h81, h82⟩ := push_fits hs' hne
  rw [S.hl] at hl2; cases hl2
  rw [hE, (sched_odd AP.toAir (pg g) S.l).2.2.2.2] at h81; cases h81
  obtain ⟨a8, hm, ha8⟩ := fits_one h82
  cases hm
  obtain ⟨ood, rfl, hoodl⟩ := fits_elems ha8
  -- the transcripts
  have hent := S.hent
  have hchals : τ.chals = [S.c1, S.c3, S.c5, S.c7] := by
    unfold PT.chals; rw [hent]; rfl
  have hchals' : (τ.push [PartV.elems ood]).chals = [S.c1, S.c3, S.c5, S.c7] := by
    rw [chals_push, hchals]
  have helems : τ.elems = [S.fins] := by unfold PT.elems; rw [hent]; rfl
  have helems' : (τ.push [PartV.elems ood]).elems = [S.fins, ood] := by
    unfold PT.elems PT.push; simp only [hent]; rfl
  have hor : τ.oracles = [S.o0, S.o1, S.o2] := by unfold PT.oracles; rw [hent]; rfl
  have hor' : (τ.push [PartV.elems ood]).oracles = [S.o0, S.o1, S.o2] := by
    unfold PT.oracles PT.push; simp only [hent]; rfl
  have hh' : (τ.push [PartV.elems ood]).header? = τ.header? := header?_push τ _ hne
  have hl' : (τ.push [PartV.elems ood]).header? = some S.l := by rw [hh', S.hl]
  have hO : ∀ k, OAgree k (τ.push [PartV.elems ood]) τ := fun k =>
    ⟨rfl, hh', fun i _ => by unfold oracleOf; rw [hor', hor]⟩
  have hfin : finalsOf (τ.push [PartV.elems ood]) = finalsOf τ := by
    unfold finalsOf; rw [helems', helems]; rfl
  have hfin' : finalsOf (τ.push [PartV.elems ood]) = S.fins := by
    unfold finalsOf; rw [helems']; rfl
  have hE' : (τ.push [PartV.elems ood]).entries.length = 9 := by rw [len_push, hE]
  have hcb : (τ.push [PartV.elems ood]).cb = τ.cb := rfl
  generalize hτ' : τ.push [PartV.elems ood] = τ' at *
  have hz' : zOf τ' = S.c7 := by unfold zOf; rw [hchals']; rfl
  -- stage 8 of τ
  simp only [StageP, hE, hchals] at hst
  have hz : ¬ (zOf τ').IsBase := by rw [hz']; exact hst.1
  -- the claim
  simp only [StageP, hE']
  refine Classical.byContradiction fun hno => ?_
  have hfri : FriGoodSoFar AP.toAir (pg g) τ' := by
    intro q hq
    exfalso
    have : friChals AP.toAir (pg g) τ' = [] := by
      unfold friChals; rw [hchals', List.drop_eq_nil_of_le (by simp), List.zip_nil_right]
    rw [this] at hq; exact Nat.not_lt_zero _ hq
  rw [_root_.not_or] at hno
  obtain ⟨hGF, hBF0⟩ := hno
  have hBF : ∀ L ∈ layOf AP.toAir (pg g) τ', ¬ BatchFar AP.toAir (pg g) τ' L.lde L.log :=
    fun L hL hf => hBF0 ⟨⟨L, hL, hf⟩, hfri⟩
  have hg : globalChecksP (F := Fp) AP (pg g) (pubT τ') (layOf AP.toAir (pg g) τ')
      (splitOod (layOf AP.toAir (pg g) τ') ood).1 S.fins S.c1 S.c3 S.c5 S.c7 = true := by
    unfold GlobalFailP at hGF; rw [hchals', helems'] at hGF
    simpa using hGF
  have hbw : ∀ m, batchedWord AP.toAir (pg g) τ' m = deepWord AP.toAir (pg g) τ' m := fun m => by
    unfold batchedWord batchChals; rw [hchals', List.drop_eq_nil_of_le (by simp), List.take_nil]; rfl
  have hLay := layOk_of hl' S.hh
  have hdeep : ∀ L ∈ layOf AP.toAir (pg g) τ', _ := fun L hL => by
    have hc := hBF L hL
    unfold BatchFar at hc
    rw [hbw, Classical.not_not] at hc
    exact deep_ok AP.toAir τ' hLay L hL hz hc
  have hAC : AllClose AP.toAir (pg g) τ' 3 := fun L hL => (hdeep L hL).1
  have hgt := globalChecksP_true hg
  rcases hst.2 with h | ⟨t, ht, hC⟩ | h
  · exact h ((allClose_congr (hO 3) (by omega)).mp hAC)
  · apply hC
    obtain ⟨_, hlt, htl⟩ := tl_mem hl' S.hh t ht
    have hd := (hdeep _ (List.getElem_mem hlt)).2
    rw [← htl] at hd
    have hoodl' : ood.length = ((layOf AP.toAir (pg g) τ').map oodCnt).sum := by
      rw [hoodl]; unfold layOf hdrOf; rw [hl']; rfl
    have hsp := splitOod_props (layOf AP.toAir (pg g) τ') ood hoodl'
    have hX : t < (AP.tables.zip ((layOf AP.toAir (pg g) τ').zip (splitOod (layOf AP.toAir (pg g) τ') ood).1)).length := by
      simp only [List.length_zip]; omega
    have hk := hgt.1 t hX
    rw [← hfin'] at hk
    have := ali_of_global hl' S.hh (by unfold oracleOf; rw [hor']; rfl) S.hf0
      (by rw [helems']; rfl) hoodl' hz t ht hd S.c1 S.c3 S.c5 hX (by rw [hz']; exact hk)
    rw [hz', Ct_congr (hO 3) (by omega) hfin, Qt_congr (hO 3) (Nat.le_refl 3),
      tl_congr _ (pg g) hh'] at this
    exact this
  · have h' := (busFinalsFailP_congr AP (pg g) hh' hfin hcb _ _).mpr h
    unfold BusFinalsFailP at h'
    apply h'
    have e2 := hgt.2
    rw [pubProd_eq, pubProd_eq] at e2
    unfold finSends finRecvs finsSplit
    rw [hfin']
    exact e2


end ZkFormal.V2.G
