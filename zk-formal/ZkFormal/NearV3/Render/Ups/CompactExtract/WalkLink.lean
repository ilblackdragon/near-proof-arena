import ZkFormal.NearV3.Render.Ups.CompactExtract.WalkTraffic
import ZkFormal.NearV3.Extract.Ups.UpsWalk
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
theorem ups_walkFp {v : List UpsSeg} (hw : Wf v) {b : Nat} (hb : b = B_EDGE ∨ b = B_BMAP) :
    ((upsTraffic v).sends b).map Msg.toFp = (walkSends3 (v.map upsWalk) b).map Msg.toFp ∧
    ((upsTraffic v).recvs b).map Msg.toFp = (walkRecvs3 (v.map upsWalk) b).map Msg.toFp := by
  rw [walkSends3_map, walkRecvs3_map]
  simp only [upsTraffic, List.map_flatMap]
  constructor <;> apply UpsRows.flatMap_congr' <;> intro s hs <;>
    obtain ⟨ps, fls, ws, hL⟩ := ups_layout hw s hs <;>
    have T := ups_walkTrafficFp hw hs hL <;> rcases hb with rfl | rfl
  · exact T.1
  · exact T.2.2.1
  · exact T.2.1
  · exact T.2.2.2

/-- **The balance over all walks.** -/
theorem walkBal_all {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR} {v : List UpsSeg} (hw : Wf v)
    {b : Nat} (hb : b = B_EDGE ∨ b = B_BMAP) (hE : WalkBal vs hs ws v b) : Walk3.BusBal vs hs (allWalks ws v) b := by
  obtain ⟨e1, e2⟩ := ups_walkFp hw hb
  unfold Walk3.BusBal
  unfold WalkBal at hE
  rw [allWalks, walkSends3_append, walkRecvs3_append]
  simp only [List.map_append] at hE ⊢
  rw [e1, e2] at hE
  simpa only [List.append_assoc] using hE

/-! ## The walks' well-formedness -/

theorem walkWf_app {A B : List WalkR} (hA : WalkWf3 A) (hB : ∀ wv ∈ B, WalkWf3 [wv])
    (hr : ((A ++ B).flatMap (·.steps)).length ≤ 2 ^ 23) : WalkWf3 (A ++ B) := by
  have one : ∀ {wv : WalkR}, wv ∈ [wv] := List.mem_singleton_self _
  refine ⟨fun wv h => ?_, fun wv h => ?_, fun wv h => ?_, fun wv h => ?_, fun wv h => ?_, hr⟩ <;>
    rcases List.mem_append.1 h with h | h
  · exact hA.len wv h
  · exact (hB wv h).len wv one
  · exact hA.canon wv h
  · exact (hB wv h).canon wv one
  · exact hA.rows wv h
  · exact (hB wv h).rows wv one
  · exact hA.start wv h
  · exact (hB wv h).start wv one
  · exact hA.chain wv h
  · exact (hB wv h).chain wv one

theorem upsWalks_len (v : List UpsSeg) : ((v.map upsWalk).flatMap (·.steps)).length = 4 * v.length := by
  induction v with
  | nil => simp
  | cons s v ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, upsWalk_len, List.length_cons] at ih ⊢
    omega

theorem segs_len {v : List UpsSeg} (hw : Wf v) : 5 * v.length ≤ 2 ^ 22 := by
  have h : ∀ (l : List UpsSeg), (∀ s ∈ l, s ∈ v) → 5 * l.length ≤ (l.map (·.rows.length)).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons s l ih =>
      obtain ⟨ps, fls, ws, hL⟩ := ups_layout hw s (hl s (by simp))
      have := hL.walk.1
      have := ih (fun t ht => hl t (by simp [ht]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  exact Nat.le_trans (h v (fun _ h => h)) hw.count

/-- The `W3` bitmap of an absent-at-branch terminal is a branch record's bitmap. -/
theorem ups_bm {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR} {v : List UpsSeg}
    (hN : NodeWf3 vs) (hW : WalkWf3 ws) (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21) (hw : Wf v)
    (hbal : WalkBal vs hs ws v B_BMAP) {s : UpsSeg} (hs' : s ∈ v) (hm : s.row 3 mB = 1) : s.row 3 wbm < 2 ^ 16 := by
  have hb := walkBal_all hw (Or.inr rfl) hbal
  have hP := P_big
  obtain ⟨ps, fls, wsl, hL⟩ := ups_layout hw s hs'
  have hl4 := hL.walk.1
  -- the row's `BMAP` step
  have hst : stepOf (s.row 3) 3 ∈ (upsWalk s).steps := by
    simp only [upsWalk, List.mem_map, List.mem_range]; exact ⟨3, by omega, rfl⟩
  have hmode : (stepOf (s.row 3) 3).mode = 2 := by
    have F := wRowF hw hs' hL 3 (by omega)
    have Mc := mode_cases F.modes 3
    exact Mc.2.2.1.2 hm
  -- canonical `BMAP` keys of all walks
  have hwalkC : ∀ {wv' : WalkR}, wv' ∈ allWalks ws v → ∀ st' ∈ wv'.steps, st'.mode = 2 →
      Link.Canon [st'.e.getD 0 0, st'.bm, st'.hv] ∧ st'.ub < P := by
    intro wv' hw' st' hst' hm2
    rcases List.mem_append.1 hw' with hw' | hw'
    · obtain ⟨b', hok'⟩ := Walk3.stepOk_of_mem hW hw' hst'
      have hab' := hok'.absB hm2
      have hc' := (hW.canon wv' hw').2.2 st' hst'
      refine ⟨?_, hc'.2.2.1⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Link.getD_lt hc'.2.2.2 0
      · have := hab'.2.1; unfold P; omega
      · have := hab'.2.2.1; unfold P; omega
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw'
      simp only [upsWalk, List.mem_map, List.mem_range] at hst'
      obtain ⟨j', hj', rfl⟩ := hst'
      refine ⟨?_, by simp only [stepOf]; exact rowLt hw ht _ _⟩
      intro x hx
      simp only [stepOf, List.mem_cons, List.not_mem_nil, or_false, List.getD_cons_zero] at hx
      rcases hx with rfl | rfl | rfl <;> exact rowLt hw ht _ _
  have hheadS : headSends hs B_BMAP = [] := by simp [headSends, B_BMAP, B_MIDROOT, B_PARENT, B_EDGE, B_DIGS]
  have hheadR : headRecvs hs B_BMAP = [] := by simp [headRecvs, B_BMAP, B_DIGEST, B_ROOT, B_EDGE]
  unfold Walk3.BusBal at hb
  rw [Walk3.walkSends3_bmap, Walk3.walkRecvs3_bmap, hheadS, hheadR, List.append_nil, List.append_nil] at hb
  let st := stepOf (s.row 3) 3
  have hprov : ∃ n, ∃ hn : n < vs.length, ∃ bm hv', vs[n].v.bmap = some (bm, hv') ∧
      [n, bm, hv'] = [st.e.getD 0 0, st.bm, st.hv] := by
    apply Classical.byContradiction; intro hno
    refine Walk3.chain_provided (k := 3) _ _ _ [st.e.getD 0 0, st.bm, st.hv] ?_ ?_ ?_ rfl
      (hwalkC (List.mem_append_right _ (List.mem_map.2 ⟨s, hs', rfl⟩)) st hst hmode).1 (u := st.ub) ?_ hb
    · intro m hm'
      have hm'' : m ∈ nodeSends3 vs B_BMAP ∨ m ∈ nodeRecvs3 vs B_BMAP := by
        rcases List.mem_append.mp hm' with h | h
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨n, hn, bm, hv', x, hbm, rfl⟩ := Walk3.mem_nodeBmap hm''
      have hsm := List.getElem_mem hn
      refine ⟨[n, bm, hv'], x, rfl, rfl, ?_, fun he => hno ⟨n, hn, bm, hv', hbm, he⟩⟩
      have hwf := hN.wf _ hsm
      generalize hvv : vs[n].v = vv at hbm hwf
      cases vv with
      | branch sv kids m =>
        simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
        obtain ⟨rfl, rfl⟩ := hbm
        exact Walk3.bmap_canon hwf.1 n (by have := hN.count; omega) sv
      | leaf => simp [NodeV3.bmap] at hbm
      | ext => simp [NodeV3.bmap] at hbm
    · intro p hp
      obtain ⟨wv', hw', hp'⟩ := List.mem_flatMap.mp hp
      obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hp'
      have hst'' := List.mem_filter.mp hst'
      have hm2 : st'.mode = 2 := by simpa using hst''.2
      exact ⟨rfl, (hwalkC hw' st' hst''.1 hm2).1, (hwalkC hw' st' hst''.1 hm2).2⟩
    · have := Walk3.flatMap_filter_len (fun st : WStep3 => decide (st.mode = 2))
        (fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)) (allWalks ws v)
      have h1 : ((allWalks ws v).flatMap (·.steps)).length = (ws.flatMap (·.steps)).length + 4 * v.length := by
        rw [allWalks, List.flatMap_append, List.length_append, upsWalks_len]
      have := segs_len hw
      omega
    · exact List.mem_flatMap.mpr ⟨upsWalk s, List.mem_append_right _ (List.mem_map.2 ⟨s, hs', rfl⟩),
        List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hmode⟩, rfl⟩⟩
  obtain ⟨n, hn, bm, hv', hbm, he⟩ := hprov
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨-, rfl, -⟩ := he
  have hwf := hN.wf _ (List.getElem_mem hn)
  generalize hvv : vs[n].v = vv at hbm hwf
  cases vv with
  | branch sv kids m =>
    simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
    obtain ⟨hb1, -⟩ := hbm
    have := Link3.kidBitmap_lt3 hwf.1
    show st.bm < 2 ^ 16
    rw [← hb1]; exact this
  | leaf => simp [NodeV3.bmap] at hbm
  | ext => simp [NodeV3.bmap] at hbm

/-- **All walks are well formed.** -/
theorem allWalks_wf {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR} {v : List UpsSeg}
    (hN : NodeWf3 vs) (hW : WalkWf3 ws) (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21) (hw : Wf v)
    (hbal : WalkBal vs hs ws v B_BMAP) : WalkWf3 (allWalks ws v) := by
  refine walkWf_app hW (fun wv hwv => ?_) ?_
  · obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hwv
    obtain ⟨ps, fls, wsl, hL⟩ := ups_layout hw s hs'
    exact (ups_walk hw hs' hL (ups_bm hN hW hWr hw hbal hs')).1
  · rw [List.flatMap_append, List.length_append, upsWalks_len]
    have := segs_len hw
    omega

/-- The `upsV3` walks never read `START` after `W0`. -/
theorem ups_sym (v : List UpsSeg) : ∀ wv ∈ v.map upsWalk, ∀ i, 1 ≤ i → i < wv.steps.length →
    (wv.step i).sym ≠ SYM_START := by
  intro wv hwv i h1 h2
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hwv
  rw [upsWalk_len] at h2
  rw [upsWalk_step s h2]
  simp only [stepOf]
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl <;> decide

/-- **The walk hypotheses for all walks** (`walkV3`'s and the `upsV3` segments'). -/
theorem ups_walkHyp {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {ws : List WalkR} {v : List UpsSeg}
    {prov : List Msg}
    (hN : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21) (hw : Wf v)
    (hb : Link3.ParentBal vs hs) (hvb : Link3.VParentBal vs es)
    (hE : WalkBal vs hs ws v B_EDGE) (hB : WalkBal vs hs ws v B_BMAP) (hK : Link3.KeynibOk ws prov)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256) (V' : List ValRec3) :
    Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs V' hs (allWalks ws v) :=
  Link3.walkHyp_any hN hhw hvw (allWalks_wf hN hW hWr hw hB) hb hvb (walkBal_all hw (Or.inl rfl) hE)
    (walkBal_all hw (Or.inr rfl) hB) hbytes
    (fun wv hwv => by
      rcases List.mem_append.1 hwv with h | h
      · exact Link3.hsym_of hW hK wv h
      · exact ups_sym v wv h) V'

/-! ## `tiLe` -/

/-- An edge moves the position by at most one. -/
theorem edge_I {n : Nat} {s : NodeS3} {e : Msg} (he : e ∈ edgesOf3 n s) : e.getD 4 0 ≤ e.getD 1 0 + 1 := by
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with (⟨i, -, rfl⟩ | he) | he
    · simp
    · cases sl <;> simp at he; subst he; simp
    · simp at he; subst he; simp
  | ext k kid m =>
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with ⟨i, -, rfl⟩ | he
    · simp
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        have := (Walk3.dropLast_x hl).2.1
        cases kid <;> simp [hl] at he <;> subst he <;> simp <;> omega
  | branch sv kids m =>
    rw [hv] at he
    simp only [List.mem_append, List.mem_filterMap] at he
    rcases he with ⟨⟨kd, j⟩, -, he⟩ | he
    · cases kd <;> simp at he; subst he; simp
    · cases sv with
      | none => simp at he
      | some sl => cases sl <;> simp at he; subst he; simp

/-- **`UpsExt0.tiLe`**: the terminal position is at most the number of steps before it. -/
theorem ups_tiLe {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3} {hs : List HeadE} {ws : List WalkR}
    {v : List UpsSeg} (G : Walk3.WalkHyp f vs V hs (allWalks ws v)) (hw : Wf v)
    {s : UpsSeg} (hs' : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx) :
    ti ≤ si := by
  have hwv : upsWalk s ∈ allWalks ws v := List.mem_append_right _ (List.mem_map.2 ⟨s, hs', rfl⟩)
  obtain ⟨hstep, -, -, -, -, hnI, -⟩ := ups_walkTerm hw hs' hL hP
  have i4 := hP.ix.2.2.2
  have F := fun i (hi : i < 4) => wRowF hw hs' hL i hi
  -- a step row moves the position by at most one
  have adv : ∀ i, 1 ≤ i → i ≤ si → s.row (i + 1) nI ≤ s.row i nI + 1 := by
    intro i h1 h2
    have hm := hstep i h1 h2
    have Fi := F i (by omega)
    have hsy := (Fi.stepE hm).1
    have hst := upsWalk_step s (i := i) (by omega)
    have hmode : ((upsWalk s).step i).mode ≤ 1 := by
      rw [hst]; have := (mode_cases Fi.modes i).1.2 hm; omega
    obtain ⟨st', -, he⟩ := Walk3.node_edge G hwv (i := i) (by rw [upsWalk_len]; omega) hmode
      (Or.inl (by
        rw [hst]; simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero, hsy]
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> decide))
    have hI := edge_I he
    rw [hst] at hI
    simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero] at hI
    have e := (Fi.stepN (by omega) hm).2.1
    rw [compactNext (by have := hL.walk.1; omega)] at e
    rw [e]
    exact hI
  have h1 : s.row 1 nI = 0 := by
    have F0 := F 0 (by omega)
    obtain ⟨hm0, -, -, h2, -, -⟩ := F0.start rfl
    have e := (F0.stepN (by omega) hm0).2.1
    rw [compactNext (by have := hL.walk.1; omega)] at e
    rw [e, h2]
  rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl
  · rw [← hnI]; exact Nat.le_of_eq h1
  · have a1 := adv 1 (by omega) (by omega)
    rw [← hnI]; omega
  · have a1 := adv 1 (by omega) (by omega); have a2 := adv 2 (by omega) (by omega)
    simp only [Nat.reduceAdd] at a1 a2 hnI
    rw [← hnI]; omega

end ZkFormal.NearV3.Render.UpsRelay.Extract
