import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsTerm
import ZkFormal.NearV3.Extract.Ups.UpsTermT
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR} {taus : List Nat}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws taus)
  {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

set_option maxHeartbeats 8000000 in
/-- **The terminal parts are the upsert at the terminal record.** -/
theorem ups_term :
    ∃ hN : s.row 0 (11 + di) < vs.length,
      (fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di))).upsert (UpsSpec.key.drop (si - ti))
          (sv (s.row 0 tau)) =
        some (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps)
          (nTof ci ti - 1)) := by
  have hw := E.ups
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  have hnT := nTof_pos ci i1 ti i2
  have hnT4 := nTof_le ci i1 ti i2
  have hlen := hP.len
  have hti := ups_tiLe E.walk hw hs hL hP
  -- terminal parts read `N_D`
  have srcT : ∀ j (hj : j < nTof ci ti), kd j ≠ 8 →
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)) := by
    intro j hj h8
    have hj' : j < ps.length := by omega
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; rfl
    obtain ⟨-, h1, h2, -, -, hsd, -⟩ := hP.term j hj' hj
    simp only [srcOf, hg]
    rw [(hP.src j hj' (by omega)).1, hsd]
  have hkdT : ∀ j (hj : j < nTof ci ti) (K : UKind), (termPlan (UCase.all.getD ci .LP) ti).getD j .RDB = K →
      kd j = K.ix := fun j hj K hK =>
    kd_eq _ (hP.part j (by omega)).1 K ((hP.term j (by omega) hj).1.trans hK)
  -- the record `N_D`
  have hNlt : s.row 0 (11 + di) < vs.length := by
    have hj : nTof ci ti - 1 < nTof ci ti := by omega
    have h8 : kd (nTof ci ti - 1) ≠ 8 := by
      intro h
      have := termLast ci i1 ti i2
      rw [← (hP.term _ (by omega) hj).1, h] at this
      exact this rfl
    have := part_sN E.node hw E.upb hs hL hP (nTof ci ti - 1) (by omega)
    obtain ⟨-, -, h2', -, -, hsd, -⟩ := hP.term (nTof ci ti - 1) (by omega) hj
    rwa [(hP.src (nTof ci ti - 1) (by omega) (by omega)).1, hsd] at this
  refine ⟨hNlt, ?_⟩
  have hTN := post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hNlt
  have hshape := ups_shape E hs hL hP
  have hok := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hNlt
  obtain ⟨tL, tE, tB⟩ := tn_cases (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
    (Link3.vpos (Link3.vid0 es)) vs[s.row 0 (11 + di)].v
  rw [← hTN] at tL tE tB
  -- the terminal row: the key read so far in `N_D`
  obtain ⟨hstepT, hT1, hT2, hT3, hci2, hnI, -, -, -, hK, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨-, -, -, hNT⟩ := ups_levels hw hs hL hP
  have RK := rowKey E.node E.head E.par E.walk hw hs hL hP (si + 1) (by omega) (Nat.le_refl _)
  rw [hNT, hnI] at RK
  obtain ⟨-, RK⟩ := RK
  rw [show si + 1 - 1 - ti = si - ti by omega] at RK
  obtain ⟨kL, kE, kB⟩ := RK _ (List.getElem?_eq_getElem hNlt)
  -- the terminal edge
  have tEdge : s.row (si + 1) mS = 1 ∨ s.row (si + 1) mK = 1 → (s.row (si + 1) nib ≠ SYM_START ∨
      s.row (si + 1) ek ≠ EK_DOWN) → [s.row 0 (11 + di), ti, s.row (si + 1) nib, s.row (si + 1) nN2,
        s.row (si + 1) nI2, s.row (si + 1) ek] ∈ edgesOf3 (s.row 0 (11 + di)) vs[s.row 0 (11 + di)] := by
    intro hm hnh
    obtain ⟨r, hr, he⟩ := rowEdge E.walk hw hs hL (si + 1) (by omega) hm hnh
    rw [hNT] at hr; rw [hNT, hnI] at he
    rw [List.getElem?_eq_getElem hNlt] at hr
    cases hr; exact he
  -- `MVE` keeps a non-empty key; an `ESx1` extension ends at `I + 1`
  have mveL : ∀ j (hj : j < ps.length), kd j = 7 → ∀ key c m,
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = .ext key c m → ti + 1 < key.length := by
    intro j hj h7 key c m hsj
    have hb := (ups_partsAllV E hs hL hP j hj).1
    have hq : upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) j =
        UpsSpec.qMVE key c m ti := by rw [upsQ_eq, h7, hsj]; rfl
    rw [hq] at hb
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape j hj
    obtain ⟨k', c', m', he', hI⟩ := s7 h7
    rw [hsj] at he'; simp only [NearSpec.PTrie.ext.injEq] at he'; obtain ⟨rfl, rfl, rfl⟩ := he'
    have hn := part_sN E.node hw E.upb hs hL hP j hj
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have ho := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hn
    simp only [srcOf, hg] at hsj
    rw [hsj] at ho
    exact mveLong hw hs hL hP j hj h7 key c m (ho.ext key c m rfl).2.2 hb hI
  have esxL : ∀ j (hj : j < ps.length), kd j = 10 → spXN ci = 1 → ∀ key c m,
      srcOf (Rpost vs es) (Vpost vs es pv) s ps j = .ext key c m → key.length = ti + 1 := by
    intro j hj h10 hX key c m hsj
    have hn := part_sN E.node hw E.upb hs hL hP j hj
    have hg : ps.getD j (0, 0) = ps[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have ho := post_nodeOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen hn
    simp only [srcOf, hg] at hsj
    rw [hsj] at ho
    have hTj := post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hn
    obtain ⟨-, tE', -⟩ := tn_cases (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
      (Link3.vpos (Link3.vid0 es)) vs[s.row ps[j].1 sN].v
    rw [← hTj] at tE'
    obtain ⟨kid, mB, hv⟩ := tE' key c m hsj
    have hwf := E.node.wf _ (List.getElem_mem hn)
    rw [hv] at hwf
    have hPb : postB vs (s.row ps[j].1 sN) = vs[s.row ps[j].1 sN].v.ser true := by
      simp only [postB]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    have hR : UpbReads s (postB vs) := fun i hi hrd => upb_reads E.node hw E.upb hs i hi hrd
    refine esx1Len hw hs hL hP j hj h10 hX (postB vs) hR key (ho.ext key c m rfl).2.1 ?_ ?_
    · rw [hPb,hv]
      have hb : (kid.bytes true).length=32 := by
        cases kid with
        | none => exact absurd rfl hwf.2.1
        | hash h => exact hwf.2.2.1
        | node n l r pre po => exact hwf.2.2.1.2
      simp [NodeV3.ser, u32Bytes_length, hpN, UpsSpec.hp_len, hb, hwf.2.2.2]
      omega
    · rw [hPb, hv]; exact ser5_ext key kid mB hwf.1
  generalize hval : sv (s.row 0 tau) = val
  generalize hsrc : srcOf (Rpost vs es) (Vpost vs es pv) s ps = src at srcT hshape mveL esxL
  generalize hTT : fullTree (Rpost vs es) (Vpost vs es pv) (s.row 0 (11 + di)) = TN at srcT tL tE tB hok
  generalize hrv : vs[s.row 0 (11 + di)].v = rv at kL kE kB tL tE tB tEdge
  -- common facts
  have hXl : ∀ t, t ≤ si → (UpsSpec.key.drop (si - t)).length = 2 - si + t := by
    intro t ht; simp [UpsSpec.key]; omega
  have hkey' := key'_drop ti si hti
  have Q0 := upsQ_zero ci si ti (s.row 0 tX) val kd sdx src
  have Qn := fun j (hj : 1 ≤ j) => upsQ_next ci si ti (s.row 0 tX) val kd sdx src j hj
  have F := wRowF hw hs hL (si + 1) (by omega)
  have hseg := hP.seg 0 (by have := hL.walk.1; omega)
  have spbF : 4 ≤ ci → s.row 0 tX < 16 ∧ (spYN ci = 1 → si ≤ 1) := by
    intro h4
    obtain ⟨c1, -, -, c4⟩ := hseg
    obtain ⟨a, -, -, b⟩ := spbSeg (okRow hw hs (i := 0) (by have := hL.walk.1; omega)) (rowLt hw hs _)
      (nextLt hw hs _) hL.walk.2.1 c1 c4 h4 (by omega) i4
    exact ⟨a, b⟩
  have keyT : 4 ≤ ci → ci ≠ 4 →
      (∀ k sl m, rv = .leaf k sl m → ti < k.length ∧ k.getD ti 0 = s.row 0 tX) ∧
      (∀ k kid m, rv = .ext k kid m → ti < k.length ∧ k.getD ti 0 = s.row 0 tX) := by
    intro h4 hne
    obtain ⟨hekK, hnib⟩ := (hK h4).2 hne
    have hm : s.row (si + 1) mK = 1 := by rw [hT3, if_pos h4]
    have he := tEdge (Or.inr hm) (Or.inr (by rw [hekK]; decide))
    have hσ : s.row (si + 1) nib < 16 := by
      rw [hnib, hL.segc _ (by have := hL.walk.1; omega) tX (by decide)]; exact (spbF h4).1
    have C := stepEdge he (by simpa using hσ) (Or.inr (by simpa using hekK))
    simp only [List.getD_cons_succ, List.getD_cons_zero] at C
    rw [hrv, hnib, hL.segc _ (by have := hL.walk.1; omega) tX (by decide)] at C
    refine ⟨fun k sl m hv => ?_, fun k kid m hv => ?_⟩ <;> rw [hv] at C
    · rcases C with ⟨_, _, _, _, _, _, _, _, h, -⟩ | ⟨k', _, _, h, h1, h2, -⟩ | ⟨_, _, _, h, -⟩ <;>
        simp at h
      obtain ⟨rfl, -⟩ := h; exact ⟨h1, h2⟩
    · rcases C with ⟨_, _, _, _, _, _, _, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨k', _, _, h, h1, h2, -⟩ <;>
        simp at h
      obtain ⟨rfl, -⟩ := h; exact ⟨h1, h2⟩
  have getI : ∀ (k : List Nat) (h : ti < k.length), k.getD ti 0 = s.row 0 tX → k[ti] = s.row 0 tX := by
    intro k h e; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] at e; exact e
  have planK : ∀ j (hj : j < nTof ci ti) (K : UKind), (termPlan (UCase.all.getD ci .LP) ti).getD j .RDB = K →
      kd j = K.ix := hkdT
  rcases (show ci = 0 ∨ ci = 1 ∨ ci = 2 ∨ ci = 3 ∨ ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10
    by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `LP`: a present leaf
    have hn : nTof 0 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 2 := planK 0 (by omega) .RLP (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := hci2 (by omega)
    obtain ⟨-, -, s2, -⟩ := hshape 0 (by omega)
    obtain ⟨k, sl, m, hT⟩ := s2 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    have hm3 : s.row (si + 1) mS = 1 := by rw [hT1]; simp
    have hekV := (F.stepE hm3).2.2 (by omega)
    have he := tEdge (Or.inl hm3) (Or.inl (by rw [(F.stepE hm3).1, show si + 1 = 3 by omega]; decide))
    rcases edge_val he (by simpa using hekV) with ⟨k', sl'', m'', hv', hp⟩ | ⟨sl'', kids, m'', hv', hp⟩
    · rw [hrv, hv] at hv'; simp only [NodeV3.leaf.injEq] at hv'; obtain ⟨rfl, -⟩ := hv'
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
      obtain ⟨-, htk⟩ := kL k sl' mB hv
      have hl := hXl ti hti
      have hkk : k = UpsSpec.key.drop (si - ti) := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at htk; exact htk
      rw [hn, Q0, k0, srcT 0 (by omega) (by omega), hT, ← hkk]
      simp only [qPart]; exact upsert_rlp k sl m val
    · rw [hrv, hv] at hv'; cases hv'
  · -- `BR`: a branch value replaced
    have hn : nTof 1 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 3 := planK 0 (by omega) .RBR (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := hci2 (by omega)
    obtain ⟨-, -, -, s3, -⟩ := hshape 0 (by omega)
    obtain ⟨sl, cs, m, hT⟩ := s3 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    rw [hn, Q0, k0, srcT 0 (by omega) (by omega), hT, hsi, h0]
    simp only [qPart]; exact upsert_rbr sl cs m val
  · -- `BV`: a branch value set
    have hn : nTof 2 ti = 1 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k0 : kd 0 = 4 := planK 0 (by omega) .RBV (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, s4, -⟩ := hshape 0 (by omega)
    obtain ⟨cs, m, hT⟩ := s4 k0
    rw [srcT 0 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    rw [hn, Q0, k0, srcT 0 (by omega) (by omega), hT, hsi, h0]
    simp only [qPart]; exact upsert_rbv cs m val
  · -- `BI`: an empty slot
    have hn : nTof 3 ti = 2 := by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have k1 : kd 1 = 5 := planK 1 (by omega) .RBI (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi := rbiSi hw hs hL hP 1 (by omega) k1
    obtain ⟨-, -, -, -, -, s5, -⟩ := hshape 1 (by omega)
    obtain ⟨bv, cs, m, hT, hy⟩ := s5 k1
    rw [srcT 1 (by omega) (by omega)] at hT
    obtain ⟨sv', kids, mB, hv⟩ := tB _ cs m hT
    have h0 := kB sv' kids mB hv
    have h16 := (hok.branch bv cs m hT).1
    rw [hn, show 2 - 1 = 1 from rfl, Qn 1 (Nat.le_refl _), k1, srcT 1 (by omega) (by omega), hT, h0,
      Nat.sub_zero]
    simp only [qPart]
    exact upsert_rbi bv cs m si val (by omega) (by rw [h16]; rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide) hy
  · -- `LSa`
    have hn : nTof 4 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 1 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT⟩ := (s10 k1).1 rfl
    rw [srcT 1 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨-, htk⟩ := kL k sl' mB hv
    have hm : s.row (si + 1) mK = 1 := by rw [hT3, if_pos (by omega)]
    have hekL := (hK (by omega)).1 rfl
    have he := tEdge (Or.inr hm) (Or.inr (by rw [hekL]; decide))
    obtain ⟨k', sl'', m'', hv', hp⟩ := edge_lendAt he (by simpa using hekL)
    rw [hrv, hv] at hv'; simp only [NodeV3.leaf.injEq] at hv'; obtain ⟨rfl, -⟩ := hv'
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
    have hl := hXl ti hti
    have hsplit := split_LSa k _ val ti si htk hkey' sl m (upsQ 4 si ti (s.row 0 tX) val kd sdx src 0) (s.row 0 tX)
      hp.symm (by omega)
    rw [wexTop 4 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk, Qn 1 (Nat.le_refl _), k1,
      srcT 1 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_leafSplit k sl m _ val (ne_of_len (by omega))
  · -- `LSb`
    have hn : nTof 5 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 6 := planK 0 (by rw [hn]; split <;> omega) .MVL
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, s6, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT, hI⟩ := s6 k0
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨-, htk⟩ := kL k sl' mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).1 k sl' mB hv
    have hl := hXl ti hti
    have hsplit := split_LSb k _ val ti si htk hkey' sl m hlt hsi
    rw [getI k hlt hx] at hsplit
    rw [wexTop 5 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk, Qn 1 (Nat.le_refl _), k1,
      srcT 1 (by rw [hn]; split <;> omega) (by omega), Q0, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_leafSplit k sl m _ val (ne_of_len (by omega))
  · -- `LSc`
    have hn : nTof 6 ti = 3 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 3 = 9 := fun h => planK 3 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 6 := planK 0 (by rw [hn]; split <;> omega) .MVL
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k2 : kd 2 = 10 := planK 2 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 6) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, s6, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, sl, m, hT, hI⟩ := s6 k0
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨sl', mB, hv⟩ := tL k sl m hT
    obtain ⟨-, htk⟩ := kL k sl' mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).1 k sl' mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hsplit := split_LSc k _ val ti si htk hkey' sl m hlt (by omega) hxk
    rw [getI k hlt hx] at hsplit
    rw [wexTop 6 si ti (s.row 0 tX) val kd sdx src 3 (by omega) hn hkW k htk, Qn 2 (by omega), k2,
      srcT 2 (by rw [hn]; split <;> omega) (by omega), Q0, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_leafSplit k sl m _ val (ne_of_get hlt hly (by rw [hy]; exact hxk))
  · -- `ESl0`
    have hn : nTof 7 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 7 := planK 0 (by rw [hn]; split <;> omega) .MVE
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT, hI⟩ := s7 k0
    have hlong := mveL 0 (by rw [hlen, hn]; split <;> omega) k0 k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    have hl := hXl ti hti
    have hsplit := split_ESl0 k _ val ti si htk hkey' c m hlong hsi
    rw [getI k hlt hx] at hsplit
    rw [wexTop 7 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk, Qn 1 (Nat.le_refl _), k1,
      srcT 1 (by rw [hn]; split <;> omega) (by omega), Q0, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_extSplit k c m _ val (take_ne_of_len (by omega))
  · -- `ESl1`
    have hn : nTof 8 ti = 1 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 1 = 9 := fun h => planK 1 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 10 := planK 0 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si = 2 := w3Si hw hs hL hP (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT⟩ := (s10 k0).2 (by decide)
    have hkl := esxL 0 (by rw [hlen, hn]; split <;> omega) k0 (by decide) k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    have hl := hXl ti hti
    have hsplit := split_ESl1 k _ val ti si htk hkey' c m (.hash []) hkl.symm hsi
    rw [getI k hlt hx] at hsplit
    rw [wexTop 8 si ti (s.row 0 tX) val kd sdx src 1 (Nat.le_refl _) hn hkW k htk, Q0, k0,
      srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_extSplit k c m _ val (take_ne_of_len (by omega))
  · -- `ESn0`
    have hn : nTof 9 ti = 3 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 3 = 9 := fun h => planK 3 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k0 : kd 0 = 7 := planK 0 (by rw [hn]; split <;> omega) .MVE
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have k2 : kd 2 = 10 := planK 2 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 9) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, -, s7, -⟩ := hshape 0 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT, hI⟩ := s7 k0
    have hlong := mveL 0 (by rw [hlen, hn]; split <;> omega) k0 k c m hT
    rw [srcT 0 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hsplit := split_ESn0 k _ val ti si htk hkey' c m hlong (by omega) hxk
    rw [getI k hlt hx] at hsplit
    rw [wexTop 9 si ti (s.row 0 tX) val kd sdx src 3 (by omega) hn hkW k htk, Qn 2 (by omega), k2,
      srcT 2 (by rw [hn]; split <;> omega) (by omega), Q0, k0, srcT 0 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_extSplit k c m _ val (take_ne_of_get hlt hly (by rw [hy]; exact hxk))
  · -- `ESn1`
    have hn : nTof 10 ti = 2 + (if 1 ≤ ti then 1 else 0) := by
      rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide
    have hkW : 1 ≤ ti → kd 2 = 9 := fun h => planK 2 (by rw [hn, if_pos h]; omega) .WEX
      (by rcases (show ti = 1 ∨ ti = 2 by omega) with rfl | rfl <;> decide)
    have k1 : kd 1 = 10 := planK 1 (by rw [hn]; split <;> omega) .SPB
      (by rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> decide)
    have hsi : si ≤ 1 := (spbF (by omega)).2 (by decide)
    have hxy := ups_xy hw hs hL hP (ci := 10) (by decide) (by decide)
    obtain ⟨-, -, -, -, -, -, -, -, s10, -⟩ := hshape 1 (by rw [hlen, hn]; split <;> omega)
    obtain ⟨k, c, m, hT⟩ := (s10 k1).2 (by decide)
    have hkl := esxL 1 (by rw [hlen, hn]; split <;> omega) k1 (by decide) k c m hT
    rw [srcT 1 (by rw [hn]; split <;> omega) (by omega)] at hT
    obtain ⟨kid, mB, hv⟩ := tE k c m hT
    obtain ⟨-, htk⟩ := kE k kid mB hv
    obtain ⟨hlt, hx⟩ := (keyT (by omega) (by omega)).2 k kid mB hv
    obtain ⟨hly, hy⟩ := key'_y hkey' (by omega)
    have hxk : k[ti] ≠ UpsSpec.yOf si := by rw [getI k hlt hx]; exact hxy
    have hsplit := split_ESn1 k _ val ti si htk hkey' c m (upsQ 10 si ti (s.row 0 tX) val kd sdx src 0)
      hkl.symm (by omega) hxk
    rw [getI k hlt hx] at hsplit
    rw [wexTop 10 si ti (s.row 0 tX) val kd sdx src 2 (by omega) hn hkW k htk, Qn 1 (Nat.le_refl _), k1,
      srcT 1 (by rw [hn]; split <;> omega) (by omega), hT]
    simp only [qPart]
    rw [← hsplit]
    exact upsert_extSplit k c m _ val (take_ne_of_get hlt hly (by rw [hy]; exact hxk))

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
