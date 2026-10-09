import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsRoot
import ZkFormal.NearV3.Extract.Ups.UpsKey
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {vs : List NodeS3} {hds : List HeadE}

/-- **A record's `res` is a record at least as deep**, strictly deeper unless it is the record itself. -/
theorem res_depth (hN : NodeWf3 vs) (hhw : HeadWf hds) (hb : Link3.ParentBal vs hds) :
    ∀ n (hn : n < vs.length), ∃ hr : vs[n].res < vs.length,
      vs[n].depth ≤ vs[vs[n].res].depth ∧ (vs[n].res ≠ n → vs[n].depth < vs[vs[n].res].depth) := by
  suffices H : ∀ t n (hn : n < vs.length), 400 - vs[n].depth = t → ∃ hr : vs[n].res < vs.length,
      vs[n].depth ≤ vs[vs[n].res].depth ∧ (vs[n].res ≠ n → vs[n].depth < vs[vs[n].res].depth) by
    intro n hn; exact H _ n hn rfl
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  intro n hn ht
  rcases Walk3.resOk_cases (hN.res n hn) with h | ⟨c, l, cr, pre, po, m, hv, h⟩
  · have e : vs[n].res = n := h
    refine ⟨by rw [e]; exact hn, ?_, fun hne => absurd e hne⟩
    simp only [e, Nat.le_refl]
  · have hk : (c, l, cr, pre, po) ∈ vs[n].v.revealed := by rw [hv]; simp [NodeV3.revealed]
    obtain ⟨hc, -, hd, hres⟩ := Link3.kid_depth hN hhw hb hn hk
    have h1 := Link3.depth_lt hN hhw hb hn
    have h2 := Link3.depth_lt hN hhw hb hc
    obtain ⟨hr, hle, -⟩ := ih (400 - vs[c].depth) (by omega) c hc rfl
    have e : vs[n].res = vs[c].res := by rw [h, hres]
    simp only [e]
    exact ⟨hr, by omega, fun _ => by omega⟩

end

theorem take_succ_of {k X : List Nat} {p : Nat} (h : k.take p = X.take p) (hk : p < k.length) (hX : p < X.length)
    (he : k.getD p 0 = X.getD p 0) : k.take (p + 1) = X.take (p + 1) := by
  rw [List.take_add_one, List.take_add_one, h, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hX]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hX,
    Option.getD_some] at he
  rw [he]

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {ws : List WalkR} {v : List UpsSeg}
  (hN : NodeWf3 vs) (hhw : HeadWf hds) (hb : Link3.ParentBal vs hds)
  (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hds (allWalks ws v)) (hw : Wf v)
  {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)

theorem wsym_lt (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ 2) : wsym i < 16 := by
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> decide

theorem wsym_key (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ 2) : UpsSpec.key.getD (i - 1) 0 = wsym i := by
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> rfl

include hN hhw hb G hw hs hL hP

/-- **A step row**: without `enter` it advances along its record's key; with `enter` it descends into a
revealed child whose `res` is the next row's record. -/
theorem stepRow (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ si) :
    ∃ r, vs[s.row i nN]? = some r ∧ s.row i enter ≤ 1 ∧ s.row (i + 1) mS + s.row (i + 1) mK + s.row (i + 1) mB = 1 ∧
    (s.row i enter = 0 → s.row (i + 1) nN = s.row i nN ∧ s.row (i + 1) nI = s.row i nI + 1 ∧
      ((∃ k sl m, r.v = .leaf k sl m ∧ s.row i nI < k.length ∧ k.getD (s.row i nI) 0 = wsym i) ∨
       (∃ k kid m, r.v = .ext k kid m ∧ s.row i nI < k.length ∧ k.getD (s.row i nI) 0 = wsym i))) ∧
    (s.row i enter = 1 → s.row (i + 1) nI = 0 ∧ ∃ c l cr pre po, cr = s.row (i + 1) nN ∧
      (∃ hc : c < vs.length, vs[c].res = cr ∧ vs[c].depth = r.depth + 1) ∧
      ((∃ sv kids m, r.v = .branch sv kids m ∧ s.row i nI = 0 ∧ kids[wsym i]? = some (NKid.node c l cr pre po)) ∨
       (∃ k m, r.v = .ext k (NKid.node c l cr pre po) m ∧ s.row i nI + 1 = k.length ∧
         k.getD (s.row i nI) 0 = wsym i))) := by
  have i4 := hP.ix.2.2.2
  obtain ⟨hstep, -⟩ := ups_walkTerm hw hs hL hP
  have hm := hstep i h1 h2
  have F := wRowF hw hs hL i (by omega)
  have nx := compactNext (s:=s) (i := i) (by have := hL.walk.1; omega)
  obtain ⟨hsy, hek, -⟩ := F.stepE hm
  have hek := hek (by omega)
  obtain ⟨hnN, hnI, hmn⟩ := F.stepN (by omega) hm
  rw [nx] at hnN hnI hmn
  obtain ⟨-, -, -, hlev, -⟩ := ups_walkLev hw hs hL
  obtain ⟨he1, hent1, hent0, -⟩ := hlev i (by omega) hm
  obtain ⟨r, hr, he⟩ := rowEdge G hw hs hL i (by omega) (Or.inl hm) (Or.inl (by rw [hsy]; rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> decide))
  have hσ : s.row i nib < 16 := by rw [hsy]; exact wsym_lt i h1 (by omega)
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 hr
  have C := stepEdge he (by simpa using hσ) (by simpa using hek)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at C
  rw [hsy] at C
  refine ⟨_, hr, he1, hmn, fun h0 => ?_, fun h1' => ?_⟩
  · -- no `enter`: the landing is the same record
    have hsame := hent0 h0
    rcases C with ⟨sv, kids, m, c, l, cr, pre, po, hv, hk, hI, h3, h4⟩ | ⟨k, sl, m, hv, hI, hx, h3, h4⟩ |
      ⟨k, kid, m, hv, hI, hx, ⟨h3, h4⟩ | ⟨hlast, c, l, cr, pre, po, hkid, h3, h4⟩⟩
    · exfalso
      have hrev : (c, l, cr, pre, po) ∈ vs[s.row i nN].v.revealed := by
        rw [hv]; simp only [NodeV3.revealed, List.mem_filterMap]; exact ⟨_, List.mem_of_getElem? hk, rfl⟩
      obtain ⟨hc, -, hd, hres⟩ := Link3.kid_depth hN hhw hb hn hrev
      obtain ⟨hcr, hle, -⟩ := res_depth hN hhw hb c hc
      have : cr = s.row i nN := by rw [← h3, hsame]
      simp only [hres, this] at hle hcr
      omega
    · exact ⟨by rw [hnN, hsame], by rw [hnI, h4], Or.inl ⟨k, sl, m, hv, hI, hx⟩⟩
    · exact ⟨by rw [hnN, hsame], by rw [hnI, h4], Or.inr ⟨k, kid, m, hv, hI, hx⟩⟩
    · exfalso
      have hrev : (c, l, cr, pre, po) ∈ vs[s.row i nN].v.revealed := by rw [hv, hkid]; simp [NodeV3.revealed]
      obtain ⟨hc, -, hd, hres⟩ := Link3.kid_depth hN hhw hb hn hrev
      obtain ⟨hcr, hle, -⟩ := res_depth hN hhw hb c hc
      have : cr = s.row i nN := by rw [← h3, hsame]
      simp only [hres, this] at hle hcr
      omega
  · -- `enter`: a descend into a revealed child
    have hz := hent1 h1'
    refine ⟨by rw [hnI, hz], ?_⟩
    rcases C with ⟨sv, kids, m, c, l, cr, pre, po, hv, hk, hI, h3, h4⟩ | ⟨k, sl, m, hv, hI, hx, h3, h4⟩ |
      ⟨k, kid, m, hv, hI, hx, ⟨h3, h4⟩ | ⟨hlast, c, l, cr, pre, po, hkid, h3, h4⟩⟩
    · have hrev : (c, l, cr, pre, po) ∈ vs[s.row i nN].v.revealed := by
        rw [hv]; simp only [NodeV3.revealed, List.mem_filterMap]; exact ⟨_, List.mem_of_getElem? hk, rfl⟩
      obtain ⟨hc, -, hd, hres⟩ := Link3.kid_depth hN hhw hb hn hrev
      exact ⟨c, l, cr, pre, po, by rw [hnN, h3], ⟨hc, hres, hd⟩, Or.inl ⟨sv, kids, m, hv, hI, hk⟩⟩
    · exfalso; rw [hz] at h4; omega
    · exfalso; rw [hz] at h4; omega
    · have hrev : (c, l, cr, pre, po) ∈ vs[s.row i nN].v.revealed := by rw [hv, hkid]; simp [NodeV3.revealed]
      obtain ⟨hc, -, hd, hres⟩ := Link3.kid_depth hN hhw hb hn hrev
      subst hkid
      exact ⟨c, l, cr, pre, po, by rw [hnN, h3], ⟨hc, hres, hd⟩, Or.inr ⟨k, m, hv, hlast, hx⟩⟩


/-- The level one-hots of rows 2 and 3 from the `enter` flags. -/
theorem lv23 : (1 ≤ si → s.row 1 enter ≤ 1 ∧ s.row 2 lv0 + s.row 1 enter = 1 ∧ s.row 2 lv1 = s.row 1 enter ∧
      s.row 2 lv2 = 0) ∧
    (2 ≤ si → s.row 2 enter ≤ 1 ∧
      ((s.row 1 enter = 0 ∧ s.row 2 enter = 0 ∧ s.row 3 lv0 = 1 ∧ s.row 3 lv1 = 0 ∧ s.row 3 lv2 = 0) ∨
       (s.row 1 enter = 0 ∧ s.row 2 enter = 1 ∧ s.row 3 lv0 = 0 ∧ s.row 3 lv1 = 1 ∧ s.row 3 lv2 = 0) ∨
       (s.row 1 enter = 1 ∧ s.row 2 enter = 0 ∧ s.row 3 lv0 = 0 ∧ s.row 3 lv1 = 1 ∧ s.row 3 lv2 = 0) ∨
       (s.row 1 enter = 1 ∧ s.row 2 enter = 1 ∧ s.row 3 lv0 = 0 ∧ s.row 3 lv1 = 0 ∧ s.row 3 lv2 = 1))) := by
  obtain ⟨hstep, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨a0, a1, a2, hlev, -⟩ := ups_walkLev hw hs hL
  have lt := fun i x => rowLt hw hs i x
  have hPl := P_lit
  have row2 : 1 ≤ si → s.row 1 enter ≤ 1 ∧ s.row 2 lv0 + s.row 1 enter = 1 ∧ s.row 2 lv1 = s.row 1 enter ∧
      s.row 2 lv2 = 0 := by
    intro h1
    obtain ⟨he, -, -, r0, r1, r2⟩ := hlev 1 (Or.inl rfl) (hstep 1 (Nat.le_refl _) h1)
    simp only [a0, a1, a2, Nat.reduceAdd, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] at r0 r1 r2
    have := lt 2 lv0; have := lt 2 lv1; have := lt 2 lv2; have := lt 1 enter
    rw [hPl] at *
    exact ⟨he, by omega, by omega, by omega⟩
  refine ⟨row2, fun h2 => ?_⟩
  obtain ⟨he1, l0, l1, l2⟩ := row2 (by omega)
  obtain ⟨he2, -, -, q0, q1, q2⟩ := hlev 2 (Or.inr rfl) (hstep 2 (by omega) h2)
  simp only [Nat.reduceAdd] at q0 q1 q2
  have := lt 3 lv0; have := lt 3 lv1; have := lt 3 lv2
  rw [hPl] at *
  refine ⟨he2, ?_⟩
  rcases (show s.row 1 enter = 0 ∨ s.row 1 enter = 1 by omega) with h | h <;>
  rcases (show s.row 2 enter = 0 ∨ s.row 2 enter = 1 by omega) with h' | h' <;>
    simp only [h'] at q0 q1 q2 <;>
    simp only [l1, l2, show s.row 2 lv0 = 1 - s.row 1 enter by omega, h] at q0 q1 q2 <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero] at q0 q1 q2 <;>
    omega

/-- **The rows' records**: row 1 is `N_0`; each `enter` moves to the next path record; `D` counts them. -/
theorem ups_lvl : s.row 1 nN = s.row 0 (11 + 0) ∧ s.row 1 nI = 0 ∧
    (1 ≤ si → s.row 1 enter ≤ 1 ∧ s.row 2 nN = s.row 0 (11 + s.row 1 enter)) ∧
    (2 ≤ si → s.row 2 enter ≤ 1 ∧ s.row 3 nN = s.row 0 (11 + (s.row 1 enter + s.row 2 enter))) ∧
    di = (if si = 0 then 0 else if si = 1 then s.row 1 enter else s.row 1 enter + s.row 2 enter) := by
  obtain ⟨hstep, hT1, hT2, hT3, -, -, hl0, hl1, hl2, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨a0, a1, a2, -, hnN⟩ := ups_walkLev hw hs hL
  obtain ⟨-, -, i3, i4⟩ := hP.ix
  obtain ⟨R2, R3⟩ := lv23 hN hhw hb G hw hs hL hP
  have F := fun i (hi : i < 4) => (wRowF hw hs hL i hi).modes
  have sN := segN hw hs hL
  have hsumT : s.row (si + 1) mS + s.row (si + 1) mK + s.row (si + 1) mB = 1 := by
    rw [hT1, hT2, hT3]; split <;> split <;> split <;> omega
  have sum1 : ∀ i, 1 ≤ i → i ≤ si + 1 → s.row i mS + s.row i mK + s.row i mB = 1 := by
    intro i h1 h2
    rcases Nat.lt_or_ge i (si + 1) with h | h
    · have := hstep i h1 (by omega); have := F i (by omega); omega
    · rw [show i = si + 1 by omega]; exact hsumT
  have rowN : ∀ i, 1 ≤ i → i ≤ si + 1 → ∀ d, d < 3 → s.row i lv0 = (if d = 0 then 1 else 0) →
      s.row i lv1 = (if d = 1 then 1 else 0) → s.row i lv2 = (if d = 2 then 1 else 0) →
      s.row i nN = s.row 0 (11 + d) := by
    intro i h1 h2 d hd e0 e1 e2
    have := hnN i h1 (by omega) (sum1 i h1 h2) (by rw [e0, e1, e2]; split <;> split <;> split <;> omega)
    rw [show N0 = 11 + 0 from rfl, show N1 = 11 + 1 from rfl, show N2 = 11 + 2 from rfl, e0, e1, e2,
      sN i (by omega) 0 (by omega), sN i (by omega) 1 (by omega), sN i (by omega) 2 (by omega)] at this
    rw [this]; rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> simp
  have hI1 : s.row 1 nI = 0 := by
    have F0 := wRowF hw hs hL 0 (by omega)
    obtain ⟨hm0, -, -, h2, -, -⟩ := F0.start rfl
    have e := (F0.stepN (by omega) hm0).2.1
    rw [compactNext (s:=s) (by have := hL.walk.1; omega)] at e
    rw [e, h2]
  refine ⟨rowN 1 (Nat.le_refl _) (by omega) 0 (by omega) (by simpa using a0) (by simpa using a1) (by simpa using a2),
    hI1, fun h1 => ?_, fun h2 => ?_, ?_⟩
  · obtain ⟨he, l0, l1, l2⟩ := R2 h1
    refine ⟨he, ?_⟩
    rcases (show s.row 1 enter = 0 ∨ s.row 1 enter = 1 by omega) with h | h <;> rw [h] at l0 l1 ⊢
    · exact rowN 2 (by omega) (by omega) 0 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
    · exact rowN 2 (by omega) (by omega) 1 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
  · obtain ⟨he2, C⟩ := R3 h2
    refine ⟨he2, ?_⟩
    rcases C with ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ <;>
      rw [e1, e2]
    · exact rowN 3 (by omega) (by omega) 0 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
    · exact rowN 3 (by omega) (by omega) 1 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
    · exact rowN 3 (by omega) (by omega) 1 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
    · exact rowN 3 (by omega) (by omega) 2 (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
  · rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl
    · simp only [Nat.reduceAdd] at hl0; rw [a0] at hl0; simp; split at hl0 <;> omega
    · obtain ⟨he, l0, l1, l2⟩ := R2 (by omega)
      simp only [Nat.reduceAdd] at hl0 hl1 hl2
      simp only [show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
      split at hl0 <;> split at hl1 <;> split at hl2 <;> omega
    · obtain ⟨-, C⟩ := R3 (by omega)
      simp only [Nat.reduceAdd] at hl0 hl1 hl2
      simp only [show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false]
      rcases C with ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ | ⟨e1, e2, x0, x1, x2⟩ <;>
        rw [e1, e2] <;> split at hl0 <;> split at hl1 <;> split at hl2 <;> omega

/-- The key fact of a row: the record's key prefix up to the position is the key read in that record. -/
def KeyAt (vs : List NodeS3) (n p i : Nat) : Prop :=
  p + 1 ≤ i ∧ ∀ r, vs[n]? = some r →
    (∀ k sl m, r.v = .leaf k sl m → p ≤ k.length ∧ k.take p = (UpsSpec.key.drop (i - 1 - p)).take p) ∧
    (∀ k kid m, r.v = .ext k kid m → p ≤ k.length ∧ k.take p = (UpsSpec.key.drop (i - 1 - p)).take p) ∧
    (∀ sv kids m, r.v = .branch sv kids m → p = 0)

/-- **Key prefix along the rows** (`1 ≤ i ≤ t*`). -/
theorem rowKey : ∀ i, 1 ≤ i → i ≤ si + 1 → KeyAt vs (s.row i nN) (s.row i nI) i := by
  obtain ⟨-, hI1, -, -, -⟩ := ups_lvl hN hhw hb G hw hs hL hP
  have i4 := hP.ix.2.2.2
  have zero : ∀ n i, 1 ≤ i → KeyAt vs n 0 i := by
    intro n i h1
    refine ⟨by omega, fun r _ => ⟨fun k sl m _ => ⟨by omega, by simp⟩, fun k kid m _ => ⟨by omega, by simp⟩,
      fun _ _ _ _ => rfl⟩⟩
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hI1]; exact zero _ _ (Nat.le_refl _)
    obtain ⟨r, hr, -, -, h0, h1'⟩ := stepRow hN hhw hb G hw hs hL hP i hpos (by omega)
    have IH := ih hpos (by omega)
    rcases (show s.row i enter = 0 ∨ s.row i enter = 1 by
      have := (stepRow hN hhw hb G hw hs hL hP i hpos (by omega)).choose_spec.2.1; omega) with he | he
    · obtain ⟨hnN, hnI, hk⟩ := h0 he
      rw [hnN, hnI]
      obtain ⟨hp, hall⟩ := IH
      obtain ⟨hL', hE', hB'⟩ := hall r hr
      have hpi : s.row i nI + 1 ≤ i := hp
      have hkey : ∀ k : List Nat, k.getD (s.row i nI) 0 = wsym i →
          k.getD (s.row i nI) 0 = (UpsSpec.key.drop (i + 1 - 1 - (s.row i nI + 1))).getD (s.row i nI) 0 := by
        intro k hx
        rw [hx, show i + 1 - 1 - (s.row i nI + 1) = i - 1 - s.row i nI by omega, List.getD_eq_getElem?_getD,
          List.getElem?_drop, show i - 1 - s.row i nI + s.row i nI = i - 1 by omega, ← List.getD_eq_getElem?_getD,
          wsym_key i (by omega) (by omega)]
      have hXl : s.row i nI < (UpsSpec.key.drop (i - 1 - s.row i nI)).length := by
        simp [UpsSpec.key]; omega
      refine ⟨by omega, fun r' hr' => ?_⟩
      rw [hr] at hr'; cases hr'
      rcases hk with ⟨k, sl, m, hv, hlt, hx⟩ | ⟨k, kid, m, hv, hlt, hx⟩
      · obtain ⟨-, hT⟩ := hL' k sl m hv
        refine ⟨fun k' sl' m' hv' => ?_, fun _ _ _ hv' => (by rw [hv] at hv'; cases hv'),
          fun _ _ _ hv' => (by rw [hv] at hv'; cases hv')⟩
        rw [hv] at hv'; cases hv'
        refine ⟨by omega, ?_⟩
        rw [show i + 1 - 1 - (s.row i nI + 1) = i - 1 - s.row i nI by omega]
        exact take_succ_of hT hlt hXl (by rw [hkey k hx, show i + 1 - 1 - (s.row i nI + 1) = i - 1 - s.row i nI by omega])
      · obtain ⟨-, hT⟩ := hE' k kid m hv
        refine ⟨fun _ _ _ hv' => (by rw [hv] at hv'; cases hv'), fun k' kid' m' hv' => ?_,
          fun _ _ _ hv' => (by rw [hv] at hv'; cases hv')⟩
        rw [hv] at hv'; cases hv'
        refine ⟨by omega, ?_⟩
        rw [show i + 1 - 1 - (s.row i nI + 1) = i - 1 - s.row i nI by omega]
        exact take_succ_of hT hlt hXl (by rw [hkey k hx, show i + 1 - 1 - (s.row i nI + 1) = i - 1 - s.row i nI by omega])
    · rw [(h1' he).1]; exact zero _ _ (by omega)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
