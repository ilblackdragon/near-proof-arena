import ZkFormal.NearV3.Extract.Ups.UpsCid

/-!
# ZkFormal.NearV3.Extract.Ups.UpsUpper — the upper chain (M7e, step 3, upper half)

The upper parts (`RDB`, `RDE`, `PT`, `k ≥ nT`) read, top-down from the instance's root record, the records on the
`[0,15]` path of the lockstep post trie, and each is what `PTrie.upsert` builds at its record:

* `Eoff`: the key consumed above level `ℓ` (`ℓ` below `D`, `t* − 1 − I` at `D`); **`ups_desc`**: every level `d < D`
  is left by an `enter` row `i` with `d + 1 + nI = i`, landing on `N_{d+1}`, and `Eoff (d + 1) = i`;
  `Eoff 0 = 0`;
* `lvl k` (a pass-through's `rc`, else `sdx`); **`lvl_prev`**: the level below an upper part is its `rc`;
  **`ptDeep`**: below a pass-through, the next non-pass-through part reads `N_rc`, strictly deeper;
* **`ups_ch`** (top-down from `ups_rootSrc`): every upper part's record has its child on the path at the part
  below (`sN (k − 1)`, read on its target window: `extCid` / `rdbCid` with `kidCidOk`), and the child's `res` is
  `N_{rc k}`; a pass-through's record is not its own `res` (depth), so it is `.ext [] (.node …)` (`resOk`);
* **`ups_upsert`**: `upsert (fullTree R V' rid) [0,15] (sv τ) = some (upsQ (|ps| − 1))`, bottom-up from
  `ups_term` with `upsert_pt` / `upsert_rdb` / `upsert_rde`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Record facts -/

theorem kidsBytes_len (b : Bool) : ∀ (l : List NKid), (∀ x ∈ l, x.wf) →
    (l.flatMap (NKid.bytes b)).length = 32 * (l.filter (·.present)).length
  | [], _ => by simp
  | x :: l, h => by
    have ih := kidsBytes_len b l (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    rw [List.flatMap_cons, List.length_append, ih]
    cases x with
    | none => simp [NKid.bytes, NKid.present]
    | hash hh => simp only [NKid.wf] at hx; simp [NKid.bytes, NKid.present, hx]; omega
    | node c l' r pre po => simp only [NKid.wf] at hx; cases b <;> simp [NKid.bytes, NKid.present, hx] <;> omega

theorem slotBytes_len (sl : NSlot3) (h : sl.wf) : (sl.bytes false).length = 36 := by
  cases sl with
  | ref lenB hh => simp only [NSlot3.wf] at h; simp [NSlot3.bytes, h.1, h.2]
  | val lenB i l pre po w => simp only [NSlot3.wf] at h; simp [NSlot3.bytes, h.1, h.2.1]

/-- The length of a branch record's bytes. -/
theorem serBr_len (sv : Option NSlot3) (kids : List NKid) (memB : List Nat) (h : (NodeV3.branch sv kids memB).wf) :
    ((NodeV3.branch sv kids memB).ser false).length =
      (if sv.isSome then 37 else 1) + 2 + 32 * (kids.filter (·.present)).length + 8 := by
  obtain ⟨-, hsv, hk, hm⟩ := h
  have := kidsBytes_len false kids hk
  cases sv with
  | none => simp [NodeV3.ser, this, hm]; omega
  | some sl => simp [NodeV3.ser, this, hm, slotBytes_len sl (hsv sl rfl)]; omega

theorem filter_take15 (l : List NKid) (hl : l.length = 16) (hp : (l[15]'(by omega)).present = true) :
    (l.filter (·.present)).length = ((l.take 15).filter (·.present)).length + 1 := by
  have e : l.take 16 = l.take 15 ++ [l[15]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
  rw [List.take_of_length_le (show l.length ≤ 16 by omega)] at e
  conv => lhs; rw [e]
  rw [List.filter_append, List.length_append]
  congr 1
  simp [hp]

theorem extSer1 (kk : List Nat) (kid : NKid) (memB : List Nat) :
    ((NodeV3.ext kk kid memB).ser true).getD 1 0 = (hpN kk false).length := by
  simp [NodeV3.ser, u32r]

theorem nodeTree_mem (V' : List ValRec3) (g : Nat → NearSpec.PTrie) (r : Rec3) :
    (nodeTree3 V' g r).mem? = some (nodeTree3 V' g r).memD := by
  cases r <;> simp [nodeTree3, NearSpec.PTrie.mem?, NearSpec.PTrie.memD]

theorem key_drop_len (d : Nat) : (UpsSpec.key.drop d).length = 2 - d := by simp [UpsSpec.key]

theorem c0ww (c0 ww np : Nat) (b : Bool) (hc0 : c0 = 3 ∨ c0 = 39)
    (h : c0 + 32 * ww + 8 = (if b = true then 37 else 1) + 2 + 32 * np + 8) :
    ww = np ∧ c0 = (if b = true then 37 else 1) + 2 := by
  cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;> omega

/-- The key consumed above level `ℓ`. -/
def Eoff (di si ti ℓ : Nat) : Nat := if ℓ = di then si - ti else ℓ

theorem slot_key (d : Nat) (hd : d < 2) : UpsSpec.key.drop d = slotOf d :: UpsSpec.key.drop (d + 1) := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> rfl

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-! ## The walk's descends -/

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {ws : List WalkR} {v : List UpsSeg}
  (hN : NodeWf3 vs) (hhw : HeadWf hds) (hb : Link3.ParentBal vs hds)
  (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hds (allWalks ws v)) (hw : UpsWf v)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hN hhw hb G hw hs hL hP

/-- **The descends of the walk**: level `d < D` is left on an `enter` row `i` at key position `nI = i − 1 − d`,
landing on `N_{d+1}`, which is entered after `i` nibbles; `N_0` is entered after none. -/
theorem ups_desc : Eoff di si ti 0 = 0 ∧ ∀ d, d < di → ∃ i, 1 ≤ i ∧ i ≤ si ∧ s.row i nN = s.row 0 (11 + d) ∧
    s.row i enter = 1 ∧ s.row (i + 1) nN = s.row 0 (11 + (d + 1)) ∧ d + 1 + s.row i nI = i ∧
    Eoff di si ti (d + 1) = i := by
  obtain ⟨n1, z1, r2, r3, hdi⟩ := ups_lvl hN hhw hb G hw hs hL hP
  obtain ⟨-, -, -, -, -, hnI, -⟩ := ups_walkTerm hw hs hL hP
  have i4 := hP.ix.2.2.2
  have st : ∀ i, 1 ≤ i → i ≤ si → s.row i enter ≤ 1 ∧ (s.row i enter = 0 → s.row (i + 1) nI = s.row i nI + 1) ∧
      (s.row i enter = 1 → s.row (i + 1) nI = 0) := by
    intro i h1 h2
    obtain ⟨r, -, he, -, h0, h1'⟩ := stepRow hN hhw hb G hw hs hL hP i h1 h2
    exact ⟨he, fun h => (h0 h).2.1, fun h => (h1' h).1⟩
  have st1 := st 1 (by omega)
  have st2 := st 2
  simp only [Nat.reduceAdd] at st1 st2
  rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl
  · simp only [ite_true] at hdi
    subst hdi
    simp only [Nat.zero_add] at hnI
    refine ⟨by simp [Eoff] <;> omega, fun d hd => by omega⟩
  · simp only [show (1 : Nat) ≠ 0 by omega, ite_false, ite_true] at hdi
    simp only [Nat.reduceAdd] at hnI
    obtain ⟨e1, a1, b1⟩ := st1 (by omega)
    obtain ⟨-, m2⟩ := r2 (by omega)
    rcases (show s.row 1 enter = 0 ∨ s.row 1 enter = 1 by omega) with h | h
    · rw [h] at hdi; subst hdi
      have := a1 h
      refine ⟨by simp [Eoff]; omega, fun d hd => by omega⟩
    · rw [h] at hdi m2; subst hdi
      have := b1 h
      refine ⟨by simp [Eoff], fun d hd => ?_⟩
      obtain rfl : d = 0 := by omega
      exact ⟨1, by omega, by omega, n1, h, m2, by omega, by simp [Eoff]; omega⟩
  · simp only [show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false] at hdi
    simp only [Nat.reduceAdd] at hnI
    obtain ⟨e1, a1, b1⟩ := st1 (by omega)
    obtain ⟨e2, a2, b2⟩ := st2 (by omega) (by omega)
    obtain ⟨-, m2⟩ := r2 (by omega)
    obtain ⟨-, m3⟩ := r3 (by omega)
    rcases (show s.row 1 enter = 0 ∨ s.row 1 enter = 1 by omega) with h | h <;>
    rcases (show s.row 2 enter = 0 ∨ s.row 2 enter = 1 by omega) with h' | h'
    · rw [h, h'] at hdi; subst hdi
      have := a1 h; have := a2 h'
      refine ⟨by simp [Eoff]; omega, fun d hd => by omega⟩
    · rw [h, h'] at hdi m3; rw [h] at m2; subst hdi
      have := a1 h; have := b2 h'
      refine ⟨by simp [Eoff], fun d hd => ?_⟩
      obtain rfl : d = 0 := by omega
      exact ⟨2, by omega, by omega, m2, h', m3, by omega, by simp [Eoff]; omega⟩
    · rw [h, h'] at hdi m3; rw [h] at m2; subst hdi
      have := b1 h; have := a2 h'
      refine ⟨by simp [Eoff], fun d hd => ?_⟩
      obtain rfl : d = 0 := by omega
      exact ⟨1, by omega, by omega, n1, h, m2, by omega, by simp [Eoff]; omega⟩
    · rw [h, h'] at hdi m3; rw [h] at m2; subst hdi
      have := b1 h; have := b2 h'
      refine ⟨by simp [Eoff], fun d hd => ?_⟩
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · exact ⟨1, by omega, by omega, n1, h, m2, by omega, by simp [Eoff]⟩
      · exact ⟨2, by omega, by omega, m2, h', m3, by omega, by simp [Eoff]; omega⟩

end

/-! ## Plan facts: levels and depths -/

/-- The level part `k` leads to: a pass-through's `rc`, else its source level. -/
def lvlOf (s : UpsSeg) (ps : List (Nat × Nat)) (kd sdx : Nat → Nat) (k : Nat) : Nat :=
  if kd k = 11 then s.row (ps.getD k (0, 0)).1 UpsV3.rc else sdx k

theorem getD_ps {ps : List (Nat × Nat)} {k : Nat} (hk : k < ps.length) : ps.getD k (0, 0) = ps[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl

/-- What `chStep` gives for part `k + 1`. -/
def ChOut (vs : List NodeS3) (s : UpsSeg) (ps : List (Nat × Nat)) (di si ti : Nat) (kd sdx : Nat → Nat) (k : Nat)
    (hk : k + 1 < ps.length) : Prop :=
  ∃ r, vs[s.row ps[k + 1].1 sN]? = some r ∧ ∃ c l cr pre po, c = s.row (ps[k]'(by omega)).1 sN ∧
    (∃ hc : c < vs.length, vs[c].res = s.row 0 (11 + s.row ps[k + 1].1 UpsV3.rc)) ∧
    (kd (k + 1) = 11 → ∃ m, r.v = .ext [] (.node c l cr pre po) m) ∧
    (kd (k + 1) = 0 → sdx (k + 1) < 2 ∧ Eoff di si ti (sdx (k + 1)) = sdx (k + 1) ∧
      Eoff di si ti (sdx (k + 1) + 1) = sdx (k + 1) + 1 ∧
      ∃ sv kids m, r.v = .branch sv kids m ∧ kids[slotOf (sdx (k + 1))]? = some (.node c l cr pre po)) ∧
    (kd (k + 1) = 1 → ∃ kk m, r.v = .ext kk (.node c l cr pre po) m ∧
      kk = (UpsSpec.key.drop (Eoff di si ti (sdx (k + 1)))).take kk.length ∧
      Eoff di si ti (sdx (k + 1) + 1) = Eoff di si ti (sdx (k + 1)) + kk.length)

theorem postB_eq {vs : List NodeS3} {n : Nat} (hn : n < vs.length) : postB vs n = vs[n].v.ser true := by
  simp only [postB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

theorem upbRead_at {vs : List NodeS3} {C : URow} (h : UpbRead vs C) {n : Nat} (hn : C sN = n) :
    ∃ hn' : n < vs.length, C spos < (vs[n].v.ser false).length ∧
      C rb = (vs[n].v.ser true).getD (C spos) 0 ∧ C plen = (vs[n].v.ser false).length ∧
      C pdep = vs[n].depth ∧ C rcid = vs[n].ucid.getD (C spos) 0 := by
  subst hn; exact h

section
variable {s : UpsSeg} {ps : List (Nat × Nat)} {ci ti di si : Nat} {kd sdx : Nat → Nat}
  (hP : UpsPlan s ps ci ti di si kd sdx)
include hP

theorem termK (k : Nat) (hk : k < ps.length) (hT : k < nTof ci ti) : 1 < kd k ∧ kd k < 11 :=
  let h := hP.term k hk hT; ⟨h.2.1, h.2.2.1⟩

theorem upperK (k : Nat) (hk : k < ps.length) (hT : nTof ci ti ≤ k) : kd k ≤ 1 ∨ kd k = 11 :=
  (hP.upper k hk hT).1

theorem rc_succ (k : Nat) (hk : k + 1 < ps.length) :
    s.row ps[k].1 UpsV3.rc = (if kd k ≤ 1 then 1 else 0) + s.row ps[k + 1].1 UpsV3.rc := by
  rw [hP.rcnt k (by omega), hP.rcnt (k + 1) hk, show ps.length - k = (ps.length - (k + 1)) + 1 by omega]
  simp only [rdCount]

/-- **The level below an upper part is its `rc`.** -/
theorem lvl_succ (k : Nat) (hk : k + 1 < ps.length) (hT : nTof ci ti ≤ k + 1) :
    lvlOf s ps kd sdx k = s.row ps[k + 1].1 UpsV3.rc := by
  have e := rc_succ hP k hk
  unfold lvlOf
  rw [getD_ps (show k < ps.length by omega)]
  by_cases h11 : kd k = 11
  · rw [if_pos h11, e, if_neg (by omega)]; omega
  · rw [if_neg h11]
    by_cases h1 : kd k ≤ 1
    · have := hP.desc k (by omega) h1; rw [if_pos h1] at e; omega
    · have hT' : k < nTof ci ti := by
        apply Classical.byContradiction; intro hc
        have := upperK hP k (by omega) (by omega); omega
      obtain ⟨-, -, -, -, hrc, hsd, -⟩ := hP.term k (by omega) hT'
      rw [if_neg h1] at e; omega

/-- **The root part leads to level `0`.** -/
theorem lvl_top (hne : 0 < ps.length) : lvlOf s ps kd sdx (ps.length - 1) = 0 := by
  have e := hP.rcnt (ps.length - 1) (by omega)
  rw [show ps.length - (ps.length - 1) = 1 by omega] at e
  simp only [rdCount, Nat.add_zero] at e
  unfold lvlOf
  rw [getD_ps (show ps.length - 1 < ps.length by omega)]
  by_cases h11 : kd (ps.length - 1) = 11
  · rw [if_pos h11, e, if_neg (by omega)]
  · rw [if_neg h11]
    by_cases h1 : kd (ps.length - 1) ≤ 1
    · have := hP.desc _ (by omega) h1; rw [if_pos h1] at e; omega
    · rw [if_neg h1] at e
      have hT' : ps.length - 1 < nTof ci ti := by
        apply Classical.byContradiction; intro hc
        have := upperK hP (ps.length - 1) (by omega) (by omega); omega
      obtain ⟨-, -, -, -, hrc, hsd, -⟩ := hP.term _ (by omega) hT'
      omega

theorem pdep_succ (k : Nat) (hk : k + 1 < ps.length) (hT : nTof ci ti ≤ k + 1) :
    s.row ps[k].1 pdep = s.row ps[k + 1].1 pdep + 1 := by
  have h1 := (hP.upper (k + 1) hk hT).2.2
  rcases Nat.lt_or_ge k (nTof ci ti) with h | h
  · have := (hP.term k (by omega) h).2.2.2.2.2.2; omega
  · have := (hP.upper k (by omega) h).2.2; omega

theorem kd8_top (k : Nat) (hk : k < ps.length) (hT : k + 1 = nTof ci ti) : kd k ≠ 8 := by
  obtain ⟨i1, i2, -, -⟩ := hP.ix
  intro h
  have := termLast ci i1 ti i2
  rw [← show k = nTof ci ti - 1 by omega, ← (hP.term k hk (by omega)).1, h] at this
  exact this rfl

/-- **Below a pass-through**, the next part that is not a pass-through reads `N_rc`, strictly deeper. -/
theorem ptDeep : ∀ k (hk : k < ps.length), kd k = 11 → ∃ j, ∃ hj : j < k, kd j ≠ 11 ∧ kd j ≠ 8 ∧
    sdx j = s.row ps[k].1 UpsV3.rc ∧ s.row ps[k].1 pdep < s.row (ps[j]'(by omega)).1 pdep := by
  intro k
  induction k with
  | zero =>
    intro hk h
    have := termK hP 0 hk (by have := nTof_pos _ hP.ix.1 _ hP.ix.2.1; omega); omega
  | succ k ih =>
    intro hk h
    have hT : nTof ci ti ≤ k + 1 := by
      apply Classical.byContradiction; intro hc
      have := termK hP (k + 1) hk (by omega); omega
    have hl := lvl_succ hP k hk hT
    have hd := pdep_succ hP k hk hT
    unfold lvlOf at hl
    rw [getD_ps (show k < ps.length by omega)] at hl
    by_cases h11 : kd k = 11
    · rw [if_pos h11] at hl
      obtain ⟨j, hj, a, b, c, d⟩ := ih (by omega) h11
      exact ⟨j, by omega, a, b, by rw [c, hl], by omega⟩
    · rw [if_neg h11] at hl
      refine ⟨k, by omega, h11, ?_, hl, by omega⟩
      rcases Nat.lt_or_ge k (nTof ci ti) with h' | h'
      · exact kd8_top hP k (by omega) (by omega)
      · have := upperK hP k (by omega) h'; omega

end

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

/-- A part's source record is at its `pdep`. -/
theorem part_depth (k : Nat) (hk : k < ps.length) (h8 : kd k ≠ 8) :
    ∃ hn : s.row ps[k].1 sN < vs.length, vs[s.row ps[k].1 sN].depth = s.row ps[k].1 pdep := by
  obtain ⟨hlt, hrd, hsN, hpd⟩ := memRead E.ups hs hL hP k hk h8
  obtain ⟨hn, -, -, -, h4, -⟩ := upbRead_at (upb_read E.node E.ups E.upb hs hlt hrd) hsN
  exact ⟨hn, by rw [← h4, hpd]⟩

/-- The source of a part (in `PTrie` form, its record's `Rec3`). -/
theorem src_eq (k : Nat) (hk : k < ps.length) :
    ∃ hn : s.row ps[k].1 sN < vs.length, srcOf (Rpost vs es) (Vpost vs es pv) s ps k =
      nodeTree3 (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
        (vs[s.row ps[k].1 sN].v.toRec3 (Link3.vpos (Link3.vid0 es))) := by
  have hn := part_sN E.node E.ups E.upb hs hL hP k hk
  refine ⟨hn, ?_⟩
  simp only [srcOf, getD_ps hk]
  exact post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hn

set_option maxHeartbeats 4000000 in
/-- **One upper part** (`k + 1 ≥ nT`, given, for a pass-through, that its record leads to `N_rc`): its record's
child on the path is the part below's record, whose `res` is `N_rc`; the record is `.ext [] (.node …)` (`PT`), a
branch with the child in `slotOf sd` (`RDB`), or an extension over the next key nibbles (`RDE`). -/
theorem chStep (k : Nat) (hk : k + 1 < ps.length) (hT : nTof ci ti ≤ k + 1)
    (hinv : kd (k + 1) = 11 → ∃ hn : s.row ps[k + 1].1 sN < vs.length,
      vs[s.row ps[k + 1].1 sN].res = s.row 0 (11 + s.row ps[k + 1].1 UpsV3.rc)) :
    ∃ r, vs[s.row ps[k + 1].1 sN]? = some r ∧ ∃ c l cr pre po, c = s.row (ps[k]'(by omega)).1 sN ∧
      (∃ hc : c < vs.length, vs[c].res = s.row 0 (11 + s.row ps[k + 1].1 UpsV3.rc)) ∧
      (kd (k + 1) = 11 → ∃ m, r.v = .ext [] (.node c l cr pre po) m) ∧
      (kd (k + 1) = 0 → sdx (k + 1) < 2 ∧ Eoff di si ti (sdx (k + 1)) = sdx (k + 1) ∧
        Eoff di si ti (sdx (k + 1) + 1) = sdx (k + 1) + 1 ∧
        ∃ sv kids m, r.v = .branch sv kids m ∧ kids[slotOf (sdx (k + 1))]? = some (.node c l cr pre po)) ∧
      (kd (k + 1) = 1 → ∃ kk m, r.v = .ext kk (.node c l cr pre po) m ∧
        kk = (UpsSpec.key.drop (Eoff di si ti (sdx (k + 1)))).take kk.length ∧
        Eoff di si ti (sdx (k + 1) + 1) = Eoff di si ti (sdx (k + 1)) + kk.length) := by
  have hw := E.ups
  have hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (postB vs (s.row i sN)).getD (s.row i spos) 0 :=
    fun i hi hrd => (upb_reads E.node hw E.upb hs i hi hrd).1
  have hup : s.row ps[k + 1].1 UpsV3.up = 1 := (hP.upper (k + 1) hk hT).2.1
  have hch : s.row ps[k + 1].1 cN = s.row ps[k].1 sN := hP.chain k hk
  have hn := part_sN E.node hw E.upb hs hL hP (k + 1) hk
  have hmem := List.getElem_mem hn
  have hcid := E.node.kidCid _ hmem
  have hwf := E.node.wf _ hmem
  -- the child id read on a row `i` of the part
  have cidOf : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i sN = s.row ps[k + 1].1 sN →
      s.row i rcid = s.row ps[k + 1].1 cN →
      s.row ps[k].1 sN = vs[s.row ps[k + 1].1 sN].ucid.getD (s.row i spos) 0 := by
    intro i hi hrd hsNi hrc
    obtain ⟨_hn6, -, -, -, -, h6⟩ := upbRead_at (upb_read E.node hw E.upb hs hi hrd) hsNi
    rw [← hch, ← hrc, h6]
  rcases upperK hP (k + 1) hk hT with h1 | h11
  · -- a descend
    have hdlt := descLt hw hs hL hP (k + 1) hk h1
    have hrc := hP.desc (k + 1) hk h1
    have hsrc := (hP.src (k + 1) hk (by omega)).1
    obtain ⟨-, D⟩ := ups_desc E.node E.head E.par E.walk hw hs hL hP
    obtain ⟨i, i1, i2, hNi, hent, hN1, hnI, hE1⟩ := D _ hdlt
    obtain ⟨r, hr, -, -, -, h1'⟩ := stepRow E.node E.head E.par E.walk hw hs hL hP i i1 i2
    obtain ⟨-, c, l, cr, pre, po, hcr, ⟨hc, hres, -⟩, hBX⟩ := h1' hent
    have hNs : s.row i nN = s.row ps[k + 1].1 sN := by rw [hNi, hsrc]
    rw [hNs, List.getElem?_eq_getElem hn, Option.some.injEq] at hr
    subst hr
    have hcres : vs[c].res = s.row 0 (11 + s.row ps[k + 1].1 UpsV3.rc) := by rw [hres, hcr, hN1, hrc]
    have hEd : Eoff di si ti (sdx (k + 1)) = sdx (k + 1) := by simp only [Eoff]; rw [if_neg (by omega)]
    have hdi2 := hP.ix.2.2.1
    -- the record's constructor from the kind (`SrcShape`)
    obtain ⟨hn', hsrcE⟩ := src_eq E hs hL hP (k + 1) hk
    have hshape := ups_shape E hs hL hP (k + 1) hk
    obtain ⟨tL, tE, tB⟩ := tn_cases (Vpost vs es pv) (fullTree (Rpost vs es) (Vpost vs es pv))
      (Link3.vpos (Link3.vid0 es)) vs[s.row ps[k + 1].1 sN].v
    rw [← hsrcE] at tL tE tB
    rcases (show kd (k + 1) = 0 ∨ kd (k + 1) = 1 by omega) with h0 | h1e
    · -- `RDB`
      obtain ⟨bv, cs, m, -, hb, -⟩ := hshape.1 h0
      obtain ⟨sv', kids', mB', hvB⟩ := tB bv cs m hb
      obtain ⟨sv, kids, m, hv, hI0, hkid⟩ := hBX.resolve_right (fun ⟨kk, m, hv, _, _⟩ => by rw [hvB] at hv; cases hv)
      have hi1 : i = sdx (k + 1) + 1 := by omega
      have hsl : wsym i = slotOf (sdx (k + 1)) := by
        rw [hi1]; rcases (show sdx (k + 1) = 0 ∨ sdx (k + 1) = 1 by omega) with h | h <;> rw [h] <;> rfl
      rw [hsl] at hkid
      have hwfB := hwf
      rw [hv] at hwfB
      have h16 := hwfB.1
      obtain ⟨c0, ww, hc0, ⟨i', hi', hrd', hsN', hpl'⟩, hW⟩ := rdbCid hw hs hL hP (k + 1) hk h0 hup
      obtain ⟨_hn4, -, -, h4', -, -⟩ := upbRead_at (upb_read E.node hw E.upb hs hi' hrd') hsN'
      rw [hpl', hv, serBr_len sv kids m hwfB] at h4'
      have hP1 : 0 < (kids.filter (·.present)).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_of_getElem? hkid, rfl⟩)
      have hww := c0ww c0 ww _ sv.isSome hc0 h4'
      obtain ⟨i'', hi'', hrd'', hsN'', hsp'', hrc''⟩ := hW (by omega)
      have hcN := cidOf i'' hi'' hrd'' hsN'' hrc''
      rw [hv] at hcid
      simp only [NodeV3.kidCidOk] at hcid
      have hcc := hcid (slotOf (sdx (k + 1))) c l cr pre po (by rw [List.getD_eq_getElem?_getD, hkid]; rfl)
      have hpos : s.row i'' spos = (if sv.isSome then 37 else 1) + 2 +
          32 * ((kids.take (slotOf (sdx (k + 1)))).filter (·.present)).length := by
        rw [hsp'']
        rcases (show sdx (k + 1) = 0 ∨ sdx (k + 1) = 1 by omega) with h | h
        · rw [h, show slotOf 0 = 0 from rfl]; simp; omega
        · rw [h] at hkid ⊢
          rw [show slotOf 1 = 15 from rfl] at hkid ⊢
          obtain ⟨hlt15, he15⟩ := List.getElem?_eq_some_iff.1 hkid
          have h15 : (kids[15]'hlt15).present = true := by rw [he15]; rfl
          have := filter_take15 kids h16 h15
          simp only [ite_true]; omega
      rw [hpos, hcc] at hcN
      exact ⟨_, List.getElem?_eq_getElem hn, c, l, cr, pre, po, hcN.symm, ⟨hc, hcres⟩, fun h => by omega,
        fun _ => ⟨by omega, hEd, by rw [hE1, hi1], sv, kids, m, hv, hkid⟩, fun h => by omega⟩
    · -- `RDE`
      obtain ⟨kk0, cc, m0, he⟩ := hshape.2.1 h1e
      obtain ⟨kid', mB', hvE⟩ := tE kk0 cc m0 he
      rcases hBX with ⟨sv, kids, m, hv, -, -⟩ | ⟨kk, m, hv, hlast, hx⟩
      · rw [hvE] at hv; cases hv
      have RK := rowKey E.node E.head E.par E.walk hw hs hL hP i i1 (by omega)
      obtain ⟨-, RK⟩ := RK
      rw [hNs] at RK
      obtain ⟨-, kE, -⟩ := RK _ (List.getElem?_eq_getElem hn)
      obtain ⟨-, htk⟩ := kE kk _ m hv
      have hsi := hP.ix.2.2.2
      have hd : sdx (k + 1) = i - 1 - s.row i nI := by omega
      have hXl : s.row i nI < (UpsSpec.key.drop (i - 1 - s.row i nI)).length := by
        rw [key_drop_len]; omega
      have hkk : kk = (UpsSpec.key.drop (sdx (k + 1))).take kk.length := by
        rw [hd, ← hlast]
        conv => lhs; rw [← List.take_of_length_le (show kk.length ≤ s.row i nI + 1 by omega)]
        refine take_succ_of htk (by omega) hXl ?_
        rw [hx, List.getD_eq_getElem?_getD, List.getElem?_drop, show i - 1 - s.row i nI + s.row i nI = i - 1 by omega,
          ← List.getD_eq_getElem?_getD, wsym_key i i1 (by omega)]
      obtain ⟨i', hi', hrd', hsN', hsp', hrc'⟩ := extCid hw hs hL hP (k + 1) hk (Or.inl h1e) hup (postB vs) hR
      have hcN := cidOf i' hi' hrd' hsN' hrc'
      rw [hsp', postB_eq hn, hv, extSer1] at hcN
      rw [hv] at hcid
      simp only [NodeV3.kidCidOk] at hcid
      rw [hcid c l cr pre po rfl] at hcN
      exact ⟨_, List.getElem?_eq_getElem hn, c, l, cr, pre, po, hcN.symm, ⟨hc, hcres⟩, fun h => by omega, fun h => by omega,
        fun _ => ⟨kk, m, hv, by rw [hEd]; exact hkk, by rw [hEd, hE1]; omega⟩⟩
  · -- a pass-through
    obtain ⟨_hn1, hres⟩ := hinv h11
    obtain ⟨_hn2, hdep⟩ := part_depth E hs hL hP (k + 1) hk (by omega)
    obtain ⟨j, hj, j11, j8, hjs, hjd⟩ := ptDeep hP (k + 1) hk h11
    obtain ⟨hnj, hdj⟩ := part_depth E hs hL hP j (by omega) j8
    have hsrcj := (hP.src j (by omega) j11).1
    simp only [hsrcj, hjs] at hdj hnj
    rcases Walk3.resOk_cases (E.node.res _ hn) with he | ⟨c, l, cr, pre, po, m, hv, hcr⟩
    · exfalso
      rw [hres] at he
      simp only [he] at hdj
      omega
    have hrev : (c, l, cr, pre, po) ∈ vs[s.row ps[k + 1].1 sN].v.revealed := by rw [hv]; simp [NodeV3.revealed]
    obtain ⟨hc, -, -, hcres⟩ := Link3.kid_depth E.node E.head E.par hn hrev
    obtain ⟨i', hi', hrd', hsN', hsp', hrc'⟩ := extCid hw hs hL hP (k + 1) hk (Or.inr h11) hup (postB vs) hR
    have hcN := cidOf i' hi' hrd' hsN' hrc'
    rw [hsp', postB_eq hn, hv, extSer1] at hcN
    rw [hv] at hcid
    simp only [NodeV3.kidCidOk] at hcid
    rw [hcid c l cr pre po rfl] at hcN
    exact ⟨_, List.getElem?_eq_getElem hn, c, l, cr, pre, po, hcN.symm, ⟨hc, by rw [hcres, ← hcr, hres]⟩,
      fun _ => ⟨m, hv⟩, fun h => by omega, fun h => by omega⟩

/-- **The top of the chain**: a pass-through root part reads the head's root record `rid`, whose `res` is the
walk's first record `N_0` (the head's `START` edge lands on `rres`). -/
theorem top_inv {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) (hne : 0 < ps.length)
    (h11 : kd (ps.length - 1) = 11) :
    ∃ hn : s.row (ps[ps.length - 1]'(by omega)).1 sN < vs.length,
      vs[s.row (ps[ps.length - 1]'(by omega)).1 sN].res =
        s.row 0 (11 + s.row (ps[ps.length - 1]'(by omega)).1 UpsV3.rc) := by
  have hw := E.ups
  have hk : ps.length - 1 < ps.length := by omega
  have hroot := ups_rootSrc hC hw hs hL hP (ps.length - 1) hk (by omega)
  have hrc : s.row ps[ps.length - 1].1 UpsV3.rc = 0 := by
    rw [hP.rcnt _ hk, show ps.length - (ps.length - 1) = 1 by omega]
    simp only [rdCount, Nat.add_zero]; rw [if_neg (by omega)]
  obtain ⟨h, hh, ht, he⟩ := Walk3.start_head E.walk (upsWalk_mem (ws := ws) hs)
  have F0 := (wRowF hw hs hL 0 (by omega)).start rfl
  rw [upsWalk_step s (by omega)] at he
  simp only [stepOf, List.cons.injEq] at he
  have hN0 : s.row 0 (11 + 0) = h.rres := by rw [← he.2.2.2.1, F0.2.2.2.2.2]; rfl
  have hhd : h = headAt hds (s.row 0 tau) := by
    have := (hC.head_all h hh).2; rw [ht] at this; exact this
  obtain ⟨hr, -, -, -, hres⟩ := Link3.head_link E.node E.head E.par hh
  rw [hroot, hrc, hN0, ← hhd]
  exact ⟨hr, hres⟩

/-- **The upper chain, top-down**: `chStep` holds for every upper part. -/
theorem ups_ch {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) :
    ∀ k (hk : k + 1 < ps.length), nTof ci ti ≤ k + 1 → ChOut vs s ps di si ti kd sdx k hk := by
  suffices H : ∀ j k (hk : k + 1 < ps.length), k + 2 + j = ps.length → nTof ci ti ≤ k + 1 →
      ChOut vs s ps di si ti kd sdx k hk by
    intro k hk hT; exact H (ps.length - k - 2) k hk (by omega) hT
  intro j
  induction j with
  | zero =>
    intro k hk hj hT
    refine chStep E hs hL hP k hk hT (fun h11 => ?_)
    have := top_inv E hs hL hP hC (by omega) (by rw [show ps.length - 1 = k + 1 by omega]; exact h11)
    simp only [show ps.length - 1 = k + 1 by omega] at this
    exact this
  | succ j ih =>
    intro k hk hj hT
    refine chStep E hs hL hP k hk hT (fun h11 => ?_)
    obtain ⟨r, -, c, l, cr, pre, po, hcs, ⟨hc, hres⟩, -⟩ := ih (k + 1) (by omega) (by omega) (by omega)
    have hl := lvl_succ hP (k + 1) (by omega) (by omega)
    unfold lvlOf at hl
    rw [if_pos h11, getD_ps hk] at hl
    subst hcs
    exact ⟨hc, by rw [hres, hl]⟩

/-- **The upper chain, bottom-up**: every part from the top terminal part up is the upsert at its record with
the key left at its level. -/
theorem ups_up {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) :
    ∀ k, nTof ci ti ≤ k + 1 → k < ps.length →
      (srcOf (Rpost vs es) (Vpost vs es pv) s ps k).upsert
          (UpsSpec.key.drop (Eoff di si ti (lvlOf s ps kd sdx k))) (sv (s.row 0 tau)) =
        some (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k) := by
  have hw := E.ups
  have i12 := hP.ix
  have hnT := nTof_pos ci i12.1 ti i12.2.1
  intro k
  induction k with
  | zero =>
    intro hT hk
    obtain ⟨-, hU⟩ := ups_term E hs hL hP
    have hk0 : nTof ci ti - 1 = 0 := by omega
    rw [hk0] at hU
    have h0 := termK hP 0 hk (by omega)
    obtain ⟨-, -, -, -, -, hsd, -⟩ := hP.term 0 hk (by omega)
    have hsrc := (hP.src 0 hk (by omega)).1
    have hl : lvlOf s ps kd sdx 0 = di := by unfold lvlOf; rw [if_neg (by omega), hsd]
    rw [hl]
    simp only [srcOf, getD_ps hk, hsrc, hsd, Eoff, if_pos rfl]
    exact hU
  | succ k ih =>
    intro hT hk
    by_cases hTk : k + 2 ≤ nTof ci ti
    · -- the top terminal part
      have hk' : k + 1 = nTof ci ti - 1 := by omega
      obtain ⟨-, hU⟩ := ups_term E hs hL hP
      rw [← hk'] at hU
      have h0 := termK hP (k + 1) hk (by omega)
      obtain ⟨-, -, -, -, -, hsd, -⟩ := hP.term (k + 1) hk (by omega)
      have hsrc := (hP.src (k + 1) hk (by omega)).1
      have hl : lvlOf s ps kd sdx (k + 1) = di := by unfold lvlOf; rw [if_neg (by omega), hsd]
      rw [hl]
      simp only [srcOf, getD_ps hk, hsrc, hsd, Eoff, if_pos rfl]
      exact hU
    have hT1 : nTof ci ti ≤ k + 1 := by omega
    have IH := ih (by omega) (by omega)
    have hl := lvl_succ hP k hk hT1
    rw [hl] at IH
    obtain ⟨r, hr, c, l, cr, pre, po, hcs, ⟨hc, -⟩, hPT, hDB, hDE⟩ := ups_ch E hs hL hP hC k hk hT1
    obtain ⟨hn, hsrcE⟩ := src_eq E hs hL hP (k + 1) hk
    rw [List.getElem?_eq_getElem hn, Option.some.injEq] at hr
    subst hr
    have hsk : srcOf (Rpost vs es) (Vpost vs es pv) s ps k = fullTree (Rpost vs es) (Vpost vs es pv) c := by
      simp only [srcOf, getD_ps (show k < ps.length by omega), hcs]
    rw [hsk] at IH
    have hcm : (fullTree (Rpost vs es) (Vpost vs es pv) c).mem? =
        some (fullTree (Rpost vs es) (Vpost vs es pv) c).memD := by
      rw [post_eq E.node E.head E.val E.par E.vpar E.sha (Vpost vs es pv) hc]; exact nodeTree_mem _ _ _
    rw [upsQ_succ, hsk, hsrcE]
    rcases upperK hP (k + 1) hk hT1 with h1 | h11
    · rcases (show kd (k + 1) = 0 ∨ kd (k + 1) = 1 by omega) with h0 | h1e
      · obtain ⟨hd2, hEd, hEd1, sv', kids, m, hv, hkid⟩ := hDB h0
        have hrc := hP.desc (k + 1) hk (by omega)
        have hlk : lvlOf s ps kd sdx (k + 1) = sdx (k + 1) := by unfold lvlOf; rw [if_neg (by omega)]
        rw [hrc, hEd1] at IH
        rw [hlk, hEd, slot_key _ hd2, hv, h0]
        simp only [NodeV3.toRec3, nodeTree3, qPart]
        exact upsert_rdb _ _ _ _ _ _ _ _ (kidAt_node _ kids _ hkid) hcm IH
      · obtain ⟨kk, m, hv, hkk, hE1⟩ := hDE h1e
        have hrc := hP.desc (k + 1) hk (by omega)
        have hlk : lvlOf s ps kd sdx (k + 1) = sdx (k + 1) := by unfold lvlOf; rw [if_neg (by omega)]
        rw [hrc, hE1] at IH
        rw [hlk, hv, h1e]
        simp only [NodeV3.toRec3, nodeTree3, kidTree3, NKid.toKid3, qPart]
        refine upsert_rde _ _ _ _ _ _ hkk.symm hcm ?_
        rw [List.drop_drop]; exact IH
    · obtain ⟨m, hv⟩ := hPT h11
      have hlk : lvlOf s ps kd sdx (k + 1) = s.row ps[k + 1].1 UpsV3.rc := by
        unfold lvlOf; rw [if_pos h11, getD_ps hk]
      rw [hlk, hv, h11]
      simp only [NodeV3.toRec3, nodeTree3, kidTree3, NKid.toKid3, qPart]
      exact upsert_pt _ _ _ _ _ hcm IH

/-- **Step 3, upper half: the segment's root part is the upsert of `[0,15]` at the instance's root record**
(in the lockstep post trie `fullTree R V'`). -/
theorem ups_upsert {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK) :
    (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid).upsert UpsSpec.key (sv (s.row 0 tau)) =
      some (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps)
        (ps.length - 1)) := by
  have hne := hL.nonempty
  have hT : nTof ci ti ≤ ps.length - 1 + 1 := by have := hP.len; omega
  have H := ups_up E hs hL hP hC (ps.length - 1) hT (by omega)
  rw [lvl_top hP hne] at H
  obtain ⟨hE0, -⟩ := ups_desc E.node E.head E.par E.walk E.ups hs hL hP
  rw [hE0, List.drop_zero] at H
  have hroot := ups_rootSrc hC E.ups hs hL hP (ps.length - 1) (by omega) (by omega)
  simp only [srcOf, getD_ps (show ps.length - 1 < ps.length by omega), hroot] at H
  exact H

end

end ZkFormal.NearV3.UpsRows
