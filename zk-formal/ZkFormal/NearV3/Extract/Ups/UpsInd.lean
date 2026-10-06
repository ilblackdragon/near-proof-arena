import ZkFormal.NearV3.Extract.Ups.UpsParts

/-!
# ZkFormal.NearV3.Extract.Ups.UpsInd — the parts of a segment, by induction (M7e, step 1)

**`ups_partsI`**: on a segment with layout and plan, every part `k` emits `nodeEnc (upsQ … k)`, and
(unless it is the new leaf) its `MEMD` limbs `rx` are the node's exact `memory_usage`, given `UpsExt0`,
that every source is a node with usage `< 2^64`, and three segment-level facts from other tables:

* `UpsShaSeg` (SHA): a `DIGEST` lookup of part `k'`'s id at its exact length `ℓ_{k'}` returns `sha256` of
  the part's bytes, which are bytes;
* `UpsMemdSeg` (`MEMD` balance, inside the segment): every `MEMD` receive is matched by a send of the
  segment with the same `(j, i, new, old, len)`;
* `UpsLookSeg`: every part's digest is looked up at its length (the parent's child window, or `W3` for
  the root).

So `UpsExtK` is discharged for every part: `dig` from SHA and the induction hypothesis (the parts below
emit `nodeEnc`), `clen`/`memB`/`memV` from the `MEMD` match with the child part (`memdMatch`: its `qlen`,
exact `rx` and old usage `rb` on its `MEM` rows), `bytes` from SHA through the lookup.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Segment-level facts from other tables -/

/-- SHA: a lookup of part `k`'s digest at its length is `sha256` of its bytes, which are bytes. -/
def UpsShaSeg (s : UpsSeg) (ps : List (Nat × Nat)) : Prop :=
  ∀ i, i < s.rows.length → s.row i gD = 1 → ∀ k (hk : k < ps.length),
    s.row i dI = upsIdN (s.row 0 tau) (k + 1) → s.row i dL = ps[k].2 →
    (∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) ∧
      regN (s.row i) = (NearSpec.sha256 ((rowsB s ps[k].1 ps[k].2).map UInt8.ofNat)).map UInt8.toNat

/-- `MEMD`, inside the segment: every receive is matched by a send with the same `(j, i, new, old, len)`. -/
def UpsMemdSeg (s : UpsSeg) : Prop :=
  ∀ i, i < s.rows.length → s.row i gMr = 1 → ∃ i', i' < s.rows.length ∧ s.row i' gMs = 1 ∧
    s.row i' j = s.row i jm ∧ s.row i' idx = s.row i idx ∧ s.row i' rx = s.row i mBv ∧
    s.row i' rb = s.row i mCv ∧ s.row i' UpsV3.qlen = s.row i UpsV3.clen

/-- Every part's digest is looked up at its length. -/
def UpsLookSeg (s : UpsSeg) (ps : List (Nat × Nat)) : Prop :=
  ∀ k (hk : k < ps.length), ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧
    s.row i dI = upsIdN (s.row 0 tau) (k + 1) ∧ s.row i dL = ps[k].2

/-! ## Lists and nodes -/

theorem consec_find : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l → ∀ i, s0 ≤ i → i < segEnd s0 l →
    ∃ q, ∃ hq : q < l.length, l[q].1 ≤ i ∧ i < l[q].1 + l[q].2
  | [], s0, _, i, h1, h2 => by simp [segEnd] at h2; omega
  | (a, ℓ) :: rest, s0, ⟨h1, h2⟩, i, hi1, hi2 => by
    subst h1
    by_cases h : i < a + ℓ
    · exact ⟨0, by simp, by simpa using hi1, by simpa using h⟩
    · simp only [segEnd] at hi2
      obtain ⟨q, hq, e1, e2⟩ := consec_find rest (a + ℓ) h2 i (by omega) hi2
      exact ⟨q + 1, by simp; omega, by simpa using e1, by simpa using e2⟩

theorem map_ofNat_toNat (l : List UInt8) : (l.map UInt8.toNat).map UInt8.ofNat = l := by
  rw [List.map_map]
  have : (UInt8.ofNat ∘ UInt8.toNat) = fun x => x := by funext x; exact UInt8.ofNat_toNat
  rw [this, List.map_id']

/-- The last eight bytes of a node's encoding are its `memory_usage`. -/
theorem nodeEnc_mem : ∀ (t : NearSpec.PTrie), isNode t = true → ∃ pre, nodeEnc t = pre ++ NearSpec.u64 t.memD
  | .hash _, h => by simp [isNode] at h
  | .leaf _ _ _, _ => ⟨_, rfl⟩
  | .ext _ _ _, _ => ⟨_, rfl⟩
  | .branch none _ _, _ => ⟨_, rfl⟩
  | .branch (some _) _ _, _ => ⟨_, rfl⟩

theorem isNode_of_len : ∀ (t : NearSpec.PTrie), 0 < (nodeEnc t).length → isNode t = true
  | .hash _, h => by simp [nodeEnc] at h
  | .leaf _ _ _, _ => rfl
  | .ext _ _ _, _ => rfl
  | .branch _ _ _, _ => rfl

theorem limbs_congr8 {f g : Nat → Nat} (h : ∀ i, i < 8 → f i = g i) : limbs f 8 = limbs g 8 := by
  rw [limbs8, limbs8, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-! ## Row facts: the `MEMD` gates -/

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A row sending on `MEMD` is a `MEM` row. -/
theorem gMs_mem (hg : C gMs = 1) : C sMEM = 1 := by
  have f := factN ok hC hD (e := sub (c gMs) (mul3 (c sMEM) (not (c rootP)) (not (c kNLF)))) (memMem (by simp [cMem]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a gMs; have := a sMEM; have := a rootP; have := a kNLF
  have hb := stBool ok hC (x := sMEM) (by simp [states])
  nev_simp at f
  rcases hb with h | h
  · simp [h, hg] at f
  · exact h

/-- The `MEMD` send gate of a `MEM` row: not the root part, not the new leaf. -/
theorem gMs_val (hm : C sMEM = 1) (h2 : C rootP ≤ 1) (h3 : C kNLF ≤ 1) :
    C gMs = (1 - C rootP) * (1 - C kNLF) := by
  have f := factN ok hC hD (e := sub (c gMs) (mul3 (c sMEM) (not (c rootP)) (not (c kNLF)))) (memMem (by simp [cMem]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a gMs
  have hb := rowBool ok hC (x := gMs) (by simp [rowBools])
  nev_simp at f
  rcases (show C rootP = 0 ∨ C rootP = 1 by omega) with e2 | e2 <;>
  rcases (show C kNLF = 0 ∨ C kNLF = 1 by omega) with e3 | e3 <;>
  simp [hm, e2, e3] at f ⊢ <;> omega

/-- The `MEMD` receive gate of a `MEM` row: `bN`. -/
theorem gMr_val (hm : C sMEM = 1) (h2 : C bN ≤ 1) : C gMr = C bN := by
  have f := factN ok hC hD (e := sub (c gMr) (.mul (c sMEM) (c bN))) (memMem (by simp [cMem]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a gMr
  have hb := rowBool ok hC (x := gMr) (by simp [rowBools])
  nev_simp at f
  rcases (show C bN = 0 ∨ C bN = 1 by omega) with e2 | e2 <;>
  simp [hm, e2] at f ⊢ <;> omega

/-- A sending row is a node-part row. -/
theorem mem_qb (hm : C sMEM = 1) : C qb = 1 := by
  have := stSum ok hC
  have hq := rowBool ok hC (x := qb) (by simp [rowBools])
  omega

/-- The exact limb of a `MEM` row is below `2^12`. -/
theorem rx_lt (hm : C sMEM = 1) (hneg : C neg ≤ 1) (hb : C b < 256) : C rx < 4096 := by
  have hfe := rowBool ok hC (x := fe) (by simp [rowBools])
  have F := memRow ok hC hD hm hneg (le1 hfe)
  have h1 := F.rx; have h2 := F.cb; have h3 := F.cc
  have : C fe * ((1 - C neg) * cbOf C + ccOf C) ≤ 14 := by
    rcases hfe with e | e <;> rw [e]
    · omega
    · rcases (show C neg = 0 ∨ C neg = 1 by omega) with e' | e' <;> rw [e'] <;> omega
  rw [h1, Nat.mod_eq_of_lt (by omega)]; omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-! ## Parts -/

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- Every row after the value rows lies in a part. -/
theorem partRow {i : Nat} (h1 : 4 + L ≤ i) (h2 : i < s.rows.length) :
    ∃ k, ∃ hk : k < ps.length, ps[k].1 ≤ i ∧ i < ps[k].1 + ps[k].2 :=
  consec_find ps (4 + L) hL.consec i h1 (by rw [hL.cover]; exact h2)

theorem partPc (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2) {x : Nat} (hx : x ∈ partConst) :
    s.row (ps[k].1 + d) x = s.row ps[k].1 x :=
  ((hL.part k hk).2.rows d hd).2.2.2.2 x hx

/-- `qlen` is the part's length. -/
theorem qlenPart (k : Nat) (hk : k < ps.length) : s.row ps[k].1 UpsV3.qlen = ps[k].2 := by
  obtain ⟨-, U⟩ := hL.part k hk
  have hℓ := U.pos
  have hle := U.le
  have hm := lenLe hw hs
  have hr := U.rows (ps[k].2 - 1) (by omega)
  have hlt : ps[k].1 + (ps[k].2 - 1) < s.rows.length := by omega
  have F := (layoutRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)).2.2.2.2.2.2.2.2.2.2.2.1 hr.1
    (hr.2.2.2.1.2 (by omega))
  rw [hr.2.1, hr.2.2.2.2 UpsV3.qlen (by decide)] at F
  have e : ((ps[k].2 : Nat) : Fp) = ((s.row ps[k].1 UpsV3.qlen : Nat) : Fp) := by
    rw [← F, show ps[k].2 = ps[k].2 - 1 + 1 by omega, natCast_add]; rfl
  exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm

/-- The rows of part `k` with `sMEM = 1` are its last eight, with `idx` the offset in them. -/
theorem memRowOf (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2)
    (hm : s.row (ps[k].1 + d) sMEM = 1) :
    8 ≤ ps[k].2 ∧ ps[k].2 - 8 ≤ d ∧ s.row (ps[k].1 + d) idx = d - (ps[k].2 - 8) := by
  obtain ⟨-, U⟩ := hL.part k hk
  generalize ps[k].1 = o at U hm ⊢
  generalize ps[k].2 = ℓ at U hd ⊢
  generalize fls[k]'(by rw [hL.lens.1]; exact hk) = fl at U
  have hrows := U.rows
  have hq' := fun d (hd : d < ℓ) => (⟨(hrows d hd).1, (hrows d hd).2.2.1, (hrows d hd).2.2.2.1⟩ :
    s.row (o + d) qb = 1 ∧ (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ))
  have hpc := fun d (hd : d < ℓ) => (hrows d hd).2.2.2.2
  obtain ⟨q, hq, e1, e2⟩ := consec_find fl 0 U.consec d (Nat.zero_le _) (by rw [U.cover]; exact hd)
  obtain ⟨UF, hle2⟩ := U.fields q hq
  have st := UF.st (d - fl[q].1) (by omega)
  rw [show o + fl[q].1 + (d - fl[q].1) = o + d by omega] at st
  have hlt : o + d < s.rows.length := by have := U.le; omega
  have hoh := oneHot hw hs hlt (hq' d hd).1
  have hs8 : stOf (s.row (o + fl[q].1)) = 8 := by
    have := hoh.sum; have := hoh.b
    unfold stOf
    rw [← st sHPL (by simp [states]), ← st sHPF (by simp [states]), ← st sKEY (by simp [states]),
      ← st sVLEN (by simp [states]), ← st sVH (by simp [states]), ← st sBM (by simp [states]),
      ← st sCH (by simp [states]), ← st sMEM (by simp [states])]
    have h2 := hoh.sum
    omega
  have ml := (memLast hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq).1 hs8
  have hlen := fLen hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq
  rw [hs8] at hlen
  have hlast := segEnd_last fl 0 U.consec U.nonempty
  rw [U.cover] at hlast
  have h8 : fl[q].2 = 8 := by rw [hlen]; rfl
  have hq1 : q = fl.length - 1 := by omega
  subst hq1
  have hix := UF.idx (d - fl[fl.length - 1].1) (by omega)
  rw [show o + fl[fl.length - 1].1 + (d - fl[fl.length - 1].1) = o + d by omega] at hix
  refine ⟨by omega, by omega, by rw [hix]; omega⟩

/-- The `MEM` rows of part `k`: the last eight rows, `sMEM = 1`, `idx = i`. -/
theorem memRows8 (k : Nat) (hk : k < ps.length) :
    8 ≤ ps[k].2 ∧ ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) sMEM = 1 ∧
      s.row (ps[k].1 + ps[k].2 - 8 + i) idx = i := by
  obtain ⟨r0, hr0, hM, -⟩ := ups_mem hw hs hL k hk
  have hpos := (hL.part k hk).2.pos
  have h7 := (hM 7 (by omega)).1
  rw [show r0 + 7 = ps[k].1 + (ps[k].2 - 1) by omega] at h7
  have h8 := (memRowOf hw hs hL hP k hk (ps[k].2 - 1) (by omega) h7).1
  refine ⟨h8, fun i hi => ?_⟩
  rw [show ps[k].1 + ps[k].2 - 8 + i = r0 + i by omega]
  exact hM i hi

/-- Bits of a part, on any of its rows: the root flag, the new-leaf flag, `bN`, `neg`. -/
theorem partBits (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2) :
    s.row (ps[k].1 + d) rootP = (if k + 1 = ps.length then 1 else 0) ∧
    s.row (ps[k].1 + d) kNLF = (if kd k = 8 then 1 else 0) ∧
    s.row (ps[k].1 + d) bN ≤ 1 ∧ s.row (ps[k].1 + d) neg ≤ 1 := by
  obtain ⟨hlt, hq, hpf⟩ := pFirst hw hs hL k hk
  have ok0 := okRow hw hs hlt
  have b1 := partBoolN ok0 (rowLt hw hs _) hpf (x := rootP) (by decide)
  have b2 := partBoolN ok0 (rowLt hw hs _) hpf (x := bN) (by decide)
  have b3 := partBoolN ok0 (rowLt hw hs _) hpf (x := neg) (by decide)
  have hR := hP.root k hk
  have hI := partIxRow hw hs hL hP k hk d hd
  rw [partPc hw hs hL hP k hk d hd (x := rootP) (by decide), partPc hw hs hL hP k hk d hd (x := bN) (by decide),
    partPc hw hs hL hP k hk d hd (x := neg) (by decide)]
  refine ⟨?_, ?_, b2, b3⟩
  · split
    · exact hR.2 (by assumption)
    · have : s.row ps[k].1 rootP ≠ 1 := fun h => by have := hR.1 h; contradiction
      omega
  · have := hI.kd 8 (by omega)
    simp only [kcol, show (8 : Nat) < 11 from by decide, ite_true] at this
    rw [show kNLF = 50 + 8 from rfl, this]
    split <;> split <;> omega



/-- A receiving part: `bN = 1`, and `jm` is its child part's `j`. -/
theorem recvHead (k : Nat) (hk : k < ps.length) (hr : recvK ci (kd k)) :
    s.row ps[k].1 bN = 1 ∧ s.row ps[k].1 jm = childK (kd k) k + 1 := by
  obtain ⟨hlt, hq, hpf⟩ := pFirst hw hs hL k hk
  have ok0 := okRow hw hs hlt
  have hI := partIxRow hw hs hL hP k hk 0 (hL.part k hk).2.pos
  rw [Nat.add_zero] at hI
  have hj : s.row ps[k].1 j = k + 1 := (hL.part k hk).1
  have h1 := (partPlan hw hs hL hP k hk).2.1 hr
  have kv : ∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = kd k then 1 else 0 := hI.kd
  have jmR : s.row ps[k].1 kRDB + s.row ps[k].1 kRDE + s.row ps[k].1 kWEX + s.row ps[k].1 kPT = 1 →
      s.row ps[k].1 jm = k := by
    intro h; rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) hpf h (by omega), hj]; omega
  have k0 : s.row ps[k].1 kRDB = if 0 = kd k then 1 else 0 := kv 0 (by omega)
  have k1 : s.row ps[k].1 kRDE = if 1 = kd k then 1 else 0 := kv 1 (by omega)
  have k9 : s.row ps[k].1 kWEX = if 9 = kd k then 1 else 0 := kv 9 (by omega)
  have k11 : s.row ps[k].1 kPT = if 11 = kd k then 1 else 0 := kv 11 (by omega)
  have kv' : ∀ n, kd k = n → ∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = n then 1 else 0 := by
    intro n hn m hm; rw [kv m hm, hn]
  rcases hr with h | h | h | h | ⟨h, hR⟩
  · have hk' := kv' 0 h
    have H := head_RDB ok0 (rowLt hw hs _) (nextLt hw hs _) hpf hk'
    refine ⟨H.2.2.2.2.2.1, ?_⟩
    rw [jmR (by rw [k0, k1, k9, k11, h]; simp)]
    simp [childK, h]; omega
  · have hk' := kv' 1 h
    have H := head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) hpf hk'
    refine ⟨H.2.2.2.2.1, ?_⟩
    rw [jmR (by rw [k0, k1, k9, k11, h]; simp)]
    simp [childK, h]; omega
  · have hk' := kv' 9 h
    have H := head_WEX ok0 (rowLt hw hs _) (nextLt hw hs _) hpf hk'
    refine ⟨H.2.2.2.2.1, ?_⟩
    rw [jmR (by rw [k0, k1, k9, k11, h]; simp)]
    simp [childK, h]; omega
  · have hk' := kv' 11 h
    have H := head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) hpf hk'
    refine ⟨H.2.2.2.2.2.2.2.1, ?_⟩
    rw [jmR (by rw [k0, k1, k9, k11, h]; simp)]
    simp [childK, h]; omega
  · have hk' := kv' 10 h
    obtain ⟨hc4, hc10⟩ := (termCase hw hs hL hP k hk (Or.inr h)).2 h
    have H := head_SPB ok0 (rowLt hw hs _) (nextLt hw hs _) hpf hk' hI.cs hc4 hc10
    refine ⟨by rw [H.2.2.2.2.2.2.2.1, hR], ?_⟩
    rw [H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hR]
    simp [childK, h]

/-- **The `MEMD` match**: a receiving part `k` gets, on its `MEM` row `i`, the child part's exact limb `rx`,
its old-usage read `rb` and its length. -/
theorem memdMatch (HM : UpsMemdSeg s) (k : Nat) (hk : k < ps.length) (hr : recvK ci (kd k)) (i : Nat) (hi : i < 8) :
    ∃ c, c = childK (kd k) k ∧ ∃ hc : c < ps.length, c < k ∧ kd c ≠ 8 ∧
      s.row (ps[k].1 + ps[k].2 - 8 + i) mBv = s.row (ps[c].1 + ps[c].2 - 8 + i) rx ∧
      s.row (ps[k].1 + ps[k].2 - 8 + i) mCv = s.row (ps[c].1 + ps[c].2 - 8 + i) rb ∧
      s.row ps[k].1 UpsV3.clen = ps[c].2 := by
  obtain ⟨h8, hM⟩ := memRows8 hw hs hL hP k hk
  obtain ⟨hm, hix⟩ := hM i hi
  have U := (hL.part k hk).2
  have hle := U.le
  have hr0 : ps[k].1 + ps[k].2 - 8 + i = ps[k].1 + (ps[k].2 - 8 + i) := by omega
  have hlt : ps[k].1 + ps[k].2 - 8 + i < s.rows.length := by omega
  obtain ⟨hbN, hjm⟩ := recvHead hw hs hL hP k hk hr
  have hbN' : s.row (ps[k].1 + ps[k].2 - 8 + i) bN = 1 := by
    rw [hr0, partPc hw hs hL hP k hk _ (by omega) (by decide), hbN]
  have hgr := gMr_val (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hm (by omega)
  obtain ⟨i', hi', hgs, ej, eidx, erx, erb, eql⟩ := HM _ hlt (by rw [hgr, hbN'])
  have hm' := gMs_mem (okRow hw hs hi') (rowLt hw hs _) (nextLt hw hs _) hgs
  have hq' := mem_qb (okRow hw hs hi') (rowLt hw hs _) (nextLt hw hs _) hm'
  -- the sending row is in a part
  have hge : 4 + L ≤ i' := by
    apply Classical.byContradiction; intro hc
    have K := kinds (okRow hw hs hi') (rowLt hw hs _) (nextLt hw hs _)
    obtain ⟨ha, hact, -⟩ := K
    rcases Nat.lt_or_ge i' 4 with h4 | h4
    · have := hL.wk i' h4; omega
    · have := ((hL.value.2.2) (i' - 4) (by omega)).1
      rw [show 4 + (i' - 4) = i' by omega] at this; omega
  obtain ⟨c, hc, e1, e2⟩ := partRow hw hs hL hP hge hi'
  have hjc : s.row i' j = c + 1 := by
    rw [show i' = ps[c].1 + (i' - ps[c].1) by omega, partPc hw hs hL hP c hc _ (by omega) (by decide)]
    exact (hL.part c hc).1
  have hjmr : s.row (ps[k].1 + ps[k].2 - 8 + i) jm = childK (kd k) k + 1 := by
    rw [hr0, partPc hw hs hL hP k hk _ (by omega) (by decide), hjm]
  have hcK : c = childK (kd k) k := by rw [hjc, hjmr] at ej; omega
  have hd' : i' - ps[c].1 < ps[c].2 := by omega
  have hm'' : s.row (ps[c].1 + (i' - ps[c].1)) sMEM = 1 := by rw [show ps[c].1 + (i' - ps[c].1) = i' by omega]; exact hm'
  obtain ⟨h8c, hlo, hix'⟩ := memRowOf hw hs hL hP c hc _ hd' hm''
  rw [show ps[c].1 + (i' - ps[c].1) = i' by omega, eidx, hix] at hix'
  have hi'e : i' = ps[c].1 + ps[c].2 - 8 + i := by omega
  obtain ⟨bR, bK, -, bNeg⟩ := partBits hw hs hL hP c hc _ hd'
  rw [show ps[c].1 + (i' - ps[c].1) = i' by omega] at bR bK
  have hgv := gMs_val (okRow hw hs hi') (rowLt hw hs _) (nextLt hw hs _) hm' (by rw [bR]; split <;> omega)
    (by rw [bK]; split <;> omega)
  have hc8 : kd c ≠ 8 := by
    intro h8'; rw [bK, if_pos h8'] at hgv; omega
  have h1 := (partPlan hw hs hL hP k hk).2.1 hr
  have hck : c < k := by rw [hcK]; unfold childK; split <;> omega
  refine ⟨c, hcK, hc, hck, hc8, ?_, ?_, ?_⟩
  · rw [← erx, hi'e]
  · rw [← erb, hi'e]
  · rw [← partPc hw hs hL hP k hk (ps[k].2 - 8 + i) (by omega) (by decide), ← hr0, ← eql,
      show i' = ps[c].1 + (i' - ps[c].1) by omega, partPc hw hs hL hP c hc _ hd' (by decide), qlenPart hw hs hL hP c hc]

/-- The old-usage reads on a part's `MEM` rows are its source's `memory_usage`. -/
theorem memSrc {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val) (c : Nat) (hc : c < ps.length) (hc8 : kd c ≠ 8)
    (hN : isNode (src c) = true) (hM : (src c).memD < 2 ^ 64) :
    limbs (fun i => s.row (ps[c].1 + ps[c].2 - 8 + i) rb) 8 = (src c).memD := by
  obtain ⟨h8, hR8⟩ := memRows8 hw hs hL hP c hc
  have U := (hL.part c hc).2
  have hle := U.le
  have hlen := lenLe hw hs
  obtain ⟨pre, hpre⟩ := nodeEnc_mem _ hN
  have hsrc := X0.srcEnc c hc
  rw [hpre] at hsrc
  have key : ∀ i, i < 8 → s.row (ps[c].1 + ps[c].2 - 8 + i) rb =
      ((NearSpec.u64 (src c).memD).map UInt8.toNat).getD i 0 := by
    intro i hi
    obtain ⟨hm, hix⟩ := hR8 i hi
    have hr0 : ps[c].1 + ps[c].2 - 8 + i = ps[c].1 + (ps[c].2 - 8 + i) := by omega
    have hd : ps[c].2 - 8 + i < ps[c].2 := by omega
    have hlt : ps[c].1 + ps[c].2 - 8 + i < s.rows.length := by omega
    have hq := (U.rows _ hd).1
    rw [← hr0] at hq
    have hoh := oneHot hw hs hlt hq
    obtain ⟨-, bK, -, -⟩ := partBits hw hs hL hP c hc _ hd
    rw [← hr0, if_neg hc8] at bK
    have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hm bK hoh
    obtain ⟨hrb, hpl⟩ := X0.reads _ hlt hrd
    have hsN : s.row (ps[c].1 + ps[c].2 - 8 + i) sN = s.row ps[c].1 sN := by
      rw [hr0]; exact partPc hw hs hL hP c hc _ hd (by decide)
    rw [hsN, hsrc] at hrb hpl
    have f := pMEM (okRow hw hs hlt) (rowLt hw hs _) hoh.sum hrd hm
    rw [hpl, hix] at f
    simp only [List.length_map, List.length_append, u64_length] at hpl f
    have hsl := (X0.srcOk c hc).1
    rw [hpre] at hsl
    simp only [List.length_append, u64_length] at hsl
    have hsp := sub_of_cast (rowLt hw hs _ _) (by rw [P_lit]; omega) (show 8 ≤ pre.length + 8 + i by omega)
      (x := s.row (ps[c].1 + ps[c].2 - 8 + i) spos) (by rw [natCast_add]; grind)
    rw [hrb, hsp, show pre.length + 8 + i - 8 = pre.length + i by omega, List.map_append]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp
  rw [limbs_congr8 key, limbs_u64, Nat.mod_eq_of_lt hM]


/-- **The parts of a segment, by induction**: every part `k` emits `nodeEnc (upsQ … k)`, and (unless it is
the new leaf) its `MEMD` limbs are the node's exact `memory_usage`. -/
theorem ups_partsI {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val)
    (hsrcM : ∀ k, k < ps.length → isNode (src k) = true ∧ (src k).memD < 2 ^ 64)
    (HS : UpsShaSeg s ps) (HM : UpsMemdSeg s) (HL : UpsLookSeg s ps) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) val kd sdx src k).memD) := by
  have hbytes : ∀ k' (hk' : k' < ps.length), ∀ d, d < ps[k'].2 → s.row (ps[k'].1 + d) b < 256 := by
    intro k' hk'
    obtain ⟨i, hi, hg, hI, hLn⟩ := HL k' hk'
    exact (HS i hi hg k' hk' hI hLn).1
  have hlenQ : ∀ k' (hk' : k' < ps.length),
      rowsB s ps[k'].1 ps[k'].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k')).map UInt8.toNat →
      (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k')).length = ps[k'].2 := by
    intro k' hk' e
    have := congrArg List.length e
    simp only [rowsB, List.length_map, List.length_range] at this
    exact this.symm
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  refine ups_part hw hs hL hP X0 k hk ⟨?_, ?_, ?_, ?_, hbytes k hk⟩
  · -- the digests of the parts below
    intro i hi hg k' hk' hI hLn
    have hk'' : k' < ps.length := by omega
    obtain ⟨e1, -⟩ := ih k' hk' hk''
    have hl := hlenQ k' hk'' e1
    have hpos := (hL.part k' hk'').2.pos
    have := (HS i hi hg k' hk'' hI (by rw [hLn, hl])).2
    rw [this, e1, map_ofNat_toNat, ← hashOf_eq_enc _ (isNode_of_len _ (by rw [hl]; exact hpos))]
  · -- `clen`: the child's length
    intro hr
    obtain ⟨c, hcK, hc, hck, -, -, -, hcl⟩ := memdMatch hw hs hL hP HM k hk hr 0 (by omega)
    subst hcK
    rw [hcl, hlenQ _ hc (ih _ hck hc).1]
  · -- `memB`: limbs `< 2^12`
    intro hr i hi
    obtain ⟨c, hcK, hc, hck, hc8, eB, eC, -⟩ := memdMatch hw hs hL hP HM k hk hr i hi
    rw [eB, eC]
    obtain ⟨h8, hR8⟩ := memRows8 hw hs hL hP c hc
    have U := (hL.part c hc).2
    have hd : ps[c].2 - 8 + i < ps[c].2 := by omega
    have hr0 : ps[c].1 + ps[c].2 - 8 + i = ps[c].1 + (ps[c].2 - 8 + i) := by omega
    have hlt : ps[c].1 + ps[c].2 - 8 + i < s.rows.length := by have := U.le; omega
    obtain ⟨-, -, -, bNeg⟩ := partBits hw hs hL hP c hc _ hd
    rw [← hr0] at bNeg
    have hb := hbytes c hc _ hd
    rw [← hr0] at hb
    refine ⟨rx_lt (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (hR8 i hi).1 bNeg hb, ?_⟩
    -- the old usage byte is a byte of the source
    have hq := (U.rows _ hd).1
    rw [← hr0] at hq
    have hoh := oneHot hw hs hlt hq
    obtain ⟨-, bK, -, -⟩ := partBits hw hs hL hP c hc _ hd
    rw [← hr0, if_neg hc8] at bK
    have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq (hR8 i hi).1 bK hoh
    obtain ⟨hrb, -⟩ := X0.reads _ hlt hrd
    have hsN : s.row (ps[c].1 + ps[c].2 - 8 + i) sN = s.row ps[c].1 sN := by
      rw [hr0]; exact partPc hw hs hL hP c hc _ hd (by decide)
    rw [hrb, hsN, X0.srcEnc c hc]
    have := toNats_lt (nodeEnc (src c)) (s.row (ps[c].1 + ps[c].2 - 8 + i) spos)
    omega
  · -- `memV`: the child's exact usage and its source's old usage
    intro hr
    obtain ⟨c, hcK, hc, hck, hc8, -, -, -⟩ := memdMatch hw hs hL hP HM k hk hr 0 (by omega)
    have eBC : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv = s.row (ps[c].1 + ps[c].2 - 8 + i) rx ∧
        s.row (ps[k].1 + ps[k].2 - 8 + i) mCv = s.row (ps[c].1 + ps[c].2 - 8 + i) rb := by
      intro i hi
      obtain ⟨c', hcK', hc', -, -, eB, eC, -⟩ := memdMatch hw hs hL hP HM k hk hr i hi
      have : c' = c := by rw [hcK', hcK]
      subst this
      exact ⟨eB, eC⟩
    subst hcK
    refine ⟨?_, ?_⟩
    · rw [limbs_congr8 (fun i hi => (eBC i hi).1)]
      exact (ih _ hck hc).2 hc8
    · rw [limbs_congr8 (fun i hi => (eBC i hi).2)]
      exact memSrc hw hs hL hP X0 _ hc hc8 (hsrcM _ hc).1 (hsrcM _ hc).2

end

end ZkFormal.NearV3.UpsRows
