import ZkFormal.NearV3.Extract.Ups.UpsLook
import ZkFormal.Near.Link.Bus
import ZkFormal.Near.Link.ShaCore

/-!
# ZkFormal.NearV3.Extract.Ups.UpsBus — segment facts from the bus balances (M7e, step 1)

* **`sha_seg`**: SHA (`ShaFacts`), the `BYTES` balance (the `upsV3` sends and other tables' sends, none of
  kind 12), "every `upsV3` `DIGEST` receive is provided", distinct instances and ids that do not wrap
  (`UpsIdBound`: `τ < 2^17`, fewer than 512 parts) give `UpsShaSeg` for every segment (`sha_core` with the
  part's bytes as the message);
* **`memd_seg`**: the `MEMD` balance (`upsV3` is the only participant: its sends are a permutation of its
  receives, as `Fp` images) and distinct `τ` per segment give `UpsMemdSeg s` for every segment: a receive of
  segment `s` is matched by a send with the same `τ`, hence of `s`.

`UpsTauDistinct v` (distinct segment instances) comes with the instance chain (`root_chain`, step 4).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The segments' instances are distinct. -/
def UpsTauDistinct (v : List UpsSeg) : Prop :=
  ∀ s ∈ v, ∀ s' ∈ v, s.row 0 tau = s'.row 0 tau → s = s'

theorem mem_upsSends {v : List UpsSeg} {b : Nat} {m : Msg} :
    m ∈ (upsTraffic v).sends b ↔ ∃ s ∈ v, ∃ i, i < s.rows.length ∧ m ∈ uMsgs (s.row i) (s.next i) b true := by
  simp [upsTraffic, UpsSeg.msgs, List.mem_flatMap]

theorem mem_upsRecvs {v : List UpsSeg} {b : Nat} {m : Msg} :
    m ∈ (upsTraffic v).recvs b ↔ ∃ s ∈ v, ∃ i, i < s.rows.length ∧ m ∈ uMsgs (s.row i) (s.next i) b false := by
  simp [upsTraffic, UpsSeg.msgs, List.mem_flatMap]

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A row receiving on `MEMD` is a `MEM` row. -/
theorem gMr_mem (hg : C gMr = 1) : C sMEM = 1 := by
  have f := factN ok hC hD (e := sub (c gMr) (.mul (c sMEM) (c bN))) (memMem (by simp [cMem]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a gMr
  have hb := stBool ok hC (x := sMEM) (by simp [states])
  nev_simp at f
  rcases hb with h | h
  · simp [h, hg] at f
  · exact h

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw hs hL

/-- A row with `qb = 1` lies after the value rows. -/
theorem qbAfter {i : Nat} (hi : i < s.rows.length) (hq : s.row i qb = 1) : 4 + L ≤ i := by
  apply Classical.byContradiction; intro hc
  obtain ⟨ha, hact, -⟩ := kinds (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · have := hL.wk i h4; omega
  · have := ((hL.value.2.2) (i - 4) (by omega)).1
    rw [show 4 + (i - 4) = i by omega] at this; omega

/-- The `MEMD` messages of a row (either side). -/
theorem memdMsgs {i : Nat} (hi : i < s.rows.length) :
    uMsgs (s.row i) (s.next i) B_MEMD true =
      (if 4 + L ≤ i ∧ s.row i gMs = 1 then
        [[s.row i tau, s.row i j, s.row i idx, s.row i rx, s.row i rb, s.row i UpsV3.qlen]] else []) ∧
    uMsgs (s.row i) (s.next i) B_MEMD false =
      (if 4 + L ≤ i ∧ s.row i gMr = 1 then
        [[s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen]] else []) := by
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · have e1 := hL.msgsW i h4 B_MEMD true
    have e2 := hL.msgsW i h4 B_MEMD false
    simp only [show ¬ (4 + L ≤ i) by omega, false_and, ite_false]
    refine ⟨by rw [e1]; simp [B_MEMD, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP],
      by rw [e2]; simp [B_MEMD, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]⟩
  rcases Nat.lt_or_ge i (4 + L) with hL4 | hL4
  · have e1 := hL.msgsV (i - 4) (by omega) B_MEMD true
    have e2 := hL.msgsV (i - 4) (by omega) B_MEMD false
    rw [show 4 + (i - 4) = i by omega] at e1 e2
    simp only [show ¬ (4 + L ≤ i) by omega, false_and, ite_false]
    refine ⟨by rw [e1]; simp [B_MEMD, B_SPOST, B_BYTES], by rw [e2]; simp [B_MEMD, B_SPOST, B_BYTES]⟩
  · have e1 := hL.msgsQ i hL4 hi B_MEMD true
    have e2 := hL.msgsQ i hL4 hi B_MEMD false
    simp only [hL4, true_and]
    refine ⟨by rw [e1]; simp [B_MEMD, B_DIGEST, B_BYTES, B_UPB], by rw [e2]; simp [B_MEMD, B_DIGEST, B_BYTES, B_UPB]⟩

end

/-- **`MEMD` inside each segment**, from the `MEMD` balance and distinct instances. -/
theorem memd_seg {v : List UpsSeg} (hw : UpsWf v)
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) : ∀ s ∈ v, UpsMemdSeg s := by
  intro s hs i hi hg
  obtain ⟨L, ps, fls, ws, hL⟩ := ups_layout hw s hs
  have hq := mem_qb (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
    (gMr_mem (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _) hg)
  have h4 := qbAfter hw hs hL hi hq
  have hmem : [s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen] ∈
      (upsTraffic v).recvs B_MEMD :=
    mem_upsRecvs.2 ⟨s, hs, i, hi, by rw [(memdMsgs hw hs hL hi).2, if_pos ⟨h4, hg⟩]; simp⟩
  obtain ⟨m', hm', he⟩ := List.mem_map.1 (hM.symm.subset (List.mem_map.2 ⟨_, hmem, rfl⟩))
  obtain ⟨s', hs', i', hi', hm''⟩ := mem_upsSends.1 hm'
  obtain ⟨L', ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
  rw [(memdMsgs hw hs' hL' hi').1] at hm''
  split at hm''
  · rename_i hc
    simp only [List.mem_singleton] at hm''
    subst hm''
    have cv := fun (t : UpsSeg) (ht : t ∈ v) (r x : Nat) => rowLt hw ht r x
    have e := Link.toFp_inj (a := [s'.row i' tau, s'.row i' j, s'.row i' idx, s'.row i' rx, s'.row i' rb,
        s'.row i' UpsV3.qlen]) (b := [s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h <;> rw [h] <;> exact cv _ hs' _ _)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h <;> rw [h] <;> exact cv _ hs _ _) he
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨et, ej, ei, ex, eb, eq⟩ := e
    have hss : s' = s := by
      apply htau s' hs' s hs
      rw [← hL'.segc i' hi' tau (by decide), ← hL.segc i hi tau (by decide), et]
    subst hss
    exact ⟨i', hi', hc.2, ej, ei, ex, eb, eq⟩
  · simp at hm''


/-! ## SHA -/

/-- The `upsV3` ids do not wrap: `τ < 2^17` and fewer than 512 parts per segment. -/
def UpsIdBound (v : List UpsSeg) : Prop :=
  ∀ s ∈ v, s.row 0 tau < 2 ^ 17 ∧ ∀ L ps fls ws, UpsLayout s L ps fls ws → ps.length < 512

theorem upsIdN_val {τ jj : Nat} (h1 : τ < 2 ^ 17) (h2 : jj ≤ 512) : upsIdN τ jj = 12 + 16 * (512 * τ + jj) := by
  unfold upsIdN K_VUPS; rw [Nat.mod_eq_of_lt (by rw [P_lit]; omega)]

theorem upsIdN_inj {τ jj τ' jj' : Nat} (h1 : τ < 2 ^ 17) (h2 : jj < 512) (h3 : τ' < 2 ^ 17) (h4 : jj' < 512)
    (h : upsIdN τ jj = upsIdN τ' jj') : τ = τ' ∧ jj = jj' := by
  rw [upsIdN_val h1 (by omega), upsIdN_val h3 (by omega)] at h; omega

theorem upsIdN_lt (τ jj : Nat) : upsIdN τ jj < P := by unfold upsIdN; exact Nat.mod_lt _ (by rw [P_lit]; omega)

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- Off node parts the digest gate is `wt3`. -/
theorem gD_noq (hq : C qb = 0) : C gD = C wt3 := by
  have f := factN ok hC hD (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3))) (memDigest (by simp [cDigest]))
  simp only [winFr] at f
  nev_simp at f
  have := hC gD; have := hC wt3
  rw [P_lit] at *
  have b1 := rowBool ok hC (x := gD) (by simp [rowBools])
  have b2 := rowBool ok hC (x := wt3) (by simp [rowBools])
  simp [hq] at f
  rcases b1 with h | h <;> rcases b2 with h' | h' <;> simp [h, h'] at f ⊢

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw hs hL

/-- A row with `gD = 1` receives `DIGEST (dI, dL, reg)`. -/
theorem digIn {i : Nat} (hi : i < s.rows.length) (hg : s.row i gD = 1) :
    [s.row i dI, s.row i dL] ++ regN (s.row i) ∈ uMsgs (s.row i) (s.next i) B_DIGEST false := by
  have ok := okRow hw hs hi
  rcases Nat.lt_or_ge i (4 + L) with h | h
  · have hq : s.row i qb = 0 := by
      have := rowBool ok (rowLt hw hs _) (x := qb) (by simp [rowBools])
      rcases this with h' | h'
      · exact h'
      · have := qbAfter hw hs hL hi h'; omega
    have hw3 := gD_noq ok (rowLt hw hs _) (nextLt hw hs _) hq
    rw [hg] at hw3
    rcases Nat.lt_or_ge i 4 with h4 | h4
    · rw [hL.msgsW i h4 B_DIGEST false]
      simp [B_DIGEST, B_MIDROOT, B_ROOT, ← hw3, regN]
    · exfalso
      obtain ⟨-, -, hwk, -, -, -, bw3, -⟩ := kinds ok (rowLt hw hs _) (nextLt hw hs _)
      have hv := ((hL.value.2.2) (i - 4) (by omega)).1
      rw [show 4 + (i - 4) = i by omega] at hv
      obtain ⟨ha, hact, -⟩ := kinds ok (rowLt hw hs _) (nextLt hw hs _)
      omega
  · rw [hL.msgsQ i h hi B_DIGEST false]
    simp [B_DIGEST, hg, regN]

end

/-- **SHA, per segment**: a lookup of a part's digest at its length is `sha256` of its bytes, which are
bytes. -/
theorem sha_seg {v : List UpsSeg} (hw : UpsWf v) {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (others : List Msg) (hbytes : ∀ m, shaR B_BYTES m = cnt ((upsTraffic v).sends B_BYTES ++ others) m)
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdig : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (htau : UpsTauDistinct v) (hB : UpsIdBound v) :
    ∀ s ∈ v, ∀ L ps fls ws, UpsLayout s L ps fls ws → UpsShaSeg s ps := by
  intro s hs L ps fls ws hL i hi hg k hk hI hLn
  obtain ⟨hτ, hps⟩ := hB s hs
  have hps' := hps L ps fls ws hL
  have hlen := lenLe hw hs
  have U := (hL.part k hk).2
  have hle := U.le
  have hencL : (rowsB s ps[k].1 ps[k].2).length = ps[k].2 := by simp [rowsB]
  -- the lookup is provided
  have hrecv : 0 < shaS B_DIGEST (digMsg (upsIdN (s.row 0 tau) (k + 1)) (rowsB s ps[k].1 ps[k].2).length
      (regN (s.row i))).toFp := by
    have := hdig _ (mem_upsRecvs.2 ⟨s, hs, i, hi, digIn hw hs hL hi hg⟩)
    rwa [hI, hLn, ← hencL] at this
  -- the sends with this id are the part's bytes
  have hS : ∀ m ∈ (upsTraffic v).sends B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (upsIdN (s.row 0 tau) (k + 1)) →
      ∃ d, d < (rowsB s ps[k].1 ps[k].2).length ∧ m = [upsIdN (s.row 0 tau) (k + 1), d, (rowsB s ps[k].1 ps[k].2).getD d 0] := by
    intro m hm a ha he
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨s', hs', i', hi', hm'⟩ := mem_upsSends.1 hm
      obtain ⟨L', ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
      obtain ⟨ci', ti', di', si', kd', sdx', hP'⟩ := ups_plan hw hs' hL'
      obtain ⟨hτ', hps2⟩ := hB s' hs'
      have hps2' := hps2 L' ps' fls' ws' hL'
      rcases Nat.lt_or_ge i' 4 with h4 | h4
      · rw [hL'.msgsW i' h4 B_BYTES true] at hm'
        simp [B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP] at hm'
      rcases Nat.lt_or_ge i' (4 + L') with hv | hv
      · rw [show i' = 4 + (i' - 4) by omega, hL'.msgsV (i' - 4) (by omega) B_BYTES true] at hm'
        simp [B_BYTES, B_SPOST] at hm'
        subst hm'
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        have e := Link.ofNat_inj (upsIdN_lt _ _) (upsIdN_lt _ _) he
        rw [hL'.segc _ (by omega) tau (by decide)] at e
        have := upsIdN_inj hτ' (by omega) hτ (by omega) e
        omega
      · rw [hL'.msgsQ i' hv hi' B_BYTES true] at hm'
        simp [B_BYTES, B_DIGEST, B_UPB, B_MEMD] at hm'
        subst hm'
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        obtain ⟨k', hk', e1, e2⟩ := partRow hw hs' hL' hP' hv hi'
        have hj : s'.row i' j = k' + 1 := by
          rw [show i' = ps'[k'].1 + (i' - ps'[k'].1) by omega, partPc hw hs' hL' hP' k' hk' _ (by omega) (by decide)]
          exact (hL'.part k' hk').1
        have e := Link.ofNat_inj (upsIdN_lt _ _) (upsIdN_lt _ _) he
        rw [hL'.segc _ hi' tau (by decide), hj] at e
        obtain ⟨et, ek⟩ := upsIdN_inj hτ' (by omega) hτ (by omega) e
        have hss : s' = s := htau s' hs' s hs et
        subst hss
        -- the row in the given layout
        have hqi : s'.row i' qb = 1 := by
          have := ((hL'.part k' hk').2.rows (i' - ps'[k'].1) (by omega)).1
          rwa [show ps'[k'].1 + (i' - ps'[k'].1) = i' by omega] at this
        obtain ⟨ci0, ti0, di0, si0, kd0, sdx0, hP0⟩ := ups_plan hw hs hL
        obtain ⟨k'', hk'', f1, f2⟩ := partRow hw hs hL hP0 (qbAfter hw hs hL hi' hqi) hi'
        have hj' : s'.row i' j = k'' + 1 := by
          rw [show i' = ps[k''].1 + (i' - ps[k''].1) by omega, partPc hw hs hL hP0 k'' hk'' _ (by omega) (by decide)]
          exact (hL.part k'' hk'').1
        have hkk : k'' = k := by omega
        subst hkk
        have hτi : s'.row i' tau = s'.row 0 tau := hL.segc _ hi' tau (by decide)
        have hd := (U.rows (i' - ps[k''].1) (by omega)).2.1
        rw [show ps[k''].1 + (i' - ps[k''].1) = i' by omega] at hd
        refine ⟨i' - ps[k''].1, by rw [hencL]; omega, ?_⟩
        rw [hτi, hj', hd]
        simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (show i' - ps[k''].1 < ps[k''].2 by omega), Option.map_some, Option.getD_some]
        rw [show ps[k''].1 + (i' - ps[k''].1) = i' by omega]
    · obtain ⟨h1, h2⟩ := hoth m hm a ha
      have e := Link.ofNat_inj h1 (upsIdN_lt _ _) he
      rw [e, upsIdN_val hτ (by omega)] at h2
      unfold K_VUPS at h2; omega
  have core := Link.sha_core hsha _ hbytes (upsIdN_lt _ _) (fun x hx => by
      simp only [rowsB, List.mem_map, List.mem_range] at hx
      obtain ⟨d, -, rfl⟩ := hx; exact rowLt hw hs _ _)
    (by rw [hencL, P_lit]; omega) (fun x hx => by
      simp only [regN, List.mem_map, List.mem_range] at hx
      obtain ⟨d, -, rfl⟩ := hx; exact rowLt hw hs _ _) hS hrecv
  refine ⟨fun d hd => core.1 _ (by simp only [rowsB, List.mem_map, List.mem_range]; exact ⟨d, hd, rfl⟩), ?_⟩
  rw [core.2]; rfl


/-- **The parts of every segment** from the per-segment `UpsExt0` and sources and the global SHA / `MEMD`
facts: every part `k` emits `nodeEnc (upsQ … k)` with exact `MEMD` limbs. -/
theorem ups_partsG {v : List UpsSeg} (hw : UpsWf v) {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (others : List Msg) (hbytes : ∀ m, shaR B_BYTES m = cnt ((upsTraffic v).sends B_BYTES ++ others) m)
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdig : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) (hB : UpsIdBound v)
    {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val)
    (hsrcM : ∀ k, k < ps.length → isNode (src k) = true ∧ (src k).memD < 2 ^ 64) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) val kd sdx src k).memD) :=
  ups_partsS hw hs hL hP X0 hsrcM (sha_seg hw hsha others hbytes hoth hdig htau hB s hs L ps fls ws hL)
    (memd_seg hw hM htau s hs)

end ZkFormal.NearV3.UpsRows
