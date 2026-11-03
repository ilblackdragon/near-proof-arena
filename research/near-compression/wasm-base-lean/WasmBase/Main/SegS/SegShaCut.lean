import WasmBase.Main.SegShaCut
import WasmBase.Main.SegS.SegShaBytes
/-!
# WasmBase.Main.SegS.SegShaCut — `SegShaCut`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegShaCut.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

theorem cutT_segT {nloc ngl : Nat} {t : Nat} {cs : List String} {base : Nat}
    (hT : (t = 30 ∧ cs = Cut.In.cols ∧ base = pubCtxIn) ∨ (t = 31 ∧ cs = Cut.Out.cols ∧ base = pubCtxOut)) :
    SegT t := ⟨by rcases hT with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> decide⟩

end SegSha

namespace SegSha

section
variable {nloc ngl : Nat} {t : Nat} {cs : List String} {base : Nat} {pub : List F} {tr : Trace}
  {chip : List StateM5a.Sha512If.IfMsg} (H : HoldsXS nloc ngl pub tr)
  (hC : SegSha.ChipIfS compressW nloc ngl pub tr chip)
  (hT : (t = 30 ∧ cs = Cut.In.cols ∧ base = pubCtxIn) ∨ (t = 31 ∧ cs = Cut.Out.cols ∧ base = pubCtxOut))

include H hT in
theorem cutT_CS : ∀ r, r < tr.height t → ∀ e ∈ Cut.streamConstraints cs base, e.eval (tr.row pub t r) = 0 :=
  fun r hr e he => have : SegT t := cutT_segT (nloc := nloc) (ngl := ngl) hT; H.constr t (cutT_lt hT) r hr e ((cutT_tab hT).1 e he)

include H hC hT in
/-- The 8 chip receives of a CUT row whose count `kD + kP` is 1 are chip messages. -/
theorem cut_msgsS {r : Nat} (hr : r < tr.height t) (hcnt : kc tr t r 2 + kc tr t r 3 = 1) :
    (∀ i, i < 4 → (kc tr t r 22 :: (((i : Nat) : F) + ((12 : Nat) : F) * kc tr t r 1) ::
      (hwF tr pub t cs r (2 * i) ++ hwF tr pub t cs r (2 * i + 1))) ∈ chip.map ifF) ∧
    (∀ i, i < 4 → (kc tr t r 22 :: (((4 + i : Nat) : F) + ((4 : Nat) : F) * kc tr t r 1) ::
      (bwF tr pub t cs r (2 * i) ++ bwF tr pub t cs r (2 * i + 1))) ∈ chip.map ifF) := by
  obtain ⟨ia, ij, iD, iP, iX, igi, -, -, icid, -, -⟩ := cut_ixs (cutT_cs hT)
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) hT
  have hc1 : ((Cut.c cs "kD" + Cut.c cs "kP").eval (tr.row pub t r)).toNat = 1 := by
    rw [Expr.eval_add', kc_c, kc_c, iD, iP, hcnt]; decide
  have mem : ∀ i ∈ Cut.ifInters cs, i.bus = busIf → i.count = Cut.c cs "kD" + Cut.c cs "kP" →
      i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF := by
    intro i hi hb hcount
    exact if_recv_memS hC ht (cutT_segT (nloc := nloc) (ngl := ngl) hT).ne20 hr ((cutT_tab hT).2.1 i hi) hb
      (by rw [hcount]; exact hc1)
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := mem _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)) rfl rfl
    simpa [hwF, kc_c, ij, icid, List.map_append] using this
  · have := mem _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)) rfl rfl
    simpa [bwF, kc_c, ij, icid, List.map_append] using this

include H hC hT in
/-- **One CUT group is one chip compression**: rows `2g` (`j = 0`: `h_in`, block words 0–7) and
`2g + 1` (`j = 1`: block words 8–15, `h_out`) under one `cid`. -/
theorem cut_groupS {g : Nat} (hr : 2 * g + 1 < tr.height t)
    (hj0 : kc tr t (2 * g) 1 = 0) (hj1 : kc tr t (2 * g + 1) 1 = 1)
    (hcid : kc tr t (2 * g + 1) 22 = kc tr t (2 * g) 22)
    (hc0 : kc tr t (2 * g) 2 + kc tr t (2 * g) 3 = 1) (hc1 : kc tr t (2 * g + 1) 2 + kc tr t (2 * g + 1) 3 = 1) :
    ∃ h blk : List Nat, h.length = 8 ∧ blk.length = 16 ∧ StateM5a.Sha512If.W64 h ∧ StateM5a.Sha512If.W64 blk ∧
      (∀ k, k < 8 → hwF tr pub t cs (2 * g) k = wF (h.getD k 0)) ∧
      (∀ w, w < 8 → bwF tr pub t cs (2 * g) w = wF (blk.getD w 0)) ∧
      (∀ w, w < 8 → bwF tr pub t cs (2 * g + 1) w = wF (blk.getD (8 + w) 0)) ∧
      (∀ k, k < 8 → hwF tr pub t cs (2 * g + 1) k = wF ((compressW h blk).getD k 0)) := by
  let W : Nat → List F := fun k =>
    if k < 8 then hwF tr pub t cs (2 * g) k else if k < 16 then bwF tr pub t cs (2 * g) (k - 8)
    else if k < 24 then bwF tr pub t cs (2 * g + 1) (k - 16) else hwF tr pub t cs (2 * g + 1) (k - 24)
  have hW3 : ∀ k, k < 32 → (W k).length = 3 := by
    intro k _; simp only [W]
    split
    · exact hwF_len ..
    · split
      · exact bwF_len ..
      · split
        · exact bwF_len ..
        · exact hwF_len ..
  obtain ⟨m0a, m0b⟩ := cut_msgsS H hC hT (r := 2 * g) (by omega) hc0
  obtain ⟨m1a, m1b⟩ := cut_msgsS H hC hT (r := 2 * g + 1) hr hc1
  have hin : ∀ m, m < 16 → (kc tr t (2 * g) 22 :: ((m : Nat) : F) :: (W (2 * m) ++ W (2 * m + 1))) ∈ chip.map ifF := by
    intro m hm
    rcases (by omega : m < 4 ∨ (4 ≤ m ∧ m < 8) ∨ (8 ≤ m ∧ m < 12) ∨ (12 ≤ m ∧ m < 16)) with h | h | h | h
    · refine mem_congr (m0a m h) ?_
      simp only [W, hj0, show 2 * m < 8 by omega, show 2 * m + 1 < 8 by omega, if_true]
      congr 2; grind
    · refine mem_congr (m0b (m - 4) (by omega)) ?_
      simp only [W, hj0, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show 2 * m < 16 by omega,
        show 2 * m + 1 < 16 by omega, if_true, if_false, show 2 * m - 8 = 2 * (m - 4) by omega,
        show 2 * m + 1 - 8 = 2 * (m - 4) + 1 by omega]
      congr 2; rw [show m = 4 + (m - 4) by omega]; grind
    · refine mem_congr (m1b (m - 8) (by omega)) ?_
      simp only [W, hj1, hcid, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show ¬ 2 * m < 16 by omega,
        show ¬ 2 * m + 1 < 16 by omega, show 2 * m < 24 by omega, show 2 * m + 1 < 24 by omega, if_true, if_false,
        show 2 * m - 16 = 2 * (m - 8) by omega, show 2 * m + 1 - 16 = 2 * (m - 8) + 1 by omega]
      congr 2; rw [← cast_one, cast_pair]; congr 1; omega
    · refine mem_congr (m1a (m - 12) (by omega)) ?_
      simp only [W, hj1, hcid, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show ¬ 2 * m < 16 by omega,
        show ¬ 2 * m + 1 < 16 by omega, show ¬ 2 * m < 24 by omega, show ¬ 2 * m + 1 < 24 by omega, if_false,
        show 2 * m - 24 = 2 * (m - 12) by omega, show 2 * m + 1 - 24 = 2 * (m - 12) + 1 by omega]
      congr 2; rw [← cast_one, cast_pair]; congr 1; omega
  obtain ⟨h, blk, h8, h16, wh, wb, hW⟩ := consumer_sound compressW_ok hC.contract hC.cidLt hW3 hin
  refine ⟨h, blk, h8, h16, wh, wb, fun k hk => ?_, fun w hw => ?_, fun w hw => ?_, fun k hk => ?_⟩
  · have := hW k (by omega); simp only [W, hk, if_true] at this
    rw [this, words_getD_h h8 hk]
  · have := hW (8 + w) (by omega)
    simp only [W, show ¬ 8 + w < 8 by omega, show 8 + w < 16 by omega, if_true, if_false,
      show 8 + w - 8 = w by omega] at this
    rw [this, words_getD_b h8 h16 (by omega)]
  · have := hW (16 + w) (by omega)
    simp only [W, show ¬ 16 + w < 8 by omega, show ¬ 16 + w < 16 by omega, show 16 + w < 24 by omega, if_true,
      if_false, show 16 + w - 16 = w by omega] at this
    rw [this, show 16 + w = 8 + (8 + w) by omega, words_getD_b h8 h16 (by omega)]
  · have := hW (24 + k) (by omega)
    simp only [W, show ¬ 24 + k < 8 by omega, show ¬ 24 + k < 16 by omega, show ¬ 24 + k < 24 by omega,
      if_false, show 24 + k - 24 = k by omega] at this
    rw [this, words_getD_o h8 h16]

include H hC hT in
/-- **The CUT stream digest.**  A CUT table (CUTI with `ctx_in`, CUTO with `ctx_out`) has `2N` data
rows followed by the padding group, and its public digest limbs (`pub[base … base+18)`) are the
limbs of six 64-bit words `d` whose bytes are `sha384 (wbytes Ws)`, where `Ws` is the concatenation
of the 8 words every data row hashes (`streamW`, in row order; all `< 2^64`).  The padding block the
AIR hashes is exactly FIPS 180-4's for the `8·|Ws|`-byte message (`pad_whole`; `gi`, `gl`, `gh`). -/
theorem cut_stream_digestS :
    ∃ N, 2 * N + 2 ≤ tr.height t ∧ (∀ r, r < 2 * N → kc tr t r 2 = 1) ∧ kc tr t (2 * N) 3 = 1 ∧
      (∀ w ∈ (List.range (2 * N)).flatMap (streamW tr pub t cs), w < 2 ^ 64) ∧
      ∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub base = limbsF d ∧
        wbytes d = NearSpecV3.E2E.Bnd.sha384 (wbytes ((List.range (2 * N)).flatMap (streamW tr pub t cs))) := by
  have hcs := cutT_cs hT
  have hC' := cutT_CS H hT
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) hT
  have hh : 4 ≤ tr.height t := H.heightPos t ht
  obtain ⟨N, hN, hd, hp0, hp1, rows, hcid, hch⟩ := cut_rows hcs hC' hh
  have hP := P_val
  have hle := H.heightLe t ht
  unfold maxLogHeight at hle
  -- counts and `j`
  have cnt : ∀ r, r ≤ 2 * N + 1 → kc tr t r 2 + kc tr t r 3 = 1 := by
    intro r hr
    obtain ⟨-, -, k, -⟩ := cut_bits hcs hC' (r := r) (by omega)
    have x := (rows r hr).2.1
    rcases k with ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨-, -, c⟩
    · rw [a, b]; grind
    · rw [a, b]; grind
    · rw [x] at c; exact absurd c (by decide)
  have j0 : ∀ g, g ≤ N → kc tr t (2 * g) 1 = 0 := by
    intro g hg; rw [(rows (2 * g) (by omega)).1, jF, show 2 * g % 2 = 0 by omega]; rfl
  have j1 : ∀ g, g ≤ N → kc tr t (2 * g + 1) 1 = 1 := by
    intro g hg; rw [(rows (2 * g + 1) (by omega)).1, jF, show (2 * g + 1) % 2 = 1 by omega]; rfl
  have grp := fun g (hg : g ≤ N) => cut_groupS H hC hT (g := g) (by omega) (j0 g hg) (j1 g hg) (hcid g hg)
    (cnt _ (by omega)) (cnt _ (by omega))
  -- a group's block is the two rows' decoded words
  let Bk : Nat → List Nat := fun g => streamW tr pub t cs (2 * g) ++ streamW tr pub t cs (2 * g + 1)
  have getw : ∀ (l : List Nat), StateM5a.Sha512If.W64 l → ∀ k, l.getD k 0 < 2 ^ 64 := by
    intro l hl k
    rw [List.getD_eq_getElem?_getD]
    rcases e : l[k]? with _ | w
    · simp
    · exact hl w (List.mem_of_getElem? e)
  have blkEq : ∀ g, g ≤ N → ∀ blk : List Nat, blk.length = 16 → StateM5a.Sha512If.W64 blk →
      (∀ w, w < 8 → bwF tr pub t cs (2 * g) w = wF (blk.getD w 0)) →
      (∀ w, w < 8 → bwF tr pub t cs (2 * g + 1) w = wF (blk.getD (8 + w) 0)) → blk = Bk g := by
    intro g _ blk h16 wb e0 e1
    apply List.ext_getElem (by simp [Bk, streamW, h16]); intro k hk1 hk2
    have gk : blk[k] = blk.getD k 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
    rw [gk]
    simp only [Bk, streamW]
    by_cases hk : k < 8
    · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_range, e0 k hk,
        decW_wF (getw blk wb k)]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [e1 (k - 8) (by omega), show 8 + (k - 8) = k by omega, decW_wF (getw blk wb k)]
  let Hf : Nat → List Nat := fun g => ((List.range g).map Bk).foldl compressW NearSpecV3.E2E.Bnd.IV384
  have Hok : ∀ g, (Hf g).length = 8 ∧ StateM5a.Sha512If.W64 (Hf g) := fun g => foldl_ok _ _ iv_ok.1 iv_ok.2
  have claim : ∀ g, g ≤ N → ∀ k, k < 8 → hwF tr pub t cs (2 * g) k = wF ((Hf g).getD k 0) := by
    intro g
    induction g with
    | zero =>
      intro _ k hk
      rw [hwF_eq hcs 0 hk]
      have f := (cut_first hcs hC' (by omega)).2.2.2
      rw [f _ (by omega), f _ (by omega), f _ (by omega), iv_limbs' k hk]
      rfl
    | succ g ih =>
      intro hg k hk
      obtain ⟨h, blk, h8, h16, wh, wb, eh, e0, e1, eo⟩ := grp g (by omega)
      have hh' : h = Hf g := list_eq_of_wF h8 (Hok g).1 wh (Hok g).2 (fun k hk => by
        rw [← eh k hk, ih (by omega) k hk])
      have hb := blkEq g (by omega) blk h16 wb e0 e1
      have step : hwF tr pub t cs (2 * (g + 1)) k = hwF tr pub t cs (2 * g + 1) k := by
        rw [hwF_eq hcs _ hk, hwF_eq hcs _ hk, show 2 * (g + 1) = 2 * g + 2 by omega,
          hch g (by omega) _ (by omega), hch g (by omega) _ (by omega), hch g (by omega) _ (by omega)]
      rw [step, eo k hk, hh', hb]
      simp only [Hf, List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil]
  -- the padding group
  obtain ⟨h, blk, h8, h16, wh, wb, eh, e0, e1, eo⟩ := grp N (Nat.le_refl _)
  have hh' : h = Hf N := list_eq_of_wF h8 (Hok N).1 wh (Hok N).2 (fun k hk => by rw [← eh k hk, claim N (by omega) k hk])
  have hb := blkEq N (Nat.le_refl _) blk h16 wb e0 e1
  -- `gl`, `gh` and the length word
  obtain ⟨ia, ij, iD, iP, iX, igi, igl, igh, icid, ih, -⟩ := cut_ixs hcs
  have r1 : 2 * N + 1 < tr.height t := by omega
  have kD1 : kc tr t (2 * N + 1) 2 = 0 := by
    have := cnt _ (Nat.le_refl _); rw [hp1] at this; grind
  have kD0 : kc tr t (2 * N) 2 = 0 := by
    have := cnt (2 * N) (by omega); rw [hp0] at this; grind
  have act1 := (cut_bits hcs hC' (r := 2 * N + 1) r1).2.2.2 kD1
  have act0 := (cut_bits hcs hC' (r := 2 * N) (by omega)).2.2.2 kD0
  have g1 : ((Cut.c cs "kP" * Cut.c cs "j").eval (tr.row pub t (2 * N + 1))).toNat = 1 := by
    rw [Expr.eval_mul', kc_c, kc_c, iP, ij, hp1, j1 N (Nat.le_refl _)]; decide
  have q : ∀ e, r16 e (Cut.c cs "kP" * Cut.c cs "j") ∈ Cut.padR16 cs → (e.eval (tr.row pub t (2 * N + 1))).toNat < 65536 :=
    fun e he => seg_r16_ltS H (seg_hsend_r16S H) ht r1 ((cutT_tab hT).2.2 _ he) g1
  have q1 := q (32 * Cut.c cs "gl") (by simp [Cut.padR16])
  have q2 := q (Cut.c cs "gh") (by simp [Cut.padR16])
  have q3 := q (Cut.c cs "gl") (by simp [Cut.padR16])
  simp only [Expr.eval_mul', Expr.eval_ofNat', kc_c, igl, igh] at q1 q2 q3
  rw [← Fp.cast_toNat (kc tr t (2 * N + 1) 20), mulq_toNat (by omega)] at q1
  have hgi := hC' (2 * N + 1) r1 (Cut.c cs "kP" * Cut.c cs "j" * (Cut.c cs "gi" - Cut.c cs "gl" - 2048 * Cut.c cs "gh"))
    (by simp [Cut.streamConstraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c, iP, ij, igi, igl, igh, hp1, j1 N (Nat.le_refl _),
    (rows (2 * N + 1) (Nat.le_refl _)).2.2.2, show (2 * N + 1) / 2 = N by omega] at hgi
  have hNg : N = (kc tr t (2 * N + 1) 20).toNat + 2048 * (kc tr t (2 * N + 1) 21).toNat := by
    have e : ((N : Nat) : F) = (((kc tr t (2 * N + 1) 20).toNat + 2048 * (kc tr t (2 * N + 1) 21).toNat : Nat) : F) := by
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat, Fp.cast_toNat]
      grind
    exact natEq e (by omega) (by omega)
  have z : ∀ x : F, 0 * x = 0 := by intro x; grind
  have toN0 : (0 : F).toNat = 0 := rfl
  have w0 : (0 : F) + 1 * (1 - 0) * ((2 ^ 21 : Nat) : F) = ((2 ^ 21 : Nat) : F) := by grind
  have w0' : (0 : F) + 1 * (1 - 1) * ((2 ^ 21 : Nat) : F) = 0 := by grind
  have gl' : kc tr t (2 * N + 1) 20 = (((kc tr t (2 * N + 1) 20).toNat : Nat) : F) := (Fp.cast_toNat _).symm
  have w7 : (1 : F) * 1 * ((1024 : Nat) : F) * kc tr t (2 * N + 1) 20 =
      ((1024 * (kc tr t (2 * N + 1) 20).toNat : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_mul, ← gl']; grind
  have w7' : (1 : F) * 1 * kc tr t (2 * N + 1) 21 = kc tr t (2 * N + 1) 21 := by grind
  have w7z : (1 : F) * 0 * ((1024 : Nat) : F) * kc tr t (2 * N) 20 = 0 := by grind
  have w7z' : (1 : F) * 0 * kc tr t (2 * N) 21 = 0 := by grind
  have range8 : ∀ (f : Nat → Nat), (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := fun f => rfl
  have sw0 : streamW tr pub t cs (2 * N) = [2 ^ 63, 0, 0, 0, 0, 0, 0, 0] := by
    rw [streamW, range8]
    simp only [bwF_eq hcs (2 * N) (show (0 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (1 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (2 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (3 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (4 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (5 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (6 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (7 : Nat) < 8 by decide),
      kD0, hp0, act0, j0 N (Nat.le_refl _), z, w0, w7z, w7z']
    simp only [decW, List.getD_cons_zero, List.getD_cons_succ, toN0, Fp.toNat_cast_of_lt (show 2 ^ 21 < P by omega)]
    decide
  have sw1 : streamW tr pub t cs (2 * N + 1) = [0, 0, 0, 0, 0, 0, 0, 1024 * N] := by
    rw [streamW, range8]
    simp only [bwF_eq hcs (2 * N + 1) (show (0 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (1 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (2 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (3 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (4 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (5 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (6 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (7 : Nat) < 8 by decide),
      kD1, hp1, act1, j1 N (Nat.le_refl _), z, w0', w7, w7']
    simp only [decW, List.getD_cons_zero, List.getD_cons_succ, toN0, ↓reduceIte, Nat.reduceLT, ite_true, ite_false, ite_self,
      Fp.toNat_cast_of_lt (show 1024 * (kc tr t (2 * N + 1) 20).toNat < P by omega)]
    simp only [Nat.mul_zero, Nat.add_zero, List.cons.injEq, and_true, true_and]
    omega
  have hpad : Bk N = padBlk (1024 * N) := by
    simp only [Bk, sw0, sw1, padBlk, show 1024 * N / 2 ^ 64 % 2 ^ 64 = 0 by omega,
      show 1024 * N % 2 ^ 64 = 1024 * N by omega]
    rfl
  -- the digest
  let out := compressW (Hf N) (Bk N)
  have hco := compressW_ok (Hf N) (Bk N)
  have hfin : ∀ k, k < 8 → hwF tr pub t cs (2 * N + 1) k = wF (out.getD k 0) := by
    intro k hk; rw [eo k hk, hh', hb]
  have h6 : (out.take 6).length = 6 := by rw [List.length_take, show out.length = 8 from hco.1]; rfl
  have hBk : ∀ g, g < N → (Bk g).length = 16 ∧ StateM5a.Sha512If.W64 (Bk g) := by
    intro g hg
    obtain ⟨-, blk', -, h16', -, wb', -, e0', e1', -⟩ := grp g (by omega)
    have := blkEq g (by omega) blk' h16' wb' e0' e1'
    rw [← this]; exact ⟨h16', wb'⟩
  have hWs : (List.range (2 * N)).flatMap (streamW tr pub t cs) = ((List.range N).map Bk).flatten := by
    rw [range2_flatMap, List.flatMap_def]
  have hlen : ((List.range N).map Bk).flatten.length = 16 * N := by
    rw [List.length_flatten, List.map_map]
    have : ((List.range N).map (List.length ∘ Bk)) = List.replicate N 16 := by
      apply List.ext_getElem (by simp); intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
      exact (hBk i (by simpa using h1)).1
    rw [this]
    clear this
    induction N with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, List.sum_cons]; omega
  refine ⟨N, hN, hd, hp0, ?_, out.take 6, h6, fun w hw => hco.2 w (List.mem_of_mem_take hw), ?_, ?_⟩
  · intro w hw
    rw [hWs] at hw
    obtain ⟨B, hB, hwB⟩ := List.mem_flatten.1 hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hB
    exact (hBk g (List.mem_range.1 hg)).2 w hwB
  · have hpub : ∀ i, i < 18 → pub.getD (base + i) 0 = kc tr t (2 * N + 1) (23 + i) := by
      intro i hi
      have e := hC' (2 * N + 1) r1 (Cut.c cs "kP" * Cut.c cs "j" * (Cut.c cs s!"h{i}" - pv (base + i))) (by
        simp only [Cut.streamConstraints, List.mem_append]
        right
        exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      simp only [Expr.eval_mul', Expr.eval_sub', kc_c, iP, ij, ih i (by omega), hp1, j1 N (Nat.le_refl _),
        pv, Expr.eval_pub] at e
      have e' : ∀ x y : F, 1 * 1 * (x - y) = 0 → y = x := by intro x y h; grind
      exact e' _ _ e
    have hf := flat_triples (out.take 6) (fun i => kc tr t (2 * N + 1) (23 + i)) (fun k hk6 => by
      have hk6' : k < 6 := by rw [h6] at hk6; exact hk6
      rw [show (out.take 6).getD k 0 = out.getD k 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk6'], ← hfin k (by omega), hwF_eq hcs _ (by omega)]
      rfl)
    rw [h6] at hf
    rw [← hf]
    simp only [pubDig]
    apply List.map_congr_left; intro i hi
    exact hpub i (List.mem_range.1 hi)
  · rw [hWs, sha384_whole N _ hlen]
    have hc : chunks16 N ((List.range N).map Bk).flatten = (List.range N).map Bk := by
      have := chunks16_flatten ((List.range N).map Bk) (fun B hB => by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hB
        exact (hBk g (List.mem_range.1 hg)).1)
      simpa using this
    rw [hc, ← hpad]

end

end SegSha

end WasmBase
