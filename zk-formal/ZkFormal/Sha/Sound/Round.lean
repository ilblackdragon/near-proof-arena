import ZkFormal.Sha.Sound.Kind
import ZkFormal.Sha.Spec

/-!
# ZkFormal.Sha.Sound.Round — row-local consequences of `cRound/cSched/cHelp/cDigest`

Each lemma looks at one row `r` and its successor `r + 1 < H` and turns the
limb additions of one constraint family into one `Nat` equation mod `2^32`
on decoded words (`View.wordAt`).
-/

namespace ZkFormal.Sha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View ZkFormal.Sha.Table
open ArenaCore.SHA256

set_option linter.deprecated false

/-- Expand the sum of a mapped literal list. -/
macro "sumsimp" : tactic =>
  `(tactic| simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil])

variable {tr : Trace Fp} {t : Nat} {pub : List Fp} {r : Nat}

/-- Word of window slot `u` (`u < 4`: row `r`, else row `r + 1`) of bit columns `col`. -/
def winW (tr : Trace Fp) (t r : Nat) (col : Nat → Nat → Nat) (u : Nat) : Nat :=
  if u < 4 then wordAt tr t r (col u) else wordAt tr t (r + 1) (col (u - 4))

/-- `W_{t-2}` of next-row slot `i`. -/
def w2W (tr : Trace Fp) (t r i : Nat) : Nat :=
  if i < 2 then wordAt tr t r (colW (i + 2)) else wordAt tr t (r + 1) (colW (i - 2))

/-- `W_{t-15}` of the helper computed on the next row, slot `i`. -/
def w15W (tr : Trace Fp) (t r i : Nat) : Nat :=
  if i < 3 then wordAt tr t r (colW (i + 1)) else wordAt tr t (r + 1) (colW 0)

/-- Value of the pair of 16-bit cells `col 0`, `col 1`. -/
def pairW (tr : Trace Fp) (t r : Nat) (col : Nat → Nat) : Nat :=
  nv tr t r (col 0) + 65536 * nv tr t r (col 1)

/-- `W_{t-7}` of next-row slot `i`. -/
def w7W (tr : Trace Fp) (t r i : Nat) : Nat :=
  if i < 3 then pairW tr t r (colW3 i) else wordAt tr t r (colW 0)

/-! ## Basic facts -/

theorem bitc (hL : ShaLocal tr t pub) (hr0 : r < tr.height t) {x : Nat} (hx : x < 456) :
    ev tr t r pub (E.c x) ≤ 1 := bool_of hL hr0 (mem_boolCols_lo hx)

theorem bitn (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {x : Nat} (hx : x < 456) :
    ev tr t r pub (E.n x) ≤ 1 := by
  rw [ev_n hr]; exact bool_of hL hr (mem_boolCols_lo hx)

theorem wv_c_col (col : Nat → Nat) : wv tr t r pub (fun b => E.c (col b)) = wordAt tr t r col := rfl

theorem wv_n_col (hr : r + 1 < tr.height t) (col : Nat → Nat) :
    wv tr t r pub (fun b => E.n (col b)) = wordAt tr t (r + 1) col := by
  unfold wv wordAt; simp only [ev_n hr]

theorem colA_lt {i b : Nat} (hi : i < 4) (hb : b < 32) : colA i b < 456 := by unfold colA; omega
theorem colE_lt {i b : Nat} (hi : i < 4) (hb : b < 32) : colE i b < 456 := by unfold colE; omega
theorem colW_lt {i b : Nat} (hi : i < 4) (hb : b < 32) : colW i b < 456 := by unfold colW; omega
theorem colSt_lt {w b : Nat} (hw : w < 8) (hb : b < 32) : colSt w b < 456 := by
  unfold colSt colA colE; split <;> omega

theorem win_le (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) (col : Nat → Nat → Nat)
    (hcol : ∀ i b, i < 4 → b < 32 → col i b < 456) {u : Nat} (hu : u < 8) :
    ∀ b, b < 32 →
      ev tr t r pub (if u < 4 then E.c (col u b) else E.n (col (u - 4) b)) ≤ 1 := by
  intro b hb
  split
  · exact bitc hL (by omega) (hcol _ _ (by omega) hb)
  · exact bitn hL hr (hcol _ _ (by omega) hb)

theorem wv_win (hr : r + 1 < tr.height t) (col : Nat → Nat → Nat) (u : Nat) :
    wv tr t r pub (fun b => if u < 4 then E.c (col u b) else E.n (col (u - 4) b)) =
      winW tr t r col u := by
  unfold winW
  by_cases hu : u < 4
  · simp only [hu, ↓reduceIte]; rfl
  · simp only [hu, ↓reduceIte]; exact wv_n_col hr _

theorem winA_le (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {u : Nat} (hu : u < 8) :
    ∀ b, b < 32 → ev tr t r pub (winA u b) ≤ 1 :=
  win_le hL hr colA (fun _ _ => colA_lt) hu

theorem winE_le (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {u : Nat} (hu : u < 8) :
    ∀ b, b < 32 → ev tr t r pub (winE u b) ≤ 1 :=
  win_le hL hr colE (fun _ _ => colE_lt) hu

theorem wv_winA (hr : r + 1 < tr.height t) (u : Nat) : wv tr t r pub (winA u) = winW tr t r colA u :=
  wv_win hr colA u

theorem wv_winE (hr : r + 1 < tr.height t) (u : Nat) : wv tr t r pub (winE u) = winW tr t r colE u :=
  wv_win hr colE u

theorem carry_lt (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) (cc : Nat → Nat → Nat)
    (l : Nat) (hcc : ∀ k, k < 3 → cc l k < 456) : ev tr t r pub (carryN cc l) < 8 :=
  ev_bits3_lt _ (fun k hk => bitn hL hr (hcc k hk))

theorem Kt_lt (u : Nat) : Spec.Kt u < 2 ^ 32 := by
  unfold Spec.Kt
  rw [List.getD_eq_getElem?_getD]
  have hall : ∀ x ∈ ArenaCore.SHA256.K, x < 2 ^ 32 := by decide
  cases h : ArenaCore.SHA256.K[u]? with
  | none => exact Nat.two_pow_pos _
  | some x => exact hall x (List.mem_of_getElem? h)

theorem K_split (j i : Nat) :
    (ArenaCore.SHA256.K.getD (4 * j + i) 0 / 2 ^ (16 * 0)) % 2 ^ 16 +
      65536 * ((ArenaCore.SHA256.K.getD (4 * j + i) 0 / 2 ^ (16 * 1)) % 2 ^ 16) =
      Spec.Kt (4 * j + i) := by
  have := Kt_lt (4 * j + i)
  unfold Spec.Kt at *
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
  omega

/-! ## Limb arithmetic -/

theorem add7 {a0 a1 A b0 b1 B c0 c1 C d0 d1 D e0 e1 E f0 f1 F g0 g1 G r0 r1 R z k0 k1 : Nat}
    (ha : a0 + 65536 * a1 = A) (hb : b0 + 65536 * b1 = B) (hc : c0 + 65536 * c1 = C)
    (hd : d0 + 65536 * d1 = D) (he : e0 + 65536 * e1 = E) (hf : f0 + 65536 * f1 = F)
    (hg : g0 + 65536 * g1 = G) (hr : r0 + 65536 * r1 = R) (hr0 : r0 < 65536) (hr1 : r1 < 65536)
    (hz : z = 0)
    (h0 : a0 + (b0 + (c0 + (d0 + (e0 + (f0 + (g0 + 0)))))) + z = r0 + 65536 * k0)
    (h1 : a1 + (b1 + (c1 + (d1 + (e1 + (f1 + (g1 + 0)))))) + k0 = r1 + 65536 * k1) :
    R = (A + B + C + D + E + F + G) % 2 ^ 32 := by
  omega

theorem add6 {a0 a1 A b0 b1 B c0 c1 C d0 d1 D e0 e1 E f0 f1 F r0 r1 R z k0 k1 : Nat}
    (ha : a0 + 65536 * a1 = A) (hb : b0 + 65536 * b1 = B) (hc : c0 + 65536 * c1 = C)
    (hd : d0 + 65536 * d1 = D) (he : e0 + 65536 * e1 = E) (hf : f0 + 65536 * f1 = F)
    (hr : r0 + 65536 * r1 = R) (hr0 : r0 < 65536) (hr1 : r1 < 65536)
    (hz : z = 0)
    (h0 : a0 + (b0 + (c0 + (d0 + (e0 + (f0 + 0))))) + z = r0 + 65536 * k0)
    (h1 : a1 + (b1 + (c1 + (d1 + (e1 + (f1 + 0))))) + k0 = r1 + 65536 * k1) :
    R = (A + B + C + D + E + F) % 2 ^ 32 := by
  omega

theorem add3 {a0 a1 A b0 b1 B c0 c1 C r0 r1 R z k0 k1 : Nat}
    (ha : a0 + 65536 * a1 = A) (hb : b0 + 65536 * b1 = B) (hc : c0 + 65536 * c1 = C)
    (hr : r0 + 65536 * r1 = R) (hr0 : r0 < 65536) (hr1 : r1 < 65536)
    (hz : z = 0)
    (h0 : a0 + (b0 + (c0 + 0)) + z = r0 + 65536 * k0)
    (h1 : a1 + (b1 + (c1 + 0)) + k0 = r1 + 65536 * k1) :
    R = (A + B + C) % 2 ^ 32 := by
  omega

theorem add2 {a0 a1 A b0 b1 B r0 r1 R z k0 k1 : Nat}
    (ha : a0 + 65536 * a1 = A) (hb : b0 + 65536 * b1 = B)
    (hr : r0 + 65536 * r1 = R) (hr0 : r0 < 65536) (hr1 : r1 < 65536)
    (hz : z = 0)
    (h0 : a0 + (b0 + 0) + z = r0 + 65536 * k0)
    (h1 : a1 + (b1 + 0) + k0 = r1 + 65536 * k1) :
    R = (A + B) % 2 ^ 32 := by
  omega

/-! ## Rounds -/

theorem roundA_mem {i l : Nat} (hi : i < 4) (hl : l < 2) : roundA i l ∈ constraints :=
  mem_cRound (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, List.mem_cons_self ..⟩⟩)

theorem roundE_mem {i l : Nat} (hi : i < 4) (hl : l < 2) : roundE i l ∈ constraints :=
  mem_cRound (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩)

/-- The four rounds of round row `Rj` (next row), slot `i`. -/
theorem round_step (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {j i : Nat} (hj : j < 16)
    (hR : nv tr t (r + 1) (colR j) = 1) (hi : i < 4) :
    wordAt tr t (r + 1) (colA i) =
      (winW tr t r colE i + bsig1 (winW tr t r colE (i + 3)) +
        ch (winW tr t r colE (i + 3)) (winW tr t r colE (i + 2)) (winW tr t r colE (i + 1)) +
        Spec.Kt (4 * j + i) + wordAt tr t (r + 1) (colW i) + bsig0 (winW tr t r colA (i + 3)) +
        maj (winW tr t r colA (i + 3)) (winW tr t r colA (i + 2)) (winW tr t r colA (i + 1)))
        % 2 ^ 32 ∧
    wordAt tr t (r + 1) (colE i) =
      (winW tr t r colA i + winW tr t r colE i + bsig1 (winW tr t r colE (i + 3)) +
        ch (winW tr t r colE (i + 3)) (winW tr t r colE (i + 2)) (winW tr t r colE (i + 1)) +
        Spec.Kt (4 * j + i) + wordAt tr t (r + 1) (colW i)) % 2 ^ 32 := by
  have hK := kindStmt tr t pub hL
  have hr0 : r < tr.height t := by omega
  have hg := ev_gRound (pub := pub) hK hr hj hR
  have bE : ∀ u, u < 8 → ∀ b, b < 32 → ev tr t r pub (winE u b) ≤ 1 :=
    fun u hu => winE_le hL hr hu
  have bA : ∀ u, u < 8 → ∀ b, b < 32 → ev tr t r pub (winA u b) ≤ 1 :=
    fun u hu => winA_le hL hr hu
  obtain ⟨sE, sE0, sE1⟩ := limb_split (winE i) (bE i (by omega))
  obtain ⟨sA, sA0, sA1⟩ := limb_split (winA i) (bA i (by omega))
  obtain ⟨sS1, sS10, sS11⟩ := limb_split (E.sig (winE (i + 3)) 6 11 25 false)
    (fun b _ => sig_le _ _ _ _ _ (bE (i + 3) (by omega)) b)
  obtain ⟨sCh, sCh0, sCh1⟩ := limb_split (fun b => E.ch (winE (i + 3) b) (winE (i + 2) b) (winE (i + 1) b))
    (ch_le _ _ _ (bE _ (by omega)) (bE _ (by omega)) (bE _ (by omega)))
  obtain ⟨sW, sW0, sW1⟩ := limb_split (fun b => E.n (colW i b))
    (fun b hb => bitn hL hr (colW_lt hi hb))
  obtain ⟨sS0, sS00, sS01⟩ := limb_split (E.sig (winA (i + 3)) 2 13 22 false)
    (fun b _ => sig_le _ _ _ _ _ (bA (i + 3) (by omega)) b)
  obtain ⟨sMj, sMj0, sMj1⟩ := limb_split (fun b => E.maj (winA (i + 3) b) (winA (i + 2) b) (winA (i + 1) b))
    (maj_le _ _ _ (bA _ (by omega)) (bA _ (by omega)) (bA _ (by omega)))
  obtain ⟨sRA, sRA0, sRA1⟩ := limb_split (fun b => E.n (colA i b))
    (fun b hb => bitn hL hr (colA_lt hi hb))
  obtain ⟨sRE, sRE0, sRE1⟩ := limb_split (fun b => E.n (colE i b))
    (fun b hb => bitn hL hr (colE_lt hi hb))
  have hK0 := ev_kLimb (pub := pub) hK hr hj hR i 0
  have hK1 := ev_kLimb (pub := pub) hK hr hj hR i 1
  have hKs : ev tr t r pub (kLimb i 0) + 65536 * ev tr t r pub (kLimb i 1) = Spec.Kt (4 * j + i) := by
    rw [hK0, hK1]; exact K_split j i
  have hcA0 := carry_lt hL hr (colCA i) 0 (fun k hk => by unfold colCA; omega)
  have hcA1 := carry_lt hL hr (colCA i) 1 (fun k hk => by unfold colCA; omega)
  have hcE0 := carry_lt hL hr (colCE i) 0 (fun k hk => by unfold colCE; omega)
  have hcE1 := carry_lt hL hr (colCE i) 1 (fun k hk => by unfold colCE; omega)
  have hKl0 : ev tr t r pub (kLimb i 0) < 65536 := by rw [hK0]; exact Nat.mod_lt _ (by decide)
  have hKl1 : ev tr t r pub (kLimb i 1) < 65536 := by rw [hK1]; exact Nat.mod_lt _ (by decide)
  have cA0 := hold hL hr0 (roundA_mem hi (l := 0) (by decide))
  have cA1 := hold hL hr0 (roundA_mem hi (l := 1) (by decide))
  have cE0 := hold hL hr0 (roundE_mem hi (l := 0) (by decide))
  have cE1 := hold hL hr0 (roundE_mem hi (l := 1) (by decide))
  simp only [roundA, roundE, ↓reduceIte, Nat.one_ne_zero] at cA0 cA1 cE0 cE1
  have ev0 : ev tr t r pub (E.k 0) = 0 := rfl
  have eA0 := addC_sound hg cA0 (by sumsimp; omega) (by omega)
  have eA1 := addC_sound hg cA1 (by sumsimp; omega) (by omega)
  have eE0 := addC_sound hg cE0 (by sumsimp; omega) (by omega)
  have eE1 := addC_sound hg cE1 (by sumsimp; omega) (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at eA0 eA1 eE0 eE1
  rw [wv_sig _ _ _ _ (by decide) (by decide) (by decide) (bE _ (by omega)), wv_winE hr] at sS1
  rw [wv_sig _ _ _ _ (by decide) (by decide) (by decide) (bA _ (by omega)), wv_winA hr] at sS0
  rw [wv_ch _ _ _ (bE _ (by omega)) (bE _ (by omega)) (bE _ (by omega)), wv_winE hr, wv_winE hr,
    wv_winE hr] at sCh
  rw [wv_maj _ _ _ (bA _ (by omega)) (bA _ (by omega)) (bA _ (by omega)), wv_winA hr, wv_winA hr,
    wv_winA hr] at sMj
  rw [wv_winE hr] at sE
  rw [wv_winA hr] at sA
  rw [wv_n_col hr] at sW sRA sRE
  have hb1 : rotr (winW tr t r colE (i + 3)) 6 ^^^ rotr (winW tr t r colE (i + 3)) 11 ^^^
      rotr (winW tr t r colE (i + 3)) 25 = bsig1 (winW tr t r colE (i + 3)) := rfl
  have hb0 : rotr (winW tr t r colA (i + 3)) 2 ^^^ rotr (winW tr t r colA (i + 3)) 13 ^^^
      rotr (winW tr t r colA (i + 3)) 22 = bsig0 (winW tr t r colA (i + 3)) := rfl
  rw [hb1] at sS1
  rw [hb0] at sS0
  exact ⟨add7 sE sS1 sCh hKs sW sS0 sMj sRA sRA0 sRA1 ev0 eA0 eA1,
    add6 sA sE sS1 sCh hKs sW sRE sRE0 sRE1 ev0 eE0 eE1⟩

/-! ## Message schedule -/

theorem sched_mem {i l : Nat} (hi : i < 4) (hl : l < 2) : sched i l ∈ constraints :=
  mem_cSched (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩⟩)

/-- Schedule word of next-row slot `i` (rows `R4..R15`). -/
theorem sched_step (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {j i : Nat} (hj : j < 16)
    (hj4 : 4 ≤ j) (hR : nv tr t (r + 1) (colR j) = 1) (hi : i < 4)
    (hI0 : nv tr t r (colI12 i 0) < 2 ^ 17) (hI1 : nv tr t r (colI12 i 1) < 2 ^ 17)
    (hW3 : i < 3 → nv tr t r (colW3 i 0) < 65536 ∧ nv tr t r (colW3 i 1) < 65536) :
    wordAt tr t (r + 1) (colW i) =
      (ssig1 (w2W tr t r i) + w7W tr t r i + pairW tr t r (colI12 i)) % 2 ^ 32 := by
  have hK := kindStmt tr t pub hL
  have hr0 : r < tr.height t := by omega
  have hg := ev_gSched (pub := pub) hK hr hj hj4 hR
  have b2 : ∀ b, b < 32 → ev tr t r pub (w2 i b) ≤ 1 := by
    intro b hb; unfold w2; split
    · exact bitc hL hr0 (colW_lt (by omega) hb)
    · exact bitn hL hr (colW_lt (by omega) hb)
  have hw2 : wv tr t r pub (w2 i) = w2W tr t r i := by
    unfold w2 w2W
    by_cases h : i < 2
    · simp only [h, ↓reduceIte]; rfl
    · simp only [h, ↓reduceIte]; exact wv_n_col hr _
  obtain ⟨sS, sS0, sS1⟩ := limb_split (E.sig (w2 i) 17 19 10 true) (fun b _ => sig_le _ _ _ _ _ b2 b)
  rw [wv_sigS _ _ _ _ (by decide) (by decide) b2, hw2] at sS
  have hs1 : rotr (w2W tr t r i) 17 ^^^ rotr (w2W tr t r i) 19 ^^^ (w2W tr t r i >>> 10) =
      ssig1 (w2W tr t r i) := rfl
  rw [hs1] at sS
  have s7 : ev tr t r pub (w7 i 0) + 65536 * ev tr t r pub (w7 i 1) = w7W tr t r i ∧
      ev tr t r pub (w7 i 0) < 65536 ∧ ev tr t r pub (w7 i 1) < 65536 := by
    unfold w7 w7W
    by_cases h : i < 3
    · simp only [h, ↓reduceIte, ev_c]; unfold pairW; have := hW3 h; omega
    · simp only [h, ↓reduceIte]
      rw [← wv_c_col]
      exact limb_split (fun b => E.c (colW 0 b)) (fun b hb => bitc hL hr0 (colW_lt (by decide) hb))
  obtain ⟨sR, sR0, sR1⟩ := limb_split (fun b => E.n (colW i b)) (fun b hb => bitn hL hr (colW_lt hi hb))
  rw [wv_n_col hr] at sR
  have hI : ev tr t r pub (E.c (colI12 i 0)) + 65536 * ev tr t r pub (E.c (colI12 i 1)) =
      pairW tr t r (colI12 i) := rfl
  have hI0' : ev tr t r pub (E.c (colI12 i 0)) < 2 ^ 17 := hI0
  have hI1' : ev tr t r pub (E.c (colI12 i 1)) < 2 ^ 17 := hI1
  have hc0 := carry_lt hL hr (colCW i) 0 (fun k hk => by unfold colCW; omega)
  have hc1 := carry_lt hL hr (colCW i) 1 (fun k hk => by unfold colCW; omega)
  have c0 := hold hL hr0 (sched_mem hi (l := 0) (by decide))
  have c1 := hold hL hr0 (sched_mem hi (l := 1) (by decide))
  simp only [sched, ↓reduceIte, Nat.one_ne_zero] at c0 c1
  have ev0 : ev tr t r pub (E.k 0) = 0 := rfl
  obtain ⟨s7e, s70, s71⟩ := s7
  have e0 := addC_sound hg c0 (by sumsimp; omega) (by omega)
  have e1 := addC_sound hg c1 (by sumsimp; omega) (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e0 e1
  exact add3 sS s7e hI sR sR0 sR1 ev0 e0 e1

/-! ## Helpers `I4/I8/I12/W3` and the chaining value `Hin` -/

theorem w15_le (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {i : Nat} (hi : i < 4) :
    ∀ b, b < 32 → ev tr t r pub (w15 i b) ≤ 1 := by
  intro b hb; unfold w15; split
  · exact bitc hL (by omega) (colW_lt (by omega) hb)
  · exact bitn hL hr (colW_lt (by decide) hb)

theorem wv_w15 (hr : r + 1 < tr.height t) (i : Nat) : wv tr t r pub (w15 i) = w15W tr t r i := by
  unfold w15 w15W
  by_cases h : i < 3
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]; exact wv_n_col hr _

theorem help_I4 (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {j i : Nat} (hj : j < 16)
    (hj1 : 1 ≤ j) (hR : nv tr t (r + 1) (colR j) = 1) (hi : i < 4) :
    pairW tr t (r + 1) (colI4 i) = ssig0 (w15W tr t r i) + wordAt tr t r (colW i) ∧
      nv tr t (r + 1) (colI4 i 0) < 2 ^ 17 ∧ nv tr t (r + 1) (colI4 i 1) < 2 ^ 17 := by
  have hK := kindStmt tr t pub hL
  have hr0 : r < tr.height t := by omega
  have hg := ev_gHelp (pub := pub) hK hr hj hj1 hR
  have b15 := w15_le hL hr hi
  obtain ⟨sS, sS0, sS1⟩ := limb_split (E.sig (w15 i) 7 18 3 true) (fun b _ => sig_le _ _ _ _ _ b15 b)
  rw [wv_sigS _ _ _ _ (by decide) (by decide) b15, wv_w15 hr] at sS
  have hs0 : rotr (w15W tr t r i) 7 ^^^ rotr (w15W tr t r i) 18 ^^^ (w15W tr t r i >>> 3) =
      ssig0 (w15W tr t r i) := rfl
  rw [hs0] at sS
  obtain ⟨sW, sW0, sW1⟩ := limb_split (fun b => E.c (colW i b)) (fun b hb => bitc hL hr0 (colW_lt hi hb))
  rw [wv_c_col] at sW
  have m0 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨0, List.mem_range.2 (by decide),
      List.mem_cons_self ..⟩⟩))))))
  have m1 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨1, List.mem_range.2 (by decide),
      List.mem_cons_self ..⟩⟩))))))
  have e0 := eqG_sound hg m0
  have e1 := eqG_sound hg m1
  rw [ev_n hr, ev_add] at e0 e1
  unfold pairW
  omega

theorem help_copy (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {j : Nat} (hj : j < 16)
    (hj1 : 1 ≤ j) (hR : nv tr t (r + 1) (colR j) = 1) {x y : Nat}
    (hm : E.eqG gHelp (E.n x) (E.c y) ∈ constraints) : nv tr t (r + 1) x = nv tr t r y := by
  have hK := kindStmt tr t pub hL
  have := eqG_sound (ev_gHelp (pub := pub) hK hr hj hj1 hR) (hold hL (by omega) hm)
  rwa [ev_n hr, ev_c] at this

theorem mem_I8 {i l : Nat} (hi : i < 4) (hl : l < 2) :
    E.eqG gHelp (E.n (colI8 i l)) (E.c (colI4 i l)) ∈ constraints :=
  mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨l, List.mem_range.2 hl,
      List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩)))))

theorem mem_I12 {i l : Nat} (hi : i < 4) (hl : l < 2) :
    E.eqG gHelp (E.n (colI12 i l)) (E.c (colI8 i l)) ∈ constraints :=
  mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨l, List.mem_range.2 hl,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩⟩)))))

theorem mem_HinCopy {w l : Nat} (hw : w < 8) (hl : l < 2) :
    E.eqG gHelp (E.n (colHin w l)) (E.c (colHin w l)) ∈ constraints :=
  mem_cHelp (List.mem_append.2 (Or.inr
    (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, List.mem_flatMap.2 ⟨l, List.mem_range.2 hl,
      List.mem_cons_self ..⟩⟩)))

theorem help_W3 (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t) {j i : Nat} (hj : j < 16)
    (hj1 : 1 ≤ j) (hR : nv tr t (r + 1) (colR j) = 1) (hi : i < 3) :
    pairW tr t (r + 1) (colW3 i) = wordAt tr t r (colW (i + 1)) ∧
      nv tr t (r + 1) (colW3 i 0) < 65536 ∧ nv tr t (r + 1) (colW3 i 1) < 65536 := by
  have hK := kindStmt tr t pub hL
  have hr0 : r < tr.height t := by omega
  have hg := ev_gHelp (pub := pub) hK hr hj hj1 hR
  obtain ⟨sW, sW0, sW1⟩ := limb_split (fun b => E.c (colW (i + 1) b))
    (fun b hb => bitc hL hr0 (colW_lt (by omega) hb))
  rw [wv_c_col] at sW
  have m0 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨0, List.mem_range.2 (by decide),
      rfl⟩⟩))))))
  have m1 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨1, List.mem_range.2 (by decide),
      rfl⟩⟩))))))
  have e0 := eqG_sound hg m0
  have e1 := eqG_sound hg m1
  rw [ev_n hr] at e0 e1
  unfold pairW
  omega

/-- The `R0` row copies the chaining value from the previous (state) row. -/
theorem hin_R0 (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t)
    (hR : nv tr t (r + 1) (colR 0) = 1) {w : Nat} (hw : w < 8) :
    pairW tr t (r + 1) (colHin w) = wordAt tr t r (colSt w) ∧
      nv tr t (r + 1) (colHin w 0) < 65536 ∧ nv tr t (r + 1) (colHin w 1) < 65536 := by
  have hr0 : r < tr.height t := by omega
  have hg : ev tr t r pub (E.n (colR 0)) = 1 := by rw [ev_n hr]; exact hR
  obtain ⟨sW, sW0, sW1⟩ := limb_split (fun b => E.c (colSt w b))
    (fun b hb => bitc hL hr0 (colSt_lt hw hb))
  rw [wv_c_col] at sW
  have m0 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inr
    (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, List.mem_flatMap.2 ⟨0, List.mem_range.2 (by decide),
      List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩))))
  have m1 := hold hL hr0 (pub := pub) (mem_cHelp (List.mem_append.2 (Or.inr
    (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, List.mem_flatMap.2 ⟨1, List.mem_range.2 (by decide),
      List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩))))
  have e0 := eqG_sound hg m0
  have e1 := eqG_sound hg m1
  rw [ev_n hr] at e0 e1
  unfold pairW
  omega

/-! ## Digest row -/

theorem colCSt_lt {w l k : Nat} (hw : w < 8) (hl : l < 2) (hk : k < 3) : colCSt w l k < 456 := by
  unfold colCSt colCA colCE; split <;> omega

/-- The `D` row (next row) holds `Hin + state` word-wise mod `2^32`. -/
theorem digest_step (hL : ShaLocal tr t pub) (hr : r + 1 < tr.height t)
    (hD : nv tr t (r + 1) colD = 1) {w : Nat} (hw : w < 8)
    (hH0 : nv tr t r (colHin w 0) < 65536) (hH1 : nv tr t r (colHin w 1) < 65536) :
    wordAt tr t (r + 1) (colSt w) = (pairW tr t r (colHin w) + wordAt tr t r (colSt w)) % 2 ^ 32 := by
  have hr0 : r < tr.height t := by omega
  have hg : ev tr t r pub (E.n colD) = 1 := by rw [ev_n hr]; exact hD
  obtain ⟨sW, sW0, sW1⟩ := limb_split (fun b => E.c (colSt w b))
    (fun b hb => bitc hL hr0 (colSt_lt hw hb))
  rw [wv_c_col] at sW
  obtain ⟨sR, sR0, sR1⟩ := limb_split (fun b => E.n (colSt w b))
    (fun b hb => bitn hL hr (colSt_lt hw hb))
  rw [wv_n_col hr] at sR
  have hH : ev tr t r pub (E.c (colHin w 0)) + 65536 * ev tr t r pub (E.c (colHin w 1)) =
      pairW tr t r (colHin w) := rfl
  have hH0' : ev tr t r pub (E.c (colHin w 0)) < 65536 := hH0
  have hH1' : ev tr t r pub (E.c (colHin w 1)) < 65536 := hH1
  have hc0 := carry_lt hL hr (colCSt w) 0 (fun k hk => colCSt_lt hw (by decide) hk)
  have hc1 := carry_lt hL hr (colCSt w) 1 (fun k hk => colCSt_lt hw (by decide) hk)
  have c0 := hold hL hr0 (pub := pub) (mem_cDigest (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw,
    List.mem_map.2 ⟨0, List.mem_range.2 (by decide), rfl⟩⟩))
  have c1 := hold hL hr0 (pub := pub) (mem_cDigest (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw,
    List.mem_map.2 ⟨1, List.mem_range.2 (by decide), rfl⟩⟩))
  simp only [↓reduceIte, Nat.one_ne_zero] at c0 c1
  have ev0 : ev tr t r pub (E.k 0) = 0 := rfl
  have e0 := addC_sound hg c0 (by sumsimp; omega) (by omega)
  have e1 := addC_sound hg c1 (by sumsimp; omega) (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e0 e1
  exact add2 hH sW sR sR0 sR1 ev0 e0 e1

end ZkFormal.Sha.Sound
