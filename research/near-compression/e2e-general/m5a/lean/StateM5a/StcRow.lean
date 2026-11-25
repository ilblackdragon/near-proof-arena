import StateM5a.StcBytes
import StateM5a.TmplWsx

/-!
# StateM5a.StcRow — B-T3: an active `STC` row's cells, from its constraints and lookups

Row-level facts (any trace, any table index `t`; the row's constraints of `Stc.constraints D` hold,
`act = 1`, and the `SRNG` lookups of `Stc.byteCols` / `hiCols` / `loCols` are bytes):

* `dec3_wordW`: a word built by `Stc.wordW` from byte cells and split parts reads, as chip limbs,
  `wlimbs` of the big-endian value of the bytes (`StcBytes.limbs_word`, exact over BabyBear);
* `msg_word` (both sides): for every word `w < 32` of the padded message,
  `dec3 (wordW …) = wlimbs (wordOf F w)` with `F p` = the row's message byte `p` (the padding
  constants after 139); `blockW_dec`;
* the digest limbs (`di`/`do`) are the limbs of the digest bytes (`ri`/`ro`), the public roots are the
  limbs of the opened `ws` bytes, and the length equations.
-/

namespace StateM5a.StcRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.WsDecode
open StateM5a.Sha512If StateM5a.StcBytes ArenaCore.Bytes

local notation "P" => 2013265921

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-! ## Field arithmetic without wrap -/

theorem ev_add_nw {a b : Expr} (h : ev tr t r pub a + ev tr t r pub b < P) :
    ev tr t r pub (a + b) = ev tr t r pub a + ev tr t r pub b := by
  rw [ev_hadd]; exact Nat.mod_eq_of_lt h

theorem ev_kmul_nw (c : Nat) (e : Expr) (h : c * ev tr t r pub e < P) (hc : c < P) :
    ev tr t r pub (K c * e) = c * ev tr t r pub e := by
  rw [ev_hmul, show K c = Expr.const c from rfl, ev_const, Nat.mod_eq_of_lt hc]; exact Nat.mod_eq_of_lt h

theorem ev_K (c : Nat) (hc : c < P) : ev tr t r pub (K c) = c := by
  rw [show K c = Expr.const c from rfl, ev_const, Nat.mod_eq_of_lt hc]

theorem ev_lin3 (a b d : Expr) (cb cd : Nat) (hcb : cb < P) (hcd : cd < P)
    (h : ev tr t r pub a + cb * ev tr t r pub b + cd * ev tr t r pub d < P) :
    ev tr t r pub (a + K cb * b + K cd * d) = ev tr t r pub a + cb * ev tr t r pub b + cd * ev tr t r pub d := by
  rw [ev_add_nw, ev_add_nw, ev_kmul_nw cb b (by omega) hcb, ev_kmul_nw cd d (by omega) hcd]
  · rw [ev_kmul_nw cb b (by omega) hcb]; omega
  · rw [ev_add_nw, ev_kmul_nw cb b (by omega) hcb, ev_kmul_nw cd d (by omega) hcd]
    · omega
    · rw [ev_kmul_nw cb b (by omega) hcb]; omega

theorem ev_lin4 (a b d e : Expr) (cb cd ce : Nat) (hcb : cb < P) (hcd : cd < P) (hce : ce < P)
    (h : ev tr t r pub a + cb * ev tr t r pub b + cd * ev tr t r pub d + ce * ev tr t r pub e < P) :
    ev tr t r pub (a + K cb * b + K cd * d + K ce * e) =
      ev tr t r pub a + cb * ev tr t r pub b + cd * ev tr t r pub d + ce * ev tr t r pub e := by
  rw [ev_add_nw, ev_lin3 a b d cb cd hcb hcd (by omega), ev_kmul_nw ce e (by omega) hce]
  rw [ev_lin3 a b d cb cd hcb hcd (by omega), ev_kmul_nw ce e (by omega) hce]; omega

/-- From `x − y = 0`: equal values. -/
theorem sub0 {a b : Expr} (h : ev tr t r pub (a - b) = 0) : ev tr t r pub a = ev tr t r pub b := eq_of_sub h

/-! ## The word lemma -/

theorem range8_map {α : Type} (g : Nat → α) :
    (List.range 8).map g = [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] := by simp [List.range_succ]

/-- **A word's chip limbs from byte cells.** -/
theorem dec3_wordW {byte sp : Nat → Expr} (hb : ∀ j, j < 8 → ev tr t r pub (byte j) < 256)
    (hl0 : ev tr t r pub (sp 0) < 32) (hh1 : ev tr t r pub (sp 1) < 256)
    (hl2 : ev tr t r pub (sp 2) < 4) (hh3 : ev tr t r pub (sp 3) < 256)
    (e5 : ev tr t r pub (byte 5) = ev tr t r pub (sp 0) + 32 * ev tr t r pub (sp 1))
    (e2 : ev tr t r pub (byte 2) = ev tr t r pub (sp 2) + 4 * ev tr t r pub (sp 3)) :
    dec3 tr t r pub (Stc.wordW byte sp) =
      wlimbs (beToNat ((List.range 8).map fun j => UInt8.ofNat (ev tr t r pub (byte j)))) := by
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide); have b4 := hb 4 (by decide); have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide); have b7 := hb 7 (by decide)
  have hw := limbs_word (ev tr t r pub (byte 0)) (ev tr t r pub (byte 1)) (ev tr t r pub (byte 2))
    (ev tr t r pub (byte 3)) (ev tr t r pub (byte 4)) (ev tr t r pub (byte 5)) (ev tr t r pub (byte 6))
    (ev tr t r pub (byte 7)) (ev tr t r pub (sp 0)) (ev tr t r pub (sp 1)) (ev tr t r pub (sp 2))
    (ev tr t r pub (sp 3)) b0 b1 b2 b3 b4 b5 b6 b7 hl0 hl2 e5 e2
  rw [range8_map]
  simp only [List.map_cons, List.map_nil] at hw
  rw [hw]
  simp only [dec3, Stc.wordW]
  rw [ev_lin3 _ _ _ 256 65536 (by decide) (by decide) (by omega),
    ev_lin4 _ _ _ _ 8 2048 524288 (by decide) (by decide) (by decide) (by omega),
    ev_lin3 _ _ _ 64 16384 (by decide) (by decide) (by omega)]

/-- A split equation over BabyBear is the integer one (the parts are small). -/
theorem split_int {b s0 s1 : Expr} (k : Nat) (hk : k ≤ 32)
    (h : ev tr t r pub (b - (s0 + K k * s1)) = 0) (h0 : ev tr t r pub s0 < 256) (h1 : ev tr t r pub s1 < 256) :
    ev tr t r pub b = ev tr t r pub s0 + k * ev tr t r pub s1 := by
  rw [sub0 h, ev_add_nw, ev_kmul_nw k s1 (by have := Nat.mul_le_mul_right (ev tr t r pub s1) hk; omega) (by omega)]
  rw [ev_kmul_nw k s1 (by have := Nat.mul_le_mul_right (ev tr t r pub s1) hk; omega) (by omega)]
  have := Nat.mul_le_mul_right (ev tr t r pub s1) hk; omega

/-- A low part from its two lookups. -/
theorem lo_bound {x : Expr} (k : Nat) (hk : k ≤ 8) (h1 : ev tr t r pub x < 256)
    (h2 : ev tr t r pub (K (2 ^ (8 - k)) * x) < 256) : ev tr t r pub x < 2 ^ k := by
  have hp : 2 ^ (8 - k) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
  have hx : 2 ^ (8 - k) * ev tr t r pub x ≤ 2 ^ 8 * 255 := Nat.mul_le_mul hp (by omega)
  rw [ev_kmul_nw _ x (by omega) (by omega)] at h2
  have e : 2 ^ (8 - k) * 2 ^ k = 256 := by rw [← Nat.pow_add, show 8 - k + k = 8 by omega]
  rcases Nat.lt_or_ge (ev tr t r pub x) (2 ^ k) with h | h
  · exact h
  · have := Nat.mul_le_mul_left (2 ^ (8 - k)) h
    omega

theorem mem_hi {s : String} {n w : Nat} (hg : (s, n) ∈ Stc.grps) (hw : w < n) :
    Stc.c s (4 * w + 1) ∈ Stc.hiCols ∧ Stc.c s (4 * w + 3) ∈ Stc.hiCols :=
  ⟨List.mem_flatMap.2 ⟨(s, n), hg, List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, by simp⟩⟩,
   List.mem_flatMap.2 ⟨(s, n), hg, List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, by simp⟩⟩⟩

theorem mem_lo {s : String} {n w : Nat} (hg : (s, n) ∈ Stc.grps) (hw : w < n) :
    (Stc.c s (4 * w), 5) ∈ Stc.loCols ∧ (Stc.c s (4 * w + 2), 2) ∈ Stc.loCols :=
  ⟨List.mem_flatMap.2 ⟨(s, n), hg, List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, by simp⟩⟩,
   List.mem_flatMap.2 ⟨(s, n), hg, List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, by simp⟩⟩⟩

/-- Membership of the six split families (`Stc.splits`). -/
theorem mem_sp1 {w : Nat} (hw : w < 18) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.mI (8 * w + j)) (Stc.spM "si" w)) : e ∈ Stc.splits := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩))))))
theorem mem_sp2 {w : Nat} (hw : w < 18) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.mO (8 * w + j)) (Stc.spM "so" w)) : e ∈ Stc.splits := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩))))))
theorem mem_sp3 {w : Nat} (hw : w < 6) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.c "ri" (8 * w + j)) (fun q => Stc.c "rsi" (4 * w + q))) :
    e ∈ Stc.splits := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩)))))
theorem mem_sp4 {w : Nat} (hw : w < 6) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.c "ro" (8 * w + j)) (fun q => Stc.c "rso" (4 * w + q))) :
    e ∈ Stc.splits := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩))))
theorem mem_sp5 {w : Nat} (hw : w < 6) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.mI (1 + 8 * w + j)) (fun q => Stc.c "wsi" (4 * w + q))) :
    e ∈ Stc.splits := (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩)))
theorem mem_sp6 {w : Nat} (hw : w < 6) {e : Expr}
    (he : e ∈ Stc.splitEqs (fun j => Stc.mO (1 + 8 * w + j)) (fun q => Stc.c "wso" (4 * w + q))) :
    e ∈ Stc.splits := (List.mem_append_right _ (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩))

theorem mem_g3 {D : Nat} {e : Expr} (he : e ∈ Stc.splits) : e ∈ Stc.splits ++ Stc.limbEqs ++ Stc.lenEqs D :=
  List.mem_append_left _ (List.mem_append_left _ he)

theorem mem_le1 {u : Nat} (hu : u < 18) : Stc.c "di" u -
    Stc.w3l (Stc.wordW (fun j => Stc.c "ri" (8 * (u / 3) + j)) (fun q => Stc.c "rsi" (4 * (u / 3) + q))) (u % 3) ∈
      Stc.limbEqs := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))))
theorem mem_le2 {u : Nat} (hu : u < 18) : Stc.c "do" u -
    Stc.w3l (Stc.wordW (fun j => Stc.c "ro" (8 * (u / 3) + j)) (fun q => Stc.c "rso" (4 * (u / 3) + q))) (u % 3) ∈
      Stc.limbEqs := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))))
theorem mem_le3 {u : Nat} (hu : u < 18) : Expr.pub (PUB_WSA + u) -
    Stc.w3l (Stc.wordW (fun j => Stc.mI (1 + 8 * (u / 3) + j)) (fun q => Stc.c "wsi" (4 * (u / 3) + q))) (u % 3) ∈
      Stc.limbEqs := (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩)))
theorem mem_le4 {u : Nat} (hu : u < 18) : Expr.pub (PUB_WSB + u) -
    Stc.w3l (Stc.wordW (fun j => Stc.mO (1 + 8 * (u / 3) + j)) (fun q => Stc.c "wso" (4 * (u / 3) + q))) (u % 3) ∈
      Stc.limbEqs := (List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))
theorem mem_gL {D : Nat} {e : Expr} (he : e ∈ Stc.limbEqs) : e ∈ Stc.splits ++ Stc.limbEqs ++ Stc.lenEqs D :=
  List.mem_append_left _ (List.mem_append_right _ he)
theorem mem_gN {D : Nat} {e : Expr} (he : e ∈ Stc.lenEqs D) : e ∈ Stc.splits ++ Stc.limbEqs ++ Stc.lenEqs D :=
  List.mem_append_right _ he

/-! ## An active `STC` row -/

section Row
variable {D : Nat}
  (hc : ∀ e ∈ (Stc.table D).constraints, ev tr t r pub e = 0)
  (hA : ev tr t r pub (Stc.c "act") = 1)
  (hB : ∀ x ∈ Stc.byteCols, ev tr t r pub x < 256)
  (hHi : ∀ x ∈ Stc.hiCols, ev tr t r pub x < 256)
  (hLo : ∀ p ∈ Stc.loCols, ev tr t r pub p.1 < 256 ∧ ev tr t r pub (K (2 ^ (8 - p.2)) * p.1) < 256)

include hc hA in
theorem gated {e : Expr} (he : e ∈ Stc.splits ++ Stc.limbEqs ++ Stc.lenEqs D) : ev tr t r pub e = 0 := by
  have hm : Stc.c "act" * e ∈ (Stc.table D).constraints :=
    List.mem_cons_of_mem _ (List.mem_map.2 ⟨e, he, rfl⟩)
  exact FieldWsb.wsb_gate hA (hc _ hm)

theorem padByte_lt (p : Nat) : Stc.padByte p < 256 := by
  unfold Stc.padByte; split
  · decide
  · split
    · decide
    · split <;> decide

theorem mem_b {p : Nat} (h : p < 139) : Stc.c "b" p ∈ Stc.byteCols :=
  (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨p, List.mem_range.2 h, rfl⟩)))))))
theorem mem_ot : Stc.c "ot" ∈ Stc.byteCols := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))))))
theorem mem_ow {j : Nat} (h : j < 48) : Stc.c "ow" j ∈ Stc.byteCols := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩))))))
theorem mem_or {j : Nat} (h : j < 42) : Stc.c "or" j ∈ Stc.byteCols := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)))))
theorem mem_ri {j : Nat} (h : j < 48) : Stc.c "ri" j ∈ Stc.byteCols := (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩))))
theorem mem_ro {j : Nat} (h : j < 48) : Stc.c "ro" j ∈ Stc.byteCols := (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)))
theorem mem_g {j : Nat} (h : j < 3) : Stc.c "g" j ∈ Stc.byteCols := (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩))

include hB in
theorem bI (p : Nat) : ev tr t r pub (Stc.mI p) < 256 := by
  unfold Stc.mI; split
  · rename_i h; exact hB _ (mem_b h)
  · rw [ev_K _ (by have := padByte_lt p; omega)]; exact padByte_lt p

include hB in
theorem bO (p : Nat) : ev tr t r pub (Stc.mO p) < 256 := by
  unfold Stc.mO
  split
  · exact hB _ mem_ot
  · split
    · rename_i h0 h; exact hB _ (mem_ow (by omega))
    · split
      · rename_i h0 h1 h; exact hB _ (mem_b (by omega))
      · split
        · rename_i h0 h1 h2 h; exact hB _ (mem_or (by unfold Stc.NB at h; omega))
        · rw [ev_K _ (by have := padByte_lt p; omega)]; exact padByte_lt p

include hHi hLo in
theorem parts {s : String} {n w : Nat} (hg : (s, n) ∈ Stc.grps) (hw : w < n) :
    ev tr t r pub (Stc.c s (4 * w)) < 32 ∧ ev tr t r pub (Stc.c s (4 * w + 1)) < 256 ∧
      ev tr t r pub (Stc.c s (4 * w + 2)) < 4 ∧ ev tr t r pub (Stc.c s (4 * w + 3)) < 256 := by
  obtain ⟨l0, l2⟩ := mem_lo hg hw
  obtain ⟨h1, h3⟩ := mem_hi hg hw
  have a := hLo _ l0; have b := hLo _ l2
  exact ⟨lo_bound 5 (by decide) a.1 a.2, hHi _ h1, lo_bound 2 (by decide) b.1 b.2, hHi _ h3⟩

/-- **A word from split equations** (cells). -/
theorem word_split {byte sp : Nat → Expr} (hb : ∀ j, j < 8 → ev tr t r pub (byte j) < 256)
    (p0 : ev tr t r pub (sp 0) < 32) (p1 : ev tr t r pub (sp 1) < 256) (p2 : ev tr t r pub (sp 2) < 4)
    (p3 : ev tr t r pub (sp 3) < 256) (hs : ∀ e ∈ Stc.splitEqs byte sp, ev tr t r pub e = 0) :
    dec3 tr t r pub (Stc.wordW byte sp) =
      wlimbs (beToNat ((List.range 8).map fun j => UInt8.ofNat (ev tr t r pub (byte j)))) :=
  dec3_wordW hb p0 p1 p2 p3
    (split_int 32 (by decide) (hs _ (by simp [Stc.splitEqs])) (by omega) p1)
    (split_int 4 (by decide) (hs _ (by simp [Stc.splitEqs])) (by omega) p3)

/-- A padding word (all constants). -/
theorem word_pad {m : Nat → Expr} (s : String) {w : Nat} (hw : 18 ≤ w)
    (hm : ∀ j, j < 8 → m (8 * w + j) = K (Stc.padByte (8 * w + j))) :
    dec3 tr t r pub (Stc.wordW (fun j => m (8 * w + j)) (Stc.spM s w)) =
      wlimbs (beToNat ((List.range 8).map fun j => UInt8.ofNat (ev tr t r pub (m (8 * w + j))))) := by
  have hsp : ∀ q, Stc.spM s w q = K (Stc.padSplit w q) := by
    intro q; unfold Stc.spM Stc.NWD; exact if_neg (by omega)
  have hpb : ∀ j, j < 8 → ev tr t r pub (m (8 * w + j)) = Stc.padByte (8 * w + j) := by
    intro j hj; rw [hm j hj, ev_K _ (by have := padByte_lt (8 * w + j); omega)]
  have hpl := fun q => padByte_lt q
  have hs : ∀ q, ev tr t r pub (Stc.spM s w q) = Stc.padSplit w q := by
    intro q; rw [hsp, ev_K]
    unfold Stc.padSplit
    have := hpl (8 * w + 5); have := hpl (8 * w + 2)
    split
    · omega
    · split
      · omega
      · split <;> omega
  refine dec3_wordW (fun j hj => by rw [hpb j hj]; exact padByte_lt _) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hs]; unfold Stc.padSplit; simp; omega
  · rw [hs]; unfold Stc.padSplit; simp; have := hpl (8 * w + 5); omega
  · rw [hs]; unfold Stc.padSplit; simp; omega
  · rw [hs]; unfold Stc.padSplit; simp; have := hpl (8 * w + 2); omega
  · rw [hpb 5 (by decide), hs, hs]; unfold Stc.padSplit; simp; omega
  · rw [hpb 2 (by decide), hs, hs]; unfold Stc.padSplit; simp; omega

theorem g_si : ("si", 18) ∈ Stc.grps := by simp [Stc.grps, Stc.NWD]
theorem g_so : ("so", 18) ∈ Stc.grps := by simp [Stc.grps, Stc.NWD]
theorem g_rsi : ("rsi", 6) ∈ Stc.grps := by simp [Stc.grps]
theorem g_rso : ("rso", 6) ∈ Stc.grps := by simp [Stc.grps]
theorem g_wsi : ("wsi", 6) ∈ Stc.grps := by simp [Stc.grps]
theorem g_wso : ("wso", 6) ∈ Stc.grps := by simp [Stc.grps]

theorem spM_lt {s : String} {w : Nat} (hw : w < 18) (q : Nat) : Stc.spM s w q = Stc.c s (4 * w + q) := by
  unfold Stc.spM Stc.NWD; exact if_pos hw

/-- The row's message byte functions. -/
def FI (tr : Trace Fp) (t r : Nat) (pub : List Fp) (p : Nat) : Nat := ev tr t r pub (Stc.mI p)
def FO (tr : Trace Fp) (t r : Nat) (pub : List Fp) (p : Nat) : Nat := ev tr t r pub (Stc.mO p)

theorem mI_pad {p : Nat} (h : 139 ≤ p) : Stc.mI p = K (Stc.padByte p) := by
  unfold Stc.mI Stc.NB; exact if_neg (by omega)
theorem mO_pad {p : Nat} (h : 139 ≤ p) : Stc.mO p = K (Stc.padByte p) := by
  unfold Stc.mO Stc.NB
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

include hc hA hB hHi hLo in
/-- **Message word `w` (input side).** -/
theorem wordI {w : Nat} (hw : w < 32) :
    dec3 tr t r pub (Stc.wordW (fun j => Stc.mI (8 * w + j)) (Stc.spM "si" w)) = wlimbs (wordOf (FI tr t r pub) w) := by
  by_cases h18 : w < 18
  · obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_si h18
    exact word_split (fun j _ => bI hB _) (by rw [spM_lt h18]; exact p0) (by rw [spM_lt h18]; exact p1)
      (by rw [spM_lt h18]; exact p2) (by rw [spM_lt h18]; exact p3)
      (fun e he => gated hc hA (mem_g3 (mem_sp1 h18 he)))
  · exact word_pad "si" (by omega) (fun j _ => mI_pad (by omega))

include hc hA hB hHi hLo in
/-- **Message word `w` (output side).** -/
theorem wordO {w : Nat} (hw : w < 32) :
    dec3 tr t r pub (Stc.wordW (fun j => Stc.mO (8 * w + j)) (Stc.spM "so" w)) = wlimbs (wordOf (FO tr t r pub) w) := by
  by_cases h18 : w < 18
  · obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_so h18
    exact word_split (fun j _ => bO hB _) (by rw [spM_lt h18]; exact p0) (by rw [spM_lt h18]; exact p1)
      (by rw [spM_lt h18]; exact p2) (by rw [spM_lt h18]; exact p3)
      (fun e he => gated hc hA (mem_g3 (mem_sp2 h18 he)))
  · exact word_pad "so" (by omega) (fun j _ => mO_pad (by omega))

include hc hA hB hHi hLo in
theorem blockI {k : Nat} (hk : k ≤ 1) :
    (Stc.blockW Stc.mI "si" k).map (dec3 tr t r pub) = (wordsF (FI tr t r pub) (16 * k) 16).map wlimbs := by
  simp only [Stc.blockW, wordsF, List.map_map]
  apply List.map_congr_left; intro i hi
  have := List.mem_range.1 hi
  exact wordI hc hA hB hHi hLo (by omega)

include hc hA hB hHi hLo in
theorem blockO {k : Nat} (hk : k ≤ 1) :
    (Stc.blockW Stc.mO "so" k).map (dec3 tr t r pub) = (wordsF (FO tr t r pub) (16 * k) 16).map wlimbs := by
  simp only [Stc.blockW, wordsF, List.map_map]
  apply List.map_congr_left; intro i hi
  have := List.mem_range.1 hi
  exact wordO hc hA hB hHi hLo (by omega)

/-- The value of limb `l` of a triple is entry `l` of `dec3`. -/
theorem ev_w3l (x : W3) : ∀ l, l < 3 → ev tr t r pub (Stc.w3l x l) = (dec3 tr t r pub x).getD l 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- A digest column group whose limb `u` is limb `u % 3` of word `u / 3`'s triple `X (u / 3)`, and
`dec3 (X k) = wlimbs (wd k)`: the group's 6 triples are `wlimbs` of the words. -/
theorem digW_of {f : Nat → Expr} {X : Nat → W3} {wd : Nat → Nat}
    (hl : ∀ u, u < 18 → ev tr t r pub (f u) = ev tr t r pub (Stc.w3l (X (u / 3)) (u % 3)))
    (hx : ∀ k, k < 6 → dec3 tr t r pub (X k) = wlimbs (wd k)) :
    (digW f).map (dec3 tr t r pub) = ((List.range 6).map wd).map wlimbs := by
  simp only [digW, List.map_map]
  apply List.map_congr_left; intro k hk
  have hk := List.mem_range.1 hk
  simp only [Function.comp, dec3]
  rw [hl _ (by omega), hl _ (by omega), hl _ (by omega),
    show (3 * k) / 3 = k by omega, show (3 * k + 1) / 3 = k by omega, show (3 * k + 2) / 3 = k by omega,
    show (3 * k) % 3 = 0 by omega, show (3 * k + 1) % 3 = 1 by omega, show (3 * k + 2) % 3 = 2 by omega,
    ev_w3l _ 0 (by decide), ev_w3l _ 1 (by decide), ev_w3l _ 2 (by decide), hx k hk]
  simp [wlimbs]

/-- The row's digest byte functions. -/
def RI (tr : Trace Fp) (t r : Nat) (pub : List Fp) (j : Nat) : Nat := ev tr t r pub (Stc.c "ri" j)
def RO (tr : Trace Fp) (t r : Nat) (pub : List Fp) (j : Nat) : Nat := ev tr t r pub (Stc.c "ro" j)

include hc hA hB hHi hLo in
/-- **The input digest limbs are its bytes' limbs.** -/
theorem digI : (digW fun u => Stc.c "di" u).map (dec3 tr t r pub) = (wordsF (RI tr t r pub) 0 6).map wlimbs := by
  rw [digW_of (X := fun k => Stc.wordW (fun j => Stc.c "ri" (8 * k + j)) (fun q => Stc.c "rsi" (4 * k + q)))
    (wd := wordOf (RI tr t r pub)) (fun u hu => sub0 (gated hc hA (mem_gL (mem_le1 hu))))]
  · simp [wordsF]
  · intro k hk
    obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_rsi hk
    exact word_split (fun j hj => hB _ (mem_ri (by omega))) p0 p1 p2 p3
      (fun e he => gated hc hA (mem_g3 (mem_sp3 hk he)))

include hc hA hB hHi hLo in
theorem digO : (digW fun u => Stc.c "do" u).map (dec3 tr t r pub) = (wordsF (RO tr t r pub) 0 6).map wlimbs := by
  rw [digW_of (X := fun k => Stc.wordW (fun j => Stc.c "ro" (8 * k + j)) (fun q => Stc.c "rso" (4 * k + q)))
    (wd := wordOf (RO tr t r pub)) (fun u hu => sub0 (gated hc hA (mem_gL (mem_le2 hu))))]
  · simp [wordsF]
  · intro k hk
    obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_rso hk
    exact word_split (fun j hj => hB _ (mem_ro (by omega))) p0 p1 p2 p3
      (fun e he => gated hc hA (mem_g3 (mem_sp4 hk he)))

/-- `pubDig` is the row digest of the public-value columns. -/
theorem pubDig_row (base : Nat) :
    TmplWsx.pubDig pub base = rowDig tr t r pub (fun j => Expr.pub (base + j)) := rfl

include hc hA hB hHi hLo in
/-- **The opened input `ws` is the public `R_in`** (as words). -/
theorem wsI : (TmplWsx.pubDig pub PUB_WSA).1 = wordsF (fun p => FI tr t r pub (1 + p)) 0 6 := by
  have h := digW_of (tr := tr) (t := t) (r := r) (pub := pub) (f := fun u => Expr.pub (PUB_WSA + u))
    (X := fun k => Stc.wordW (fun j => Stc.mI (1 + 8 * k + j)) (fun q => Stc.c "wsi" (4 * k + q)))
    (wd := wordOf (fun p => FI tr t r pub (1 + p))) (fun u hu => sub0 (gated hc hA (mem_gL (mem_le3 hu))))
    (fun k hk => by
      obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_wsi hk
      rw [word_split (fun j _ => bI hB _) p0 p1 p2 p3 (fun e he => gated hc hA (mem_g3 (mem_sp5 hk he)))]
      simp only [wordOf, chunk, FI, Nat.add_assoc])
  have hw : W64 ((List.range 6).map (wordOf (fun p => FI tr t r pub (1 + p)))) := by
    intro w hw; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw; exact wordOf_lt _ _
  rw [pubDig_row, rowDig_of (d := ⟨_, by simp, hw⟩) h]
  simp [wordsF]

include hc hA hB hHi hLo in
theorem wsO : (TmplWsx.pubDig pub PUB_WSB).1 = wordsF (fun p => FO tr t r pub (1 + p)) 0 6 := by
  have h := digW_of (tr := tr) (t := t) (r := r) (pub := pub) (f := fun u => Expr.pub (PUB_WSB + u))
    (X := fun k => Stc.wordW (fun j => Stc.mO (1 + 8 * k + j)) (fun q => Stc.c "wso" (4 * k + q)))
    (wd := wordOf (fun p => FO tr t r pub (1 + p))) (fun u hu => sub0 (gated hc hA (mem_gL (mem_le4 hu))))
    (fun k hk => by
      obtain ⟨p0, p1, p2, p3⟩ := parts hHi hLo g_wso hk
      rw [word_split (fun j _ => bO hB _) p0 p1 p2 p3 (fun e he => gated hc hA (mem_g3 (mem_sp6 hk he)))]
      simp only [wordOf, chunk, FO, Nat.add_assoc])
  have hw : W64 ((List.range 6).map (wordOf (fun p => FO tr t r pub (1 + p)))) := by
    intro w hw; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw; exact wordOf_lt _ _
  rw [pubDig_row, rowDig_of (d := ⟨_, by simp, hw⟩) h]
  simp [wordsF]

include hc hA hB in
/-- **The opened `wsLen`**: bytes 49–51 are the public count, bytes 52–56 zero, and `wsLen ≤ 2^D`. -/
theorem lenI (hD : D ≤ 20) :
    WsLen.wsLen pub = FI tr t r pub 49 + 256 * FI tr t r pub 50 + 65536 * FI tr t r pub 51 ∧
      (∀ k, k < 5 → FI tr t r pub (52 + k) = 0) ∧ WsLen.wsLen pub ≤ 2 ^ D := by
  have hb : ∀ p, p < 139 → FI tr t r pub p = ev tr t r pub (Stc.c "b" p) := by
    intro p hp; unfold FI Stc.mI Stc.NB; rw [if_pos hp]
  have e1 : ev tr t r pub (Stc.c "b" 49 + K 256 * Stc.c "b" 50 + K 65536 * Stc.c "b" 51 - .pub PUB_WSLEN) = 0 :=
    gated hc hA (mem_gN (by simp [Stc.lenEqs]))
  have e2 : ev tr t r pub (Stc.c "g" 0 + K 256 * Stc.c "g" 1 + K 65536 * Stc.c "g" 2 -
      (K (2 ^ D) - .pub PUB_WSLEN)) = 0 := gated hc hA (mem_gN (by simp [Stc.lenEqs]))
  have b49 := hB _ (mem_b (p := 49) (by decide)); have b50 := hB _ (mem_b (p := 50) (by decide))
  have b51 := hB _ (mem_b (p := 51) (by decide))
  have g0 := hB _ (mem_g (j := 0) (by decide)); have g1 := hB _ (mem_g (j := 1) (by decide))
  have g2 := hB _ (mem_g (j := 2) (by decide))
  have hW : WsLen.wsLen pub = ev tr t r pub (Stc.c "b" 49) + 256 * ev tr t r pub (Stc.c "b" 50) +
      65536 * ev tr t r pub (Stc.c "b" 51) := by
    rw [← ev_lin3 _ _ _ 256 65536 (by decide) (by decide) (by omega), sub0 e1]; rfl
  refine ⟨by rw [hb 49 (by decide), hb 50 (by decide), hb 51 (by decide)]; exact hW, ?_, ?_⟩
  · intro k hk
    rw [hb _ (by omega)]
    exact gated hc hA (mem_gN (by simp only [Stc.lenEqs, List.mem_append, List.mem_map, List.mem_range]; exact Or.inl ⟨k, hk, rfl⟩))
  · have hg := sub0 e2
    rw [ev_lin3 _ _ _ 256 65536 (by decide) (by decide) (by omega), ev_sub,
      ev_K _ (by have : 2 ^ D ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hD; omega)] at hg
    have h20 : 2 ^ D ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hD
    have hWlt : WsLen.wsLen pub < 2 ^ 24 := by rw [hW]; omega
    have hWP := WsLen.wsLen_lt (pub := pub)
    have e3 : ev tr t r pub (Expr.pub PUB_WSLEN) = WsLen.wsLen pub := rfl
    rw [e3] at hg
    generalize WsLen.wsLen pub = W at hg hWlt hWP ⊢
    generalize 2 ^ D = Z at hg h20 ⊢
    generalize ev tr t r pub (Stc.c "g" 0) = x0 at hg g0
    generalize ev tr t r pub (Stc.c "g" 1) = x1 at hg g1
    generalize ev tr t r pub (Stc.c "g" 2) = x2 at hg g2
    rcases Nat.lt_or_ge Z W with hlt | hle
    · have m1 : (P - W) % P = P - W := Nat.mod_eq_of_lt (by omega)
      have m2 : (Z + (P - W)) % P = Z + (P - W) := Nat.mod_eq_of_lt (by omega)
      rw [m1, m2] at hg
      omega
    · exact hle

end Row

end StateM5a.StcRow
