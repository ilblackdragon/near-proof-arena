import ZkFormal.Sha.Complete.Rows

/-!
# ZkFormal.Sha.Complete.Cells — cell values of the honest rows, by column group
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout

@[simp] theorem henv_cur (msgs : List Msg) (t r : Nat) (pub : List Fp) (c : Nat) :
    (henv msgs t r pub).cur c = rowCell (rowAt msgs r) c := rfl
@[simp] theorem henv_nxt (msgs : List Msg) (t r : Nat) (pub : List Fp) (c : Nat) :
    (henv msgs t r pub).nxt c = rowCell (rowAt msgs ((r + 1) % (honestTrace msgs).height t)) c := rfl

@[simp] theorem rowCell_start (id c : Nat) : rowCell (.start id) c = startCell id c := rfl
@[simp] theorem rowCell_round (j : Nat) (B : Blk) (c : Nat) : rowCell (.round j B) c = roundCell j B c := rfl
@[simp] theorem rowCell_digest (B : Blk) (c : Nat) : rowCell (.digest B) c = digestCell B c := rfl
@[simp] theorem rowCell_pad (c : Nat) : rowCell .pad c = 0 := rfl

/-! ## Start rows -/

section
variable (id : Nat)

theorem sc_A (i b : Nat) (hi : i < 4) (hb : b < 32) :
    startCell id (colA i b) = bit (ivW (3 - i)) b := by
  unfold startCell colA
  rw [if_pos (by omega), if_pos (by omega)]
  congr 2 <;> omega

theorem sc_E (i b : Nat) (hi : i < 4) (hb : b < 32) :
    startCell id (colE i b) = bit (ivW (7 - i)) b := by
  unfold startCell colE
  rw [if_pos (by omega), if_neg (by omega)]
  congr 2 <;> omega

theorem sc_S : startCell id colS = 1 := by unfold startCell; simp [colS]
theorem sc_Id : startCell id colId = id := by unfold startCell; simp [colId, colS]

theorem sc_other (c : Nat) (h1 : 256 ≤ c) (h2 : c ≠ colS) (h3 : c ≠ colId) : startCell id c = 0 := by
  unfold startCell
  rw [if_neg (by omega), if_neg h2, if_neg h3]

theorem sc_St (w b : Nat) (hw : w < 8) (hb : b < 32) : startCell id (colSt w b) = bit (ivW w) b := by
  unfold colSt
  split
  · rw [sc_A id _ _ (by omega) hb]; congr 2; omega
  · rw [sc_E id _ _ (by omega) hb]; congr 2; omega
end

/-! ## Round rows -/

section
variable (j : Nat) (B : Blk)

theorem rc_A (i b : Nat) (hi : i < 4) (hb : b < 32) :
    roundCell j B (colA i b) = bit (B.A (4 * j + 4 + i)) b := by
  unfold roundCell colA
  rw [if_pos (by omega)]
  congr 2 <;> omega

theorem rc_E (i b : Nat) (hi : i < 4) (hb : b < 32) :
    roundCell j B (colE i b) = bit (B.Ee (4 * j + 4 + i)) b := by
  unfold roundCell colE
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2 <;> omega

theorem rc_W (i b : Nat) (hi : i < 4) (hb : b < 32) :
    roundCell j B (colW i b) = bit (B.W (4 * j + i)) b := by
  unfold roundCell colW
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 2 <;> omega

theorem rc_CA (i l k : Nat) (hi : i < 4) (hl : l < 2) (hk : k < 3) :
    roundCell j B (colCA i l k) = bit (carry (B.termsA (4 * j + i)) l) k := by
  unfold roundCell colCA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [show (384 + 6 * i + 3 * l + k - 384) / 6 = i by omega,
    show (384 + 6 * i + 3 * l + k - 384) % 6 / 3 = l by omega,
    show (384 + 6 * i + 3 * l + k - 384) % 3 = k by omega]

theorem rc_CE (i l k : Nat) (hi : i < 4) (hl : l < 2) (hk : k < 3) :
    roundCell j B (colCE i l k) = bit (carry (B.termsE (4 * j + i)) l) k := by
  unfold roundCell colCE
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [show (408 + 6 * i + 3 * l + k - 408) / 6 = i by omega,
    show (408 + 6 * i + 3 * l + k - 408) % 6 / 3 = l by omega,
    show (408 + 6 * i + 3 * l + k - 408) % 3 = k by omega]

theorem rc_CW (i l k : Nat) (hi : i < 4) (hl : l < 2) (hk : k < 3) :
    roundCell j B (colCW i l k) = if 4 ≤ j then bit (B.schedCarry (4 * j + i) l) k else 0 := by
  unfold roundCell colCW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  dsimp only
  rw [show (432 + 6 * i + 3 * l + k - 432) / 6 = i by omega,
    show (432 + 6 * i + 3 * l + k - 432) % 6 / 3 = l by omega,
    show (432 + 6 * i + 3 * l + k - 432) % 3 = k by omega]

theorem rc_help (d i l : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 3) (hi : i < 4) (hl : l < 2) :
    roundCell j B (456 + 8 * (d - 1) + 2 * i + l) = if d ≤ j then B.help (4 * (j - d) + i) l else 0 := by
  unfold roundCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [show (456 + 8 * (d - 1) + 2 * i + l - 456) / 8 + 1 = d by omega,
    show (456 + 8 * (d - 1) + 2 * i + l - 456) % 8 / 2 = i by omega,
    show (456 + 8 * (d - 1) + 2 * i + l - 456) % 2 = l by omega]

theorem rc_I4 (i l : Nat) (hi : i < 4) (hl : l < 2) :
    roundCell j B (colI4 i l) = if 1 ≤ j then B.help (4 * (j - 1) + i) l else 0 := by
  have := rc_help j B 1 i l (by decide) (by decide) hi hl
  unfold colI4; simpa using this

theorem rc_I8 (i l : Nat) (hi : i < 4) (hl : l < 2) :
    roundCell j B (colI8 i l) = if 2 ≤ j then B.help (4 * (j - 2) + i) l else 0 := by
  have := rc_help j B 2 i l (by decide) (by decide) hi hl
  unfold colI8; simpa using this

theorem rc_I12 (i l : Nat) (hi : i < 4) (hl : l < 2) :
    roundCell j B (colI12 i l) = if 3 ≤ j then B.help (4 * (j - 3) + i) l else 0 := by
  have := rc_help j B 3 i l (by decide) (by decide) hi hl
  unfold colI12; simpa using this

theorem rc_W3 (i l : Nat) (hi : i < 3) (hl : l < 2) :
    roundCell j B (colW3 i l) = if 1 ≤ j then limbN (B.W (4 * (j - 1) + i + 1)) l else 0 := by
  unfold roundCell colW3
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [show (480 + 2 * i + l - 480) / 2 = i by omega, show (480 + 2 * i + l - 480) % 2 = l by omega]

theorem rc_Hin (w l : Nat) (hw : w < 8) (hl : l < 2) :
    roundCell j B (colHin w l) = limbN (B.hin.getD w 0) l := by
  unfold roundCell colHin
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (486 + 2 * w + l - 486) / 2 = w by omega, show (486 + 2 * w + l - 486) % 2 = l by omega]

theorem rc_R (j' : Nat) (hj : j' < 16) : roundCell j B (colR j') = if j' = j then 1 else 0 := by
  unfold roundCell colR
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show 502 + j' - 502 = j' by omega]

theorem rc_D : roundCell j B colD = 0 := by unfold roundCell colD; simp
theorem rc_S : roundCell j B colS = 0 := by unfold roundCell colS; simp

theorem rc_F (q : Nat) (hq : q < 16) :
    roundCell j B (colF q) = if j < 4 && B.isData (16 * j + q) then 1 else 0 := by
  unfold roundCell colF
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  rw [show 520 + q - 520 = q by omega]

theorem rc_Fprev : roundCell j B colFprev =
    (if j = 0 then 1 else if j < 4 && B.isData (16 * j - 1) then 1 else 0) := by
  unfold roundCell; simp [colFprev]
theorem rc_Nd : roundCell j B colNd = B.ndRow j := by unfold roundCell; simp [colNd, colFprev]
theorem rc_Id : roundCell j B colId = B.id := by unfold roundCell; simp [colNd, colFprev, colId]
theorem rc_Last : roundCell j B colLast = (if B.last then 1 else 0) := by
  unfold roundCell; simp [colNd, colFprev, colId, colLast]
theorem rc_P80 : roundCell j B colP80 = (if B.p80 then 1 else 0) := by
  unfold roundCell; simp [colNd, colFprev, colId, colLast, colP80]
theorem rc_Seen : roundCell j B colSeen = (if B.seen then 1 else 0) := by
  unfold roundCell; simp [colNd, colFprev, colId, colLast, colP80, colSeen]
theorem rc_Pn : roundCell j B colPn = (if B.p80 && !B.last then 1 else 0) := by
  unfold roundCell; simp [colNd, colFprev, colId, colLast, colP80, colSeen, colPn]
theorem rc_Dmult : roundCell j B colDmult = 0 := by
  unfold roundCell; simp [colNd, colFprev, colId, colLast, colP80, colSeen, colPn, colDmult]

theorem rc_St (j : Nat) (B : Blk) (w b : Nat) (hw : w < 8) (hb : b < 32) :
    roundCell j B (colSt w b) =
      bit (if w < 4 then B.A (4 * j + 7 - w) else B.Ee (4 * j + 11 - w)) b := by
  unfold colSt
  split
  · rw [rc_A j B _ _ (by omega) hb]; congr 2; omega
  · rw [rc_E j B _ _ (by omega) hb]; congr 2; omega
end

/-! ## Digest rows -/

section
variable (B : Blk)

theorem dc_A (i b : Nat) (hi : i < 4) (hb : b < 32) :
    digestCell B (colA i b) = bit (B.hout (3 - i)) b := by
  unfold digestCell colA
  rw [if_pos (by omega)]
  congr 2 <;> omega

theorem dc_E (i b : Nat) (hi : i < 4) (hb : b < 32) :
    digestCell B (colE i b) = bit (B.hout (7 - i)) b := by
  unfold digestCell colE
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2 <;> omega

theorem dc_St (w b : Nat) (hw : w < 8) (hb : b < 32) : digestCell B (colSt w b) = bit (B.hout w) b := by
  unfold colSt
  split
  · rw [dc_A B _ _ (by omega) hb]; congr 2; omega
  · rw [dc_E B _ _ (by omega) hb]; congr 2; omega

theorem dc_CA (i l k : Nat) (hi : i < 4) (hl : l < 2) (hk : k < 3) :
    digestCell B (colCA i l k) = bit (carry [B.hin.getD (3 - i) 0, B.fin (3 - i)] l) k := by
  unfold digestCell colCA
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [decide_eq_false (by omega : ¬ 408 ≤ 384 + 6 * i + 3 * l + k)]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (384 + 6 * i + 3 * l + k - 384) / 6 = i by omega,
    show (384 + 6 * i + 3 * l + k - 384) % 6 / 3 = l by omega,
    show (384 + 6 * i + 3 * l + k - 384) % 3 = k by omega]

theorem dc_CE (i l k : Nat) (hi : i < 4) (hl : l < 2) (hk : k < 3) :
    digestCell B (colCE i l k) = bit (carry [B.hin.getD (7 - i) 0, B.fin (7 - i)] l) k := by
  unfold digestCell colCE
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  dsimp only
  rw [decide_eq_true (by omega : 408 ≤ 408 + 6 * i + 3 * l + k)]
  simp only [ite_true]
  rw [show (408 + 6 * i + 3 * l + k - 408) / 6 = i by omega,
    show (408 + 6 * i + 3 * l + k - 408) % 6 / 3 = l by omega,
    show (408 + 6 * i + 3 * l + k - 408) % 3 = k by omega]

theorem dc_CSt (w l k : Nat) (hw : w < 8) (hl : l < 2) (hk : k < 3) :
    digestCell B (colCSt w l k) = bit (carry [B.hin.getD w 0, B.fin w] l) k := by
  unfold colCSt
  split
  · rw [dc_CA B _ _ _ (by omega) hl hk, show 3 - (3 - w) = w by omega]
  · rw [dc_CE B _ _ _ (by omega) hl hk, show 7 - (7 - w) = w by omega]

theorem dc_mid (c : Nat) (h1 : 256 ≤ c) (h2 : c < 384 ∨ (432 ≤ c ∧ c < 518)) : digestCell B c = 0 := by
  unfold digestCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [colD, colNd, colId, colLast, colP80, colSeen, colPn, colDmult]
  have a1 : c ≠ 518 := by omega
  have a2 : c ≠ 537 := by omega
  have a3 : c ≠ 538 := by omega
  have a4 : c ≠ 539 := by omega
  have a5 : c ≠ 540 := by omega
  have a6 : c ≠ 541 := by omega
  have a7 : c ≠ 542 := by omega
  have a8 : c ≠ 543 := by omega
  simp [a1, a2, a3, a4, a5, a6, a7, a8]

theorem dc_W (i b : Nat) (hi : i < 4) (hb : b < 32) : digestCell B (colW i b) = 0 :=
  dc_mid B _ (by unfold colW; omega) (by unfold colW; omega)
theorem dc_R (j : Nat) (hj : j < 16) : digestCell B (colR j) = 0 :=
  dc_mid B _ (by unfold colR; omega) (by unfold colR; omega)
theorem dc_D : digestCell B colD = 1 := by unfold digestCell; simp [colD]
theorem dc_after (c : Nat) (h1 : 519 ≤ c) (h2 : c < 537) : digestCell B c = 0 := by
  unfold digestCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  repeat (rw [if_neg (by simp only [colD, colNd, colId, colLast, colP80, colSeen, colPn, colDmult]; omega)])
theorem dc_S : digestCell B colS = 0 := dc_after B _ (by decide) (by decide)
theorem dc_F (q : Nat) (hq : q < 16) : digestCell B (colF q) = 0 :=
  dc_after B _ (by unfold colF; omega) (by unfold colF; omega)
theorem dc_Fprev : digestCell B colFprev = 0 := dc_after B _ (by decide) (by decide)
theorem dc_Nd : digestCell B colNd = B.ndRow 4 := by unfold digestCell; simp [colD, colNd]
theorem dc_Id : digestCell B colId = B.id := by unfold digestCell; simp [colD, colNd, colId]
theorem dc_Last : digestCell B colLast = (if B.last then 1 else 0) := by
  unfold digestCell; simp [colD, colNd, colId, colLast]
theorem dc_P80 : digestCell B colP80 = (if B.p80 then 1 else 0) := by
  unfold digestCell; simp [colD, colNd, colId, colLast, colP80]
theorem dc_Seen : digestCell B colSeen = (if B.seen then 1 else 0) := by
  unfold digestCell; simp [colD, colNd, colId, colLast, colP80, colSeen]
theorem dc_Pn : digestCell B colPn = (if B.p80 && !B.last then 1 else 0) := by
  unfold digestCell; simp [colD, colNd, colId, colLast, colP80, colSeen, colPn]
theorem dc_Dmult : digestCell B colDmult = (if B.last && B.dmult then 1 else 0) := by
  unfold digestCell; simp [colD, colNd, colId, colLast, colP80, colSeen, colPn, colDmult]
end

/-! ## Boolean columns -/

theorem mem_boolCols (c : Nat) (h : c ∈ boolCols) :
    c < 456 ∨ (502 ≤ c ∧ c < 536) ∨ c = 536 ∨ c = 539 ∨ c = 540 ∨ c = 541 := by
  simp only [boolCols, List.mem_append, List.mem_range, List.mem_range'_1, List.mem_cons,
    List.mem_nil_iff, or_false, colFprev, colLast, colP80, colSeen] at h
  omega

theorem ite_le {p : Prop} [Decidable p] {a b n : Nat} (ha : p → a ≤ n) (hb : ¬p → b ≤ n) :
    (if p then a else b) ≤ n := by
  by_cases h : p
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

set_option maxRecDepth 8000 in
theorem rowCell_bool (row : Row) (c : Nat)
    (hc : c < 456 ∨ (502 ≤ c ∧ c < 536) ∨ c = 536 ∨ c = 539 ∨ c = 540 ∨ c = 541) :
    rowCell row c ≤ 1 := by
  have hb : ∀ x k, bit x k ≤ 1 := fun x k => Nat.le_of_lt_succ (bit_lt x k)
  cases row with
  | start id =>
    simp only [rowCell_start, startCell, colS, colId]
    repeat' (refine ite_le (fun _ => ?_) (fun _ => ?_))
    all_goals first | omega | exact hb _ _
  | round j B =>
    simp only [rowCell_round, roundCell, colFprev, colNd, colId, colLast, colP80, colSeen, colPn]
    repeat' (refine ite_le (fun _ => ?_) (fun _ => ?_))
    all_goals first | omega | exact hb _ _
  | digest B =>
    simp only [rowCell_digest, digestCell, colD, colNd, colId, colLast, colP80, colSeen, colPn,
      colDmult]
    repeat' (refine ite_le (fun _ => ?_) (fun _ => ?_))
    all_goals first | omega | exact hb _ _
  | pad => simp

end ZkFormal.Sha.Complete
