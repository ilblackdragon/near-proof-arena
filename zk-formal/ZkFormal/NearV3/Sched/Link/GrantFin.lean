import ZkFormal.NearV3.Sched.Link.GrantRun

/-!
# ZkFormal.NearV3.Sched.Link.GrantFin — the memory `w` column is `granted` (stage E step a)

The memory table carries a second value along each segment: `w` (granted total), with
`INIT w = inc`, `READ w = wp`, `GRANT w = wp + isL·ok·inc` (mod `P`) and `wp` = the previous row's
`w` (`Mem.row_init`, `row_read`, `row_grant`, `row_next`). For instance τ (process key block `f`,
`MemCtx`), on τ's link addresses (`QL τ n`):

* `simW t a = (stAt t).granted[a − τ·2^14]`: the simulated granted totals;
* **`frameW`**: an address changes only at its ops' times (`tryGrant` writes `granted[l]` only
  for the slot's link, whose GRANT op is at that time);
* **`step_w`**: an op on a link address that reads `wp = simW t` writes `w = simW (t + 1)`. A
  process GRANT has `isL = 1` (`init_row_isL`), `ok = [tryGrant grants]` (`grant_sem`, with
  the in-values read from the simulation by `mem_reads`), and `wp + inc ≤ 4,500,000` by `GInv`
  (`stAt_ginv`), so the mod-`P` sum is exact (`tryGrant_gget`); a scan READ (time `< T0`) keeps it;
* **`fin_w`**: the last row of a link segment holds `simW 2^29`, by induction along the segment
  (segments are unique per τ-address, `mem_seg_uniqueQ`; times strictly increase,
  `mem_seg_timeQ`; the frame bridges the gaps, `frame_iter`);
* **`fin_granted`**: hence the final `w` of link `l` is `stF.granted[l]` (`stAt_endG`);
* **`codec_gfin`**: the codec's `gfin` of record `k` (received on `SFIN`, sole sender the memory)
  is `stF.granted[k]`.

Extra hypotheses on the start state `st` (both proved for `lpState`): `GInv n 4,500,000 st`
(`lpState_ginv`) and `SzOk n st`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- The link addresses of instance τ. -/
def QL (τ n a : Nat) : Bool := QT τ n a && decide (a - τ * 16384 < 4096)

theorem QL_iff {τ n a : Nat} (hn : n ≤ 64) :
    QL τ n a = true ↔ τ * 16384 ≤ a ∧ a - τ * 16384 < n * n := by
  have := Nat.mul_le_mul hn hn
  simp only [QL, QT, idxOk, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem QL_qt {τ n a : Nat} (h : QL τ n a = true) : QT τ n a = true := by
  simp only [QL, Bool.and_eq_true] at h; exact h.1

theorem QL_link {τ n l : Nat} (hn : n ≤ 64) (hl : l < n * n) : QL τ n (addrOf τ 0 l) = true := by
  rw [QL_iff hn]; unfold addrOf; omega

/-- The simulated granted totals of instance τ. -/
def simW (τ n : Nat) (allowed : Array Bool) (tr : Trace Fp) (tp f m : Nat) (st : St) (t a : Nat) : Nat :=
  if QL τ n a = true then (stAt n allowed tr tp f m st t).granted[a - τ * 16384]! else 0

/-- `tryGrant_gget` without the `let`. -/
theorem tryGrant_gget' (n : Nat) (allowed : Array Bool) {S : St} (hG : GInv n 4500000 S) {l : Nat}
    (hl : l < S.granted.size) (bw x : Nat) :
    (tryGrant n allowed S l bw).2.granted[x]! =
      (if (allowed[l]! && decide (bw ≤ S.senderBudget[l / n]!) && decide (bw ≤ S.receiverBudget[l % n]!)) = true ∧
          x = l then S.granted[x]! + bw else S.granted[x]!) :=
  tryGrant_gget n allowed hG hl bw x

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd f m : Nat}
  {P : InstPub} {allowed : Array Bool} {st : St}

namespace MemCtx
variable (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
include C

/-- **Frame** for the granted totals. -/
theorem frameW (hS : SzOk P.n st) (hG : GInv P.n 4500000 st) :
    Frame (memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n))
      (simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st) := by
  intro t a hno
  unfold simW
  by_cases hq : QL (cv tr tp f Proc.tau) P.n a = true
  · rw [if_pos hq, if_pos hq]
    cases he : entAt tr tp f m t with
    | none => rw [stAt_none _ _ _ _ _ _ _ he]
    | some p =>
      obtain ⟨i, j⟩ := p
      obtain ⟨hi, hj, ht⟩ := entAt_some he
      rw [stAt_some _ _ _ _ _ _ _ he]
      obtain ⟨-, -, -, -, hl, -⟩ := C.ent hi hj
      obtain ⟨-, -, ⟨o9, m9, t9, a9, -⟩⟩ := C.slot_ops hi hj
      have n9 := fun h => hno o9 m9 ⟨h, by rw [t9, ht]⟩
      rw [a9] at n9
      have hsz := (stAt_szOk P.n allowed tr tp f m st hS t).2.2
      have hGt := stAt_ginv P.n allowed tr tp f m st hG t
      rw [tryGrant_gget' P.n allowed hGt (by rw [hsz]; exact hl)]
      rw [if_neg]
      rintro ⟨-, hx⟩
      apply n9
      have := (QL_iff C.PO.n64).1 hq
      unfold addrOf; omega
  · rw [if_neg hq, if_neg hq]

/-- **Correct step** of one op on a link address. -/
theorem step_w (hS : SzOk P.n st) (hG : GInv P.n 4500000 st) {r : Nat} (hr : r < tr.height tm)
    (ha : cv tr tm r Mem.act = 1) (hf0 : cv tr tm r Mem.fst = 0)
    (hq : QL (cv tr tp f Proc.tau) P.n (cv tr tm r Mem.addr) = true)
    (hwp : cv tr tm r Mem.wp =
      simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st (cv tr tm r Mem.t) (cv tr tm r Mem.addr)) :
    cv tr tm r Mem.w =
      simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st (cv tr tm r Mem.t + 1) (cv tr tm r Mem.addr) := by
  have hn := C.PO.n64
  have hnn := Nat.mul_le_mul hn hn
  have hqt := QL_qt hq
  have hql := (QL_iff hn).1 hq
  have h1 := opMsg_get1 (tr := tr) (tm := tm) (pub := pub) r
  rcases op_row C.hH C.O C.OS C.OO C.PS C.htau C.hf C.hk C.hc C.I hn hr ha hf0 hqt with
    ⟨i, hi, j, hj, k, hk', hM⟩ | ⟨f', hf', hq', ht', hM⟩
  · -- a GRANT of slot `(i, j)`
    obtain ⟨e, hb⟩ := ent_time C.hL C.hHt C.I hi hj hk'
    rw [hM, e, Option.some.injEq] at h1
    have htt := (Proc.ofNat_cv_eq (by unfold T0 at hb; omega) (cv_lt _ _)).1 h1
    have he := entAt_slot C.I hi hj
    obtain ⟨es, er, hs, hr', hl, hinc⟩ := C.ent hi hj
    obtain ⟨⟨o7, m7, t7, a7, v7⟩, ⟨o8, m8, t8, a8, v8⟩, ⟨o9, m9, t9, a9, v9⟩⟩ := C.slot_ops hi hj
    have y7 := C.mem_reads o7 m7
    have y8 := C.mem_reads o8 m8
    have y9 := C.mem_reads o9 m9
    rw [v7, t7, a7] at y7; rw [v8, t8, a8] at y8; rw [v9, t9, a9] at y9
    unfold simσ at y7 y8 y9
    rw [if_pos (QT_snd hn hs), rd_snd _ hn hs] at y7
    rw [if_pos (QT_rcv hn hr'), rd_rcv _ hn hr'] at y8
    rw [if_pos (QT_link hn hl), rd_link _ hn hl] at y9
    have hB := stAt_bnd P.n allowed tr tp f m st C.hB (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
    have hsz := (stAt_szOk P.n allowed tr tp f m st hS (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)).2.2
    have hGt := stAt_ginv P.n allowed tr tp f m st hG (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
    obtain ⟨gS, gR, gL, -, -, -⟩ := grant_sem C.hH C.O C.OS C.I C.hτ C.SP C.PO C.hB C.hV hi hj
      (by rw [y7]; exact (hB _).1) (by rw [y8]; exact (hB _).2.1) (by rw [y9]; exact (hB _).2.2)
    have hLp := C.hL
    obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := C.I.hdr i hi
    obtain ⟨-, -, -, -, -, -, -, -, -, e7, -, e8, -, e9, -, -, -, -, hok, -⟩ :=
      Proc.ent_msgs hLp C.hHt hh0 hh hj
    rw [ht] at e7 e8 e9
    have hT : cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j < 2013265921 := by unfold T0 at hb; omega
    have hτ' := C.hτ
    have hokb := ok_iff hok gS gR gL
    have hseg := seg_init C.hM hr ha
    have hV := C.hV
    rw [← htt] at hwp ⊢
    generalize hτd : cv tr tp f Proc.tau = τ at *
    generalize hw : Proc.hdrAt tr tp f i + 1 + j = w at *
    have lt := fun x => cv_lt (tr := tr) (t := tp) w x
    rcases hk' with rfl | rfl | rfl
    · exfalso
      rw [e7] at hM
      obtain ⟨-, -, ad, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      rw [ad] at hql; unfold addrOf at hql; omega
    · exfalso
      rw [e8] at hM
      obtain ⟨-, -, ad, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      rw [ad] at hql; unfold addrOf at hql; omega
    · rw [e9] at hM
      obtain ⟨-, hgr, ad, -, -, -, ic, ok, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      -- `isL = 1` from the segment's `INIT` row
      obtain ⟨f0, hf0r, hff, ea, -, eil⟩ := hseg
      have hf0h : f0 < tr.height tm := by omega
      have hil : cv tr tm r Mem.isL = 1 := by
        rw [eil, init_row_isL C.hH C.O.mem hτ' hn hV hf0h hff (by rw [← ea]; exact hqt), ← ea, ad]
        unfold addrOf; rw [if_pos (by omega)]
      obtain ⟨-, -, -, -, -, gw1, gw0⟩ := Mem.row_grant C.hM hr hgr
      have eo : addrOf τ 0 (cv tr tp w Proc.link) - τ * 16384 = cv tr tp w Proc.link := by
        unfold addrOf; omega
      unfold simW at hwp ⊢
      rw [ad, if_pos (QL_link hn hl), eo] at hwp ⊢
      rw [stAt_some _ _ _ _ _ _ _ he, hw, tryGrant_gget' P.n allowed hGt (by rw [hsz]; exact hl)]
      have hG1 := hGt (cv tr tp w Proc.link)
      rw [← es] at hG1
      by_cases hd : cv tr tp w Proc.ok = 1
      · have hd' := hokb.1 hd
        rw [← es, ← er, ← y7, ← y8] at *
        rw [if_pos ⟨hd', rfl⟩, ← gw1 hil (by rw [ok]; exact hd), hwp, ic]
        have : cv tr tp w Proc.inc ≤ cv tr tp w Proc.sbIn := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd'; exact hd'.1.2
        rw [← y7] at hG1
        exact Nat.mod_eq_of_lt (by omega)
      · rw [if_neg (fun c => hd (hokb.2 (by rw [es, er, y7, y8] at *; exact c.1)))]
        rw [gw0 (Or.inr (by rw [ok]; have := (Mem.row_flags C.hM hr).2.2.2.2.2.2.2.1; rw [ok] at this; omega)), hwp]
  · -- a scan READ: before the process times
    have hSD := sd_local C.hH C.OS
    have hS' := Scan.SLocal.of_sd hSD
    obtain ⟨-, hkS, -, hcol⟩ := Scan.shape_all hS' hf' hq' 19 (by omega)
    have hcid := hcol Scan.cid (by simp [Scan.reqCols])
    have hlt := (blk_ok C.hH C.OS C.SP C.PO hf' hq' ht').lt
    have := C.PO.len16
    have h2 := congrArg (·[2]?) hM
    rw [hM, Scan.op_msg, hcid, hkS] at h1
    simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
    have htt := (Proc.ofNat_cv_eq (by omega) (cv_lt _ _)).1 h1
    have hrd : cv tr tm r Mem.isRd = 1 := by
      obtain ⟨-, -, -, hR, hG, -, -, -, -, -, hsum, -⟩ := Mem.row_flags C.hM hr
      simp only [Mem.opMsg_eq, Scan.op_msg, hkS, List.map_cons, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq] at h2
      have := (Proc.ofNat_cv_eq (by omega) (by omega)).1 h2
      omega
    rw [(Mem.row_read C.hM hr hrd).2.1, hwp]
    unfold simW
    rw [stAt_none _ _ _ _ _ _ _ (entAt_lt C.hL C.hHt C.I (show cv tr tm r Mem.t < T0 by unfold T0; omega))]

/-- **The last row of a link segment holds the final simulated granted total.** -/
theorem fin_w (hS : SzOk P.n st) (hG : GInv P.n 4500000 st) {r : Nat} (hr : r < tr.height tm)
    (hl : cv tr tm r Mem.lst = 1) (hq : QL (cv tr tp f Proc.tau) P.n (cv tr tm r Mem.addr) = true) :
    cv tr tm r Mem.w =
      simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st (2 ^ 29) (cv tr tm r Mem.addr) := by
  have hM := C.hM
  have hn := C.PO.n64
  have hqt := QL_qt hq
  have hI := initOnce_of C.hτ hn C.hV
  have hT := mem_timeQ C.hH C.O C.OS C.OO C.PS C.htau C.hf C.hk C.hc C.I C.SP C.PO hn
  have huniq := mem_seg_uniqueQ C.hH C.O.mem hI
  have hF := C.frameW hS hG
  have ha : cv tr tm r Mem.act = 1 := by
    have F := Mem.row_flags hM hr; omega
  obtain ⟨f0, hf0r, hff0, hact, hrest⟩ := Mem.seg_of hM hr ha
  have hf0 : f0 < tr.height tm := by omega
  have ea : cv tr tm r Mem.addr = cv tr tm f0 Mem.addr := (hact r hf0r (Nat.le_refl _)).2
  -- every op row on the address lies in `(f0, r]`
  have inseg : ∀ r', r' < tr.height tm → cv tr tm r' Mem.act = 1 → cv tr tm r' Mem.fst = 0 →
      cv tr tm r' Mem.addr = cv tr tm r Mem.addr → f0 < r' ∧ r' ≤ r := by
    intro r' hr' ha' hf' he
    obtain ⟨f1, hf1, hff1, hact1, hrest1⟩ := Mem.seg_of hM hr' ha'
    have e1 : cv tr tm r' Mem.addr = cv tr tm f1 Mem.addr := (hact1 r' hf1 (Nat.le_refl _)).2
    have e : f1 = f0 := huniq f1 f0 (by omega) hf0 hff1 hff0 (by rw [← e1, he]; exact hqt)
      (by rw [← e1, he, ea])
    rw [e] at hf1 hrest1
    have hlt : f0 < r' := by
      rcases Nat.lt_or_ge f0 r' with h | h
      · exact h
      · have : f0 = r' := by omega
        rw [← this] at hf'; omega
    refine ⟨hlt, Nat.le_of_not_lt fun hrr => ?_⟩
    have := (hrest1 (r + 1) (by omega) (by omega)).2
    rw [Nat.add_sub_cancel] at this
    omega
  have hmono := mem_seg_timeQ C.hH C.O.mem C.O.cmp hT hr (fun x h1 h2 => (hact x h1 h2).1)
    (fun x h1 h2 => (hrest x h1 h2).1)
    (fun x h1 h2 => by rw [(hact x h1 h2).2, ← ea]; exact hqt)
  -- ops on the address at times in `[s, s + d)` come from rows of the segment
  have nofr : ∀ s d, (∀ y, f0 < y → y ≤ r → ¬ (s ≤ cv tr tm y Mem.t ∧ cv tr tm y Mem.t < s + d)) →
      simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st (s + d) (cv tr tm r Mem.addr) =
        simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st s (cv tr tm r Mem.addr) := by
    intro s d h
    exact frame_iter _ _ hF (cv tr tm r Mem.addr) d s (fun o ho hoa hin => by
      obtain ⟨r', hr', ha', hf', rfl⟩ := mem_memOps (mem_memOpsQ.1 ho).1
      obtain ⟨h1, h2⟩ := inseg r' hr' ha' hf' hoa
      exact h r' h1 h2 hin)
  -- the value after each row of the segment
  let e : Nat → Nat := fun x => if x = f0 then 0 else cv tr tm x Mem.t + 1
  have claim : ∀ d, f0 + d ≤ r →
      cv tr tm (f0 + d) Mem.w = simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st (e (f0 + d))
        (cv tr tm r Mem.addr) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.add_zero, e, if_pos rfl]
      -- the `INIT` row: `w = inc = st.granted[l]`
      have hq0 : QT (cv tr tp f Proc.tau) P.n (cv tr tm f0 Mem.addr) = true := by rw [← ea]; exact hqt
      obtain ⟨x, hx, hmsg⟩ := init_row_msg C.hH C.O.mem hn C.hV hf0 hff0 hq0
      have hx' := idxOk_lt hn hx
      rw [Mem.opMsg_eq] at hmsg
      simp only [initRec, List.map_cons, List.map_nil, List.cons.injEq] at hmsg
      obtain ⟨eaddr, -, -, -, -, einc, -⟩ := hmsg
      have hτ' := C.hτ
      have had := cell_ofNat eaddr (by omega)
      have hql := (QL_iff hn).1 hq
      rw [ea, had] at hql
      have hnn := Nat.mul_le_mul hn hn
      have hxl : x < 4096 := by omega
      rw [if_pos hxl] at einc
      have hgx : st.granted[x]! ≤ 4500000 := by have := hG x; omega
      rw [← (Mem.row_init hM hf0 hff0).2.2.1, cell_ofNat einc (by omega)]
      unfold simW
      rw [ea, had, if_pos (by rw [QL_iff hn]; omega), show cv tr tp f Proc.tau * 16384 + x -
        cv tr tp f Proc.tau * 16384 = x by omega]
      rfl
    | succ d ih =>
      intro hd
      rw [show f0 + (d + 1) = f0 + d + 1 by omega] at hd ⊢
      have ih' := ih (by omega)
      have hx1 : f0 < f0 + d + 1 := by omega
      obtain ⟨hf1, hl1⟩ := hrest (f0 + d + 1) hx1 hd
      rw [Nat.add_sub_cancel] at hl1
      have N := Mem.row_next hM (r := f0 + d) (by omega) (hact (f0 + d) (by omega) (by omega)).1 hl1
      have hadd : cv tr tm (f0 + d + 1) Mem.addr = cv tr tm r Mem.addr := by
        rw [(hact _ (by omega) hd).2, ← ea]
      have hle : e (f0 + d) ≤ cv tr tm (f0 + d + 1) Mem.t := by
        simp only [e]
        split
        · omega
        · have := hmono (f0 + d) (f0 + d + 1) (by omega) (by omega) hd; omega
      have hbr := nofr (e (f0 + d)) (cv tr tm (f0 + d + 1) Mem.t - e (f0 + d)) (fun y h1 h2 ⟨hs, he⟩ => by
        rcases Nat.lt_or_ge y (f0 + d + 1) with hy | hy
        · -- an earlier row of the segment
          simp only [e] at hs
          split at hs
          · omega
          · rcases Nat.eq_or_lt_of_le (show y ≤ f0 + d by omega) with q | q
            · rw [q] at hs; omega
            · have := hmono y (f0 + d) (by omega) q (by omega); omega
        · rcases Nat.eq_or_lt_of_le hy with q | q
          · rw [← q] at he; omega
          · have := hmono (f0 + d + 1) y (by omega) q h2; omega)
      rw [show e (f0 + d) + (cv tr tm (f0 + d + 1) Mem.t - e (f0 + d)) = cv tr tm (f0 + d + 1) Mem.t by
        omega] at hbr
      have hwp : cv tr tm (f0 + d + 1) Mem.wp = simW (cv tr tp f Proc.tau) P.n allowed tr tp f m st
          (cv tr tm (f0 + d + 1) Mem.t) (cv tr tm (f0 + d + 1) Mem.addr) := by
        rw [N.2.2.2.2.2.1, ih', hadd, hbr]
      have hs := C.step_w hS hG (by omega) (hact _ (by omega) hd).1 hf1 (by rw [hadd]; exact hq) hwp
      rw [hadd] at hs
      rw [hs]
      simp only [e, if_neg (show f0 + d + 1 ≠ f0 by omega)]
  have hc := claim (r - f0) (by omega)
  rw [show f0 + (r - f0) = r by omega] at hc
  rw [hc]
  have htr := hT r hr ha hqt
  have hle : e r ≤ 2 ^ 29 := by simp only [e]; split <;> omega
  have hend := nofr (e r) (2 ^ 29 - e r) (fun y h1 h2 ⟨hs, he⟩ => by
    simp only [e] at hs
    split at hs
    · omega
    · rcases Nat.eq_or_lt_of_le h2 with q | q
      · rw [q] at hs; omega
      · have := hmono y r (by omega) q (Nat.le_refl _); omega)
  rw [show e r + (2 ^ 29 - e r) = 2 ^ 29 by omega] at hend
  exact hend.symm

/-- **Final granted total of link `l`.** -/
theorem fin_granted (hS : SzOk P.n st) (hG : GInv P.n 4500000 st) {r l : Nat} (hr : r < tr.height tm)
    (hl : cv tr tm r Mem.lst = 1) (hll : l < P.n * P.n)
    (ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 0 l) :
    cv tr tm r Mem.w = (specSt P.n allowed (reqsOf P) tr tp f st m).granted[l]! := by
  have hn := C.PO.n64
  rw [C.fin_w hS hG hr hl (by rw [ha]; exact QL_link hn hll), ha]
  unfold simW
  rw [if_pos (QL_link hn hll), show addrOf (cv tr tp f Proc.tau) 0 l - cv tr tp f Proc.tau * 16384 = l by
    unfold addrOf; omega]
  have := C.stAt_endG
  simp only [GArr, Prod.mk.injEq] at this
  rw [this.2.2.2]

end MemCtx

/-- **The codec's final granted total of record `k` is the spec's `stF.granted[k]`.** -/
theorem codec_gfin (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
    (hS : SzOk P.n st) (hG : GInv P.n 4500000 st)
    (O : CodecValOwn AP tcd) {fc : Nat} (hfc : fc < tr.height tcd) (hF : cv tr tcd fc Codec.kF = 1)
    (hτ : cv tr tcd fc Codec.tau = cv tr tp f Proc.tau) (hNN : cv tr tcd fc Codec.NN = P.n * P.n)
    {k : Nat} (hk : k < P.n * P.n) :
    cv tr tcd (fc + 5 + 24 * k + 23) Codec.gfin = (specSt P.n allowed (reqsOf P) tr tp f st m).granted[k]! := by
  have hL := codec_local C.hH O
  have hH22 := codec_h22 C.hH O
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hfc hF
  have hkN : k < cv tr tcd fc Codec.NN := by rw [hNN]; exact hk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, m11, msg11, -⟩ := Codec.codec_rec_msgs hL (RR k hkN) (RS k hkN)
  have hw : fc + 5 + 24 * k + 23 < tr.height tcd := (RR k hkN 23 (by omega)).1
  obtain ⟨r, hr, hl, hmsg⟩ := fin_src C.hH C.O.mem O.lt hw (by rw [O.tab]; exact codec_mem 11 (by decide))
    (by rw [Codec.i11_def]) (by rw [Codec.i11_def]) (by rw [m11]; exact Nat.one_ne_zero)
  rw [msg11] at hmsg
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨e1, -, e3, -⟩ := hmsg
  have hτ' := C.hτ
  have hn := C.PO.n64
  have hkk : k < 4096 := by have := Nat.mul_le_mul hn hn; omega
  have ha : cv tr tm r Mem.addr = addrOf (cv tr tp f Proc.tau) 0 k := by
    show (tr.cell tm r Mem.addr).toNat = _
    rw [← e1, toNat_ofNat_lt' (by omega)]; unfold addrOf; rw [← hτ]; omega
  have hv : cv tr tm r Mem.w = cv tr tcd (fc + 5 + 24 * k + 23) Codec.gfin := by
    show (tr.cell tm r Mem.w).toNat = _
    rw [← e3, toNat_ofNat_lt' (cv_lt _ _)]
  rw [← hv]
  exact C.fin_granted hS hG hr hl hk ha

end

end ZkFormal.NearV3.Sched
