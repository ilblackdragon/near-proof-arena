import ZkFormal.NearV3.Sched.Link.MemRun

/-!
# ZkFormal.NearV3.Sched.Link.MemLink — memory consistency of an instance: `EntryMem`, `ReadOk`

Stage B step 2. `MemCtx` bundles what the memory link of instance τ = `tau(f)` uses: the AIR,
the ownership conditions, the instance's rows, its public data, the spec state `st`
(`≤ 4,500,000`, sizes) and `InitVals` (`hInitVals`; it also fixes the `INIT` rows' `isL`,
`init_row_isL`).

The simulation is `simσ t a = rd τ (stAt t) a` on τ's addresses (`QT τ n`).

* `frame`: an address changes only at its ops' times (`tryGrant` writes exactly the three
  GRANT addresses of the slot, which all have ops at that time);
* `step_ok`: a slot's GRANTs write the `tryGrant` result (`grant_sem`, in-values bounded by the
  simulation); the scan READs (times `≤ 2^16 < T0`) write nothing;
* **`mem_reads`**: every op on τ's addresses reads the simulation (`mem_reads_simQ`);
* **`entry_mem`**: `EntryMem` for every entry of the instance;
* **`read_ok`**: `ReadOk` for the instance.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

/-- What the memory link of the instance with key block `f` uses. -/
structure MemCtx (AP : AirP) (pub : List Fp) (tr : Trace Fp) (tp tm tcmp ts tch tg tsd tcd f m : Nat)
    (P : InstPub) (allowed : Array Bool) (st : St) : Prop where
  hH : HoldsP AP pub tr
  O : SchedOwn AP tp tm tcmp ts tch tg
  OS : ScanOwn AP tsd tp
  OO : OpOwn AP tp tsd tcd
  PS : ParSmall AP pub
  htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256
  hf : f < tr.height tp
  hk : cv tr tp f Proc.kK = 1
  hc : cv tr tp f Proc.kc = 0
  I : Proc.Inst tr tp f m
  SP : ScanPub AP pub (cv tr tp f Proc.tau) P
  PO : ScanPubOk P
  hB : ABnd 4500000 st
  hsz : SzA P.n st
  hV : InitVals AP tr pub (cv tr tp f Proc.tau) P.n allowed st

/-- The simulated memory of instance τ. -/
def simσ (τ n : Nat) (allowed : Array Bool) (tr : Trace Fp) (tp f m : Nat) (st : St) (t a : Nat) : Nat :=
  if QT τ n a = true then rd τ (stAt n allowed tr tp f m st t) a else 0

/-- An `INIT` row with an address in τ's range has a τ address. -/
theorem init_row_qt {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tm : Nat} (hH : HoldsP AP pub tr)
    (hM : MemOwn AP tm) {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64) {allowed : Array Bool} {st : St}
    (hV : InitVals AP tr pub τ n allowed st) {f : Nat} (hf : f < tr.height tm)
    (hff : cv tr tm f Mem.fst = 1) (h1 : τ * 16384 ≤ cv tr tm f Mem.addr)
    (h2 : cv tr tm f Mem.addr < τ * 16384 + 16384) : QT τ n (cv tr tm f Mem.addr) = true := by
  have hL := mLocal_of hH hM
  have hs := mem_sopSent_of_recv hH hM hf (Mem.init_row hL hf hff).1
  have hin : Mem.opMsg tr tm pub f ∈ (sopSent AP tr pub).filter (isTauInit τ) := by
    refine List.mem_filter.2 ⟨hs, ?_⟩
    simp only [isTauInit, Mem.op_init hL hf hff, opMsg_head, Bool.and_eq_true, beq_iff_eq,
      Option.any_some, decide_eq_true_eq, toNat_ofNat_lt' (cv_lt _ _)]
    exact ⟨trivial, h1, h2⟩
  obtain ⟨x, hx, he⟩ := (mem_initMsgs hn).1 (hV.subset hin)
  have hx' := idxOk_lt hn hx
  have e1 := congrArg List.head? he
  rw [opMsg_head] at e1
  simp only [initRec, List.map_cons, List.head?_cons, Option.some.injEq] at e1
  have e := (Proc.ofNat_cv_eq (cv_lt _ _) (by omega)).1 e1
  rw [QT_iff, e]
  exact ⟨by omega, by rw [show τ * 16384 + x - τ * 16384 = x by omega]; exact hx⟩

theorem ok_iff {ok cS cR cL inc sb rb : Nat} {al : Bool} (h : ok = cS * cR * cL)
    (hS : cS = if inc ≤ sb then 1 else 0) (hR : cR = if inc ≤ rb then 1 else 0)
    (hL : cL = if al then 1 else 0) :
    (ok = 1 ↔ (al && decide (inc ≤ sb) && decide (inc ≤ rb)) = true) := by
  subst h hS hR hL
  by_cases a : al = true <;> by_cases b : inc ≤ sb <;> by_cases c : inc ≤ rb <;> simp [a, b, c]

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd f m : Nat}
  {P : InstPub} {allowed : Array Bool} {st : St}

namespace MemCtx
variable (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
include C

theorem hτ : cv tr tp f Proc.tau < 256 := C.htau f C.hf (Proc.act_of (pLocal_of C.hH C.O.tp_lt C.O.tp_tab) C.hf (Or.inl C.hk))

theorem hL : Proc.PLocal tr tp pub := pLocal_of C.hH C.O.tp_lt C.O.tp_tab
theorem hHt : tr.height tp ≤ 2 ^ 22 := proc_height C.hH C.O.tp_lt C.O.tp_tab
theorem hM : Mem.MLocal tr tm pub := mLocal_of C.hH C.O.mem

/-- The entry facts used below. -/
theorem ent {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link / P.n ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link % P.n ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s < P.n ∧ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r < P.n ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < P.n * P.n ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc < 2 ^ 25 := by
  obtain ⟨hsr, hs, hr, hinc⟩ := entry_sr C.hH C.O C.OS C.SP C.PO C.I rfl hi hj
  have hn : 0 < P.n := by omega
  have hl : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < P.n * P.n := by
    have : (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s + 1) * P.n ≤ P.n * P.n :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; omega
  refine ⟨?_, ?_, hs, hr, hl, hinc⟩
  · rw [← hsr, Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr]; omega
  · rw [← hsr, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- The three GRANT ops of a slot, in `memOpsQ`. -/
theorem slot_ops {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    (∃ o ∈ memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n),
      o.t = cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j ∧
      o.a = addrOf (cv tr tp f Proc.tau) 1 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s) ∧
      o.vin = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn) ∧
    (∃ o ∈ memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n),
      o.t = cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j ∧
      o.a = addrOf (cv tr tp f Proc.tau) 2 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r) ∧
      o.vin = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn) ∧
    (∃ o ∈ memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n),
      o.t = cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j ∧
      o.a = addrOf (cv tr tp f Proc.tau) 0 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link) ∧
      o.vin = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn) := by
  obtain ⟨-, -, hs, hr, hl, -⟩ := C.ent hi hj
  have hn := C.PO.n64
  have hnn := Nat.mul_le_mul hn hn
  have G := grant_rows C.hH C.O C.I C.hτ hi hj (by omega) (by omega) (by omega)
  obtain ⟨r7, h7, a7, z7, -, ad7, t7, vi7, -⟩ := G 7 (Or.inl rfl)
  obtain ⟨r8, h8, a8, z8, -, ad8, t8, vi8, -⟩ := G 8 (Or.inr (Or.inl rfl))
  obtain ⟨r9, h9, a9, z9, -, ad9, t9, vi9, -⟩ := G 9 (Or.inr (Or.inr rfl))
  simp only [if_true, show (8 : Nat) ≠ 7 from by decide, show (9 : Nat) ≠ 7 from by decide,
    show (9 : Nat) ≠ 8 from by decide, if_false] at ad7 vi7 ad8 vi8 ad9 vi9
  refine ⟨⟨_, mem_memOpsQ.2 ⟨memOps_mem h7 a7 z7, ?_⟩, t7, ad7, vi7⟩,
    ⟨_, mem_memOpsQ.2 ⟨memOps_mem h8 a8 z8, ?_⟩, t8, ad8, vi8⟩,
    ⟨_, mem_memOpsQ.2 ⟨memOps_mem h9 a9 z9, ?_⟩, t9, ad9, vi9⟩⟩
  · show QT _ _ (cv tr tm r7 Mem.addr) = true
    rw [ad7]; exact QT_snd hn hs
  · show QT _ _ (cv tr tm r8 Mem.addr) = true
    rw [ad8]; exact QT_rcv hn hr
  · show QT _ _ (cv tr tm r9 Mem.addr) = true
    rw [ad9]; exact QT_link hn hl

/-- **Frame.** -/
theorem frame : Frame (memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n))
    (simσ (cv tr tp f Proc.tau) P.n allowed tr tp f m st) := by
  intro t a hno
  unfold simσ
  split
  · next hq =>
    cases he : entAt tr tp f m t with
    | none => rw [stAt_none _ _ _ _ _ _ _ he]
    | some p =>
      obtain ⟨i, j⟩ := p
      obtain ⟨hi, hj, ht⟩ := entAt_some he
      rw [stAt_some _ _ _ _ _ _ _ he]
      obtain ⟨es, er, hs, hr, hl, -⟩ := C.ent hi hj
      obtain ⟨⟨o7, m7, t7, a7, -⟩, ⟨o8, m8, t8, a8, -⟩, ⟨o9, m9, t9, a9, -⟩⟩ := C.slot_ops hi hj
      have n7 := fun h => hno o7 m7 ⟨h, by rw [t7, ht]⟩
      have n8 := fun h => hno o8 m8 ⟨h, by rw [t8, ht]⟩
      have n9 := fun h => hno o9 m9 ⟨h, by rw [t9, ht]⟩
      rw [a7] at n7; rw [a8] at n8; rw [a9] at n9
      have hsz := stAt_sz P.n allowed tr tp f m st C.hsz t
      generalize hτd : cv tr tp f Proc.tau = τ at *
      obtain ⟨h1, hx⟩ := QT_iff.1 hq
      have hx' := idxOk_lt C.PO.n64 hx
      generalize hw : Proc.hdrAt tr tp f i + 1 + j = w at *
      have G := fun x => tryGrant_get P.n allowed hsz hl (cv tr tp w Proc.inc) x
      unfold addrOf at n7 n8 n9
      unfold rd
      split
      · rw [(G _).2.2]; split
        · next hc => exfalso; exact n9 (by omega)
        · rfl
      · split
        · rw [(G _).1]; split
          · next hc => exfalso; exact n7 (by omega)
          · rfl
        · rw [(G _).2.1]; split
          · next hc => exfalso; exact n8 (by omega)
          · rfl
  · rfl

/-- **Correct steps.** -/
theorem step_ok : StepOk (memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n))
    (simσ (cv tr tp f Proc.tau) P.n allowed tr tp f m st) := by
  have hn := C.PO.n64
  have hnn := Nat.mul_le_mul hn hn
  intro t hyp o ho hot
  obtain ⟨ho', hq⟩ := mem_memOpsQ.1 ho
  obtain ⟨r, hr, ha, hf0, rfl⟩ := mem_memOps ho'
  simp only at hq hot ⊢
  have h1 := opMsg_get1 (tr := tr) (tm := tm) (pub := pub) r
  rcases op_row C.hH C.O C.OS C.OO C.PS C.htau C.hf C.hk C.hc C.I hn hr ha hf0 hq with
    ⟨i, hi, j, hj, k, hk', hM⟩ | ⟨f', hf', hq', ht', hM⟩
  · -- a GRANT of slot `(i, j)`
    obtain ⟨e, hb⟩ := ent_time C.hL C.hHt C.I hi hj hk'
    rw [hM, e, Option.some.injEq] at h1
    have htt := (Proc.ofNat_cv_eq (by unfold T0 at hb; omega) (cv_lt _ _)).1 h1
    rw [hot] at htt
    subst htt
    have he := entAt_slot C.I hi hj
    unfold simσ
    rw [if_pos hq, stAt_some _ _ _ _ _ _ _ he]
    obtain ⟨es, er, hs, hr', hl, hinc⟩ := C.ent hi hj
    obtain ⟨⟨o7, m7, t7, a7, v7⟩, ⟨o8, m8, t8, a8, v8⟩, ⟨o9, m9, t9, a9, v9⟩⟩ := C.slot_ops hi hj
    have y7 := hyp o7 m7 t7
    have y8 := hyp o8 m8 t8
    have y9 := hyp o9 m9 t9
    rw [v7, a7] at y7; rw [v8, a8] at y8; rw [v9, a9] at y9
    unfold simσ at y7 y8 y9
    rw [if_pos (QT_snd hn hs), rd_snd _ hn hs] at y7
    rw [if_pos (QT_rcv hn hr'), rd_rcv _ hn hr'] at y8
    rw [if_pos (QT_link hn hl), rd_link _ hn hl] at y9
    have hB := stAt_bnd P.n allowed tr tp f m st C.hB (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
    have hsz := stAt_sz P.n allowed tr tp f m st C.hsz (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
    obtain ⟨gS, gR, gL, oS, oR, oL⟩ := grant_sem C.hH C.O C.OS C.I C.hτ C.SP C.PO C.hB C.hV hi hj
      (by rw [y7]; exact (hB _).1) (by rw [y8]; exact (hB _).2.1) (by rw [y9]; exact (hB _).2.2)
    have hLp := C.hL
    obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := C.I.hdr i hi
    obtain ⟨-, -, -, -, -, -, -, -, -, e7, -, e8, -, e9, -, -, -, -, hok, -⟩ :=
      Proc.ent_msgs hLp C.hHt hh0 hh hj
    rw [ht] at e7 e8 e9
    have hT : cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j < 2013265921 := by unfold T0 at hb; omega
    have hτ' := C.hτ
    generalize hτd : cv tr tp f Proc.tau = τ at *
    generalize hw : Proc.hdrAt tr tp f i + 1 + j = w at *
    have hok' := ok_iff hok gS gR gL
    have G := fun x => tryGrant_get P.n allowed hsz hl (cv tr tp w Proc.inc) x
    have lt := fun x => cv_lt (tr := tr) (t := tp) w x
    rcases hk' with rfl | rfl | rfl
    · rw [e7] at hM
      obtain ⟨-, -, ad, -, -, vo, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      rw [ad, vo, rd_snd _ hn hs, (G _).1, oS, ← es, ← er, ← y7, ← y8]
      by_cases hd : cv tr tp w Proc.ok = 1
      · rw [if_pos hd, if_pos ⟨hok'.1 hd, rfl⟩]
      · rw [if_neg hd, if_neg (fun c => hd (hok'.2 c.1))]
    · rw [e8] at hM
      obtain ⟨-, -, ad, -, -, vo, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      rw [ad, vo, rd_rcv _ hn hr', (G _).2.1, oR, ← es, ← er, ← y7, ← y8]
      by_cases hd : cv tr tp w Proc.ok = 1
      · rw [if_pos hd, if_pos ⟨hok'.1 hd, rfl⟩]
      · rw [if_neg hd, if_neg (fun c => hd (hok'.2 c.1))]
    · rw [e9] at hM
      obtain ⟨-, -, ad, -, -, vo, -⟩ := row_of_msg C.hM hr ha hM (by unfold addrOf; omega) hT
        (lt _) (lt _) (lt _) (lt _) (lt _)
      rw [ad, vo, rd_link _ hn hl, (G _).2.2, oL, ← es, ← er, ← y7, ← y8, ← y9]
      by_cases hd : cv tr tp w Proc.ok = 1
      · rw [if_pos hd, if_pos ⟨hok'.1 hd, rfl⟩]
      · rw [if_neg hd, if_neg (fun c => hd (hok'.2 c.1))]
  · -- a scan READ: before the process times
    have hSD := sd_local C.hH C.OS
    have hS := Scan.SLocal.of_sd hSD
    obtain ⟨-, hkS, -, hcol⟩ := Scan.shape_all hS hf' hq' 19 (by omega)
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
    have hv := hyp _ ho hot
    simp only at hv
    rw [(Mem.row_read C.hM hr hrd).1, hv]
    unfold simσ
    rw [stAt_none _ _ _ _ _ _ _ (entAt_lt C.hL C.hHt C.I (show t < T0 by unfold T0; omega))]

/-- **Every op on τ's addresses reads the simulation.** -/
theorem mem_reads : ∀ o ∈ memOpsQ tr tm (QT (cv tr tp f Proc.tau) P.n),
    o.vin = simσ (cv tr tp f Proc.tau) P.n allowed tr tp f m st o.t o.a :=
  mem_reads_simQ C.hH C.O.mem C.O.cmp (initOnce_of C.hτ C.PO.n64 C.hV)
    (mem_timeQ C.hH C.O C.OS C.OO C.PS C.htau C.hf C.hk C.hc C.I C.SP C.PO C.PO.n64)
    C.frame C.step_ok (fun a hq => by
      unfold simσ
      rw [if_pos hq]
      exact (memInit_tau C.hH C.O.mem C.hτ C.PO.n64 C.hB C.hV hq).symm)

/-- **`EntryMem` for every entry of the instance.** -/
theorem entry_mem {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    EntryMem P.n allowed (reqsOf P) tr tp f st i j := by
  have hn := C.PO.n64
  obtain ⟨es, er, hs, hr', hl, -⟩ := C.ent hi hj
  obtain ⟨⟨o7, m7, t7, a7, v7⟩, ⟨o8, m8, t8, a8, v8⟩, ⟨o9, m9, t9, a9, v9⟩⟩ := C.slot_ops hi hj
  have y7 := C.mem_reads o7 m7
  have y8 := C.mem_reads o8 m8
  have y9 := C.mem_reads o9 m9
  rw [v7, t7, a7] at y7; rw [v8, t8, a8] at y8; rw [v9, t9, a9] at y9
  unfold simσ at y7 y8 y9
  rw [if_pos (QT_snd hn hs), rd_snd _ hn hs] at y7
  rw [if_pos (QT_rcv hn hr'), rd_rcv _ hn hr'] at y8
  rw [if_pos (QT_link hn hl), rd_link _ hn hl] at y9
  have hA := stAt_slot (n := P.n) (allowed := allowed) (reqs := reqsOf P) (st := st) C.hL C.hHt C.I
    (fun i hi j hj => by
      obtain ⟨⟨rest, h1, -⟩, h2, -⟩ := entry_inc C.hH C.O C.OS C.SP C.PO C.I rfl hi hj
      exact ⟨⟨rest, h1⟩, h2⟩) i hi j (Nat.le_of_lt hj)
  simp only [Arr, Prod.mk.injEq] at hA
  obtain ⟨hsb, hrb, hal⟩ := hA
  have hB := stAt_bnd P.n allowed tr tp f m st C.hB (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
  obtain ⟨gS, gR, gL, -, -, oL⟩ := grant_sem C.hH C.O C.OS C.I C.hτ C.SP C.PO C.hB C.hV hi hj
    (by rw [y7]; exact (hB _).1) (by rw [y8]; exact (hB _).2.1) (by rw [y9]; exact (hB _).2.2)
  exact ⟨by rw [y7, hsb, es], by rw [y8, hrb, er], by rw [y9, hal], gS, gR, gL, oL⟩

/-- **`ReadOk` for the instance.** -/
theorem read_ok : ReadOk AP tr pub (cv tr tp f Proc.tau) (reqsOf P).length st := by
  intro l t v hl hv h1 h2 hmem
  have hR := reqsOf_length C.PO
  have := C.PO.len16
  have hn := C.PO.n64
  have hτ := C.hτ
  have hc := List.count_pos_iff.2 hmem
  rw [sopSent_count, ← mem_ops_eq_sent C.hH C.O.mem _ (Or.inl (by simp [OP_READ]; rfl))] at hc
  obtain ⟨r, hr, hm⟩ := List.mem_filterMap.1 (List.count_pos_iff.1 hc)
  have hr' := List.mem_range.1 hr
  by_cases hc' : cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0
  · simp only [hc'.1, hc'.2, and_self, ↓reduceIte, Option.some.injEq] at hm
    have hm' := hm
    rw [Mem.opMsg_eq] at hm'
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hm'
    obtain ⟨ea, et, -, evin, -⟩ := hm'
    have ha := cell_ofNat ea (by unfold addrOf; omega)
    have ht := cell_ofNat et (by omega)
    have hvin := cell_ofNat evin hv
    obtain ⟨f0, hf0r, hff, eaddr, -, -⟩ := seg_init C.hM hr' hc'.1
    have hq0 := init_row_qt C.hH C.O.mem hτ hn C.hV (by omega) hff
      (by rw [← eaddr, ha]; unfold addrOf; omega) (by rw [← eaddr, ha]; unfold addrOf; omega)
    rw [← eaddr] at hq0
    have hll : l < P.n * P.n := by
      rw [ha] at hq0
      have := (QT_iff.1 hq0).2
      rw [show addrOf (cv tr tp f Proc.tau) 0 l - cv tr tp f Proc.tau * 16384 = l by unfold addrOf; omega] at this
      simp only [idxOk, decide_eq_true_eq] at this
      omega
    have y := C.mem_reads _ (mem_memOpsQ.2 ⟨memOps_mem hr' hc'.1 hc'.2, hq0⟩)
    simp only at y
    rw [hvin, ht, ha] at y
    unfold simσ at y
    rw [if_pos (QT_link hn hll), rd_link _ hn hll, stAt_pre C.hL C.hHt C.I t (by unfold T0; omega)] at y
    exact y
  · simp [hc'] at hm

end MemCtx

end

end ZkFormal.NearV3.Sched
