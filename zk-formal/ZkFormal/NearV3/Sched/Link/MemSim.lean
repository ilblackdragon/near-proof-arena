import ZkFormal.NearV3.Sched.Link.MemTau

/-!
# ZkFormal.NearV3.Sched.Link.MemSim — the simulated memory of an instance (stage B step 2)

* `entry_sr`: an entry's `INC` has `s·n + r = link`, `s, r < n`, `inc < 2^25` (scan link);
* `mem_grant`: a memory GRANT row with `vin < 2^29` (the comparator gives `sf = [inc ≤ vin]`):
  condition `c = isL ? al : [inc ≤ vin]`, `ok ≤ c`, `v = ok ? vin − inc : vin`;
* `seg_init`: an active row carries `al`, `isL` from the `INIT` row of its segment;
* the `isL` flag of the `INIT` rows of τ's addresses is `[link address]` (`init_row_isL`, from
  `InitVals`: the `INIT` row's `c = isL` is in the message);
* **`grant_sem`**: for an entry of the instance with in-values `≤ 4,500,000`, the GRANT outcomes
  `cS = [inc ≤ sbIn]`, `cR = [inc ≤ rbIn]`, `cL = allowed[link]`, and the out-values
  `sbOut, rbOut, alOut = ok ? in − inc : in`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd : Nat}

/-- **The `INC` of an entry**: sender, receiver, link and the increase bound. -/
theorem entry_sr (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub} (SP : ScanPub AP pub τ P) (PO : ScanPubOk P)
    {f m : Nat} (I : Proc.Inst tr tp f m) (hτ : cv tr tp f Proc.tau = τ) {i : Nat} (hi : i < m)
    {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s * P.n + cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link ∧
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s < P.n ∧
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r < P.n ∧
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc < 2 ^ 25 := by
  have hL := pLocal_of hH O.tp_lt O.tp_tab
  have hHt := proc_height hH O.tp_lt O.tp_tab
  have hSD := sd_local hH OS
  have hS := Scan.SLocal.of_sd hSD
  obtain ⟨⟨hh0, hh, ht, -⟩, -⟩ := I.hdr i hi
  obtain ⟨-, -, -, -, -, -, hm6, hmsg6, -⟩ := Proc.ent_msgs hL hHt hh0 hh hj
  have hw : Proc.hdrAt tr tp f i + 1 + j < tr.height tp :=
    ((Proc.round_shape hL hHt hh0 hh).2.2 j hj).1.1
  generalize Proc.hdrAt tr tp f i + 1 + j = w at hw hm6 hmsg6 ⊢
  obtain ⟨w', hw', kk, hkk, hm', hmsg'⟩ := inc_sender hH O OS hw (by rw [hm6]; decide)
  -- the scan row lies in a request block of τ
  have F := Scan.row_flags hS hw'
  have hkS : cv tr tsd w' Scan.kS = 1 := by
    have b := Scan.bool_of hS hw' (x := Scan.kS) (by simp [Scan.boolCols, Scan.sharedBool])
    rcases (by omega : kk = 0 ∨ kk = 1) with rfl | rfl
    · have := Scan.mult_one (by rw [Scan.inc0_def]) hm'; omega
    · have := Scan.mult_one (by rw [show 1 + 1 = 2 from rfl, Scan.inc1_def]) hm'; omega
  obtain ⟨f', hf1, hf2, hq⟩ := Scan.kS_block hSD w' hw' hkS
  have hf' : f' < tr.height tsd := by omega
  have hR := Scan.shape_all hS hf' hq (w' - f') (by omega)
  unfold Scan.RS at hR
  rw [show f' + (w' - f') = w' by omega] at hR
  have htf : cv tr tsd f' Scan.tau = τ := by
    have e := congrArg List.head? hmsg'
    rw [Scan.inc_head hkk, hmsg6] at e
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at e
    rw [← hR.2.2.2 Scan.tau (by simp [Scan.reqCols]), (Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)).1 e,
      ht, hτ]
  have hτP : τ < 2013265921 := htf ▸ cv_lt _ _
  have B := blk_ok hH OS SP PO hf' hq htf
  obtain ⟨-, -, hinc, -⟩ := Scan.scan_request hS hf' hq B.bm B.base B.dd PO.base24 PO.d24
  have hinc' := hinc (w' - f') (by omega) kk hkk (by rw [show f' + (w' - f') = w' by omega]; exact hm')
  rw [show f' + (w' - f') = w' by omega] at hinc'
  obtain ⟨-, hjj, hmsg⟩ := hinc'
  generalize (ScanSpec.stAt (requestValues P.params) (rawAt P (cv tr tsd f' Scan.cid)).bm P.params.base
    (2 * (w' - f') + kk)).2 = jj at hjj hmsg
  rw [hmsg, hmsg6, Scan.incMsg, htf] at hmsg'
  -- bounds
  have hcid := B.lt
  have l16 := PO.len16
  obtain ⟨hs, hr, hne⟩ := PO.raw _ (rawAt_mem hcid)
  have hn := PO.n64
  have hl40 := incsOf_length_le P.params (rawAt P (cv tr tsd f' Scan.cid)).bm
  have hig := incsOf_getD_lt P.params (rawAt P (cv tr tsd f' Scan.cid)).bm PO.base24 PO.d24 jj
  have hsn : (rawAt P (cv tr tsd f' Scan.cid)).s * P.n ≤ 64 * 64 := Nat.mul_le_mul (by omega) hn
  rw [B.s, B.r, B.link] at hmsg'
  have E := ofNat_list_inj (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h <;> subst h <;> omega)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h <;> subst h <;> exact cv_lt _ _) hmsg'
  simp only [List.cons.injEq] at E
  obtain ⟨-, -, hi', -, hs', hr', hlk, -⟩ := E
  rw [← hs', ← hr', ← hlk, ← hi']
  exact ⟨rfl, hs, hr, hig⟩

end

/-! ## Memory GRANT rows -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem Mem.iSf_mem : Mem.iSf ∈ Mem.interactions := by rw [Mem.interactions_eq]; simp

/-- **A memory GRANT row** with `vin < 2^29`, `inc ≤ 2^29`. -/
theorem mem_grant (hH : HoldsP AP pub tr) {tm tc : Nat} (hM : MemOwn AP tm) (hC : CmpOwn AP tc)
    {r : Nat} (hr : r < tr.height tm) (hg : cv tr tm r Mem.isGr = 1)
    (hv : cv tr tm r Mem.vin < 2 ^ 29) (hi : cv tr tm r Mem.inc ≤ 2 ^ 29) :
    cv tr tm r Mem.cc = (if cv tr tm r Mem.isL = 1 then cv tr tm r Mem.al
      else if cv tr tm r Mem.inc ≤ cv tr tm r Mem.vin then 1 else 0) ∧
    cv tr tm r Mem.ok ≤ cv tr tm r Mem.cc ∧
    cv tr tm r Mem.v = (if cv tr tm r Mem.ok = 1 then cv tr tm r Mem.vin - cv tr tm r Mem.inc
      else cv tr tm r Mem.vin) := by
  have hL := mLocal_of hH hM
  obtain ⟨-, -, -, -, -, -, -, hO, -, hSf, -, -⟩ := Mem.row_flags hL hr
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := Mem.row_grant hL hr hg
  have hmem : Mem.iSf ∈ AP.tables[tm]!.interactions := by rw [hM.tab]; exact Mem.iSf_mem
  have hmult : Mem.iSf.multNat tr tm r pub ≠ 0 := by
    rw [Mem.multNat_c (i := Mem.iSf) rfl, if_pos hg]; decide
  have hsf : cv tr tm r Mem.sf = if cv tr tm r Mem.inc ≤ cv tr tm r Mem.vin then 1 else 0 := by
    rcases cmp_sound_le hH hC hM.lt hr hmem rfl rfl hmult (x := tr.cell tm r Mem.vin)
        (y := tr.cell tm r Mem.inc) (b := tr.cell tm r Mem.sf) rfl hv hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : cv tr tm r Mem.sf = 1 := by unfold cv; rw [h1]; rfl
      rw [this, if_pos (show cv tr tm r Mem.inc ≤ cv tr tm r Mem.vin from h2)]
    · have : cv tr tm r Mem.sf = 0 := by unfold cv; rw [h1]; rfl
      rw [this, if_neg (by unfold cv; omega)]
  refine ⟨by rw [g1, hsf], g2, ?_⟩
  have lt := cv_lt (tr := tr) (t := tm) r Mem.v
  split
  · next ho =>
    by_cases hc : cv tr tm r Mem.inc ≤ cv tr tm r Mem.vin
    · have := g4 ho (by rw [hsf, if_pos hc])
      omega
    · rw [g5 ho (by rw [hsf, if_neg hc])]; omega
  · exact g3 (by omega)

/-- **The `INIT` row of a segment** carries `addr`, `al`, `isL` to every row of the segment. -/
theorem seg_init {tm : Nat} (hL : Mem.MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm)
    (ha : cv tr tm r Mem.act = 1) :
    ∃ f, f ≤ r ∧ cv tr tm f Mem.fst = 1 ∧ cv tr tm r Mem.addr = cv tr tm f Mem.addr ∧
      cv tr tm r Mem.al = cv tr tm f Mem.al ∧ cv tr tm r Mem.isL = cv tr tm f Mem.isL := by
  obtain ⟨f, hfr, hff, hact, hrest⟩ := Mem.seg_start hL r hr ha
  have hc : ∀ d, f + d ≤ r → cv tr tm (f + d) Mem.addr = cv tr tm f Mem.addr ∧
      cv tr tm (f + d) Mem.al = cv tr tm f Mem.al ∧ cv tr tm (f + d) Mem.isL = cv tr tm f Mem.isL := by
    intro d
    induction d with
    | zero => intro _; exact ⟨rfl, rfl, rfl⟩
    | succ d ih =>
      intro hd
      have hl := (hrest (f + d + 1) (by omega) (by omega)).2
      simp only [Nat.add_sub_cancel] at hl
      have N := Mem.row_next hL (r := f + d) (by omega) (hact (f + d) (by omega) (by omega)) hl
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      rw [show f + (d + 1) = f + d + 1 by omega]
      exact ⟨N.2.2.1.trans i1, N.2.2.2.2.2.2.1.trans i2, N.2.2.2.2.2.2.2.trans i3⟩
  have := hc (r - f) (by omega)
  rw [show f + (r - f) = r by omega] at this
  exact ⟨f, hfr, hff, this⟩

/-- A memory row receiving a GRANT message. -/
theorem row_of_msg {tm : Nat} (hL : Mem.MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm)
    (ha : cv tr tm r Mem.act = 1) {a t vi vo ic o cc : Nat}
    (h : Mem.opMsg tr tm pub r = [a, t, OP_GRANT, vi, vo, ic, o, cc].map Fp.ofNat)
    (h1 : a < 2013265921) (h2 : t < 2013265921) (h3 : vi < 2013265921) (h4 : vo < 2013265921)
    (h5 : ic < 2013265921) (h6 : o < 2013265921) (h7 : cc < 2013265921) :
    cv tr tm r Mem.fst = 0 ∧ cv tr tm r Mem.isGr = 1 ∧ cv tr tm r Mem.addr = a ∧
      cv tr tm r Mem.t = t ∧ cv tr tm r Mem.vin = vi ∧ cv tr tm r Mem.v = vo ∧
      cv tr tm r Mem.inc = ic ∧ cv tr tm r Mem.ok = o ∧ cv tr tm r Mem.cc = cc := by
  obtain ⟨-, hF, -, hR, hG, -, -, -, -, -, hsum, -⟩ := Mem.row_flags hL hr
  rw [Mem.opMsg_eq] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h
  have hop := (Proc.ofNat_cv_eq (by omega) (by simp [OP_GRANT])).1 e3
  simp only [OP_GRANT] at hop
  exact ⟨by omega, by omega, cell_ofNat e1 h1, cell_ofNat e2 h2, cell_ofNat e4 h3, cell_ofNat e5 h4,
    cell_ofNat e6 h5, cell_ofNat e7 h6, cell_ofNat e8 h7⟩

end

/-! ## The GRANTs of an entry -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd : Nat}

/-- The memory row receiving GRANT `k` of a process row. -/
theorem grant_row (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg) {w : Nat}
    (hw : w < tr.height tp) {k : Nat} (hk : k = 7 ∨ k = 8 ∨ k = 9)
    (hm : (Proc.interactions[k]!).multNat tr tp w pub = 1) :
    ∃ r, r < tr.height tm ∧ cv tr tm r Mem.act = 1 ∧
      Mem.opMsg tr tm pub r = (Proc.interactions[k]!).msgVal tr tp w pub := by
  have hi : Proc.interactions[k]! ∈ AP.tables[tp]!.interactions := by
    rw [O.tp_tab]; exact mem_i k (by omega)
  have hb : (Proc.interactions[k]!).bus = B_SOP := by rcases hk with rfl | rfl | rfl <;> rfl
  have hs : (Proc.interactions[k]!).send = true := by rcases hk with rfl | rfl | rfl <;> rfl
  exact mem_sent_row hH O.mem O.tp_lt hw hi hb hs (by rw [hm]; decide)

/-- The three GRANT rows of entry `j` of round `i`: addresses, time, in/out values. -/
theorem grant_rows (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    {f m : Nat} (I : Proc.Inst tr tp f m) (hτ : cv tr tp f Proc.tau < 256)
    {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)
    (hs : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s < 64)
    (hr : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r < 64)
    (hl : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < 4096) :
    ∀ k, (k = 7 ∨ k = 8 ∨ k = 9) → ∃ rw, rw < tr.height tm ∧ cv tr tm rw Mem.act = 1 ∧
      cv tr tm rw Mem.fst = 0 ∧ cv tr tm rw Mem.isGr = 1 ∧
      cv tr tm rw Mem.addr = (if k = 7 then addrOf (cv tr tp f Proc.tau) 1 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s)
        else if k = 8 then addrOf (cv tr tp f Proc.tau) 2 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.r)
        else addrOf (cv tr tp f Proc.tau) 0 (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link)) ∧
      cv tr tm rw Mem.t = cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j ∧
      cv tr tm rw Mem.vin = cv tr tp (Proc.hdrAt tr tp f i + 1 + j)
        (if k = 7 then Proc.sbIn else if k = 8 then Proc.rbIn else Proc.alIn) ∧
      cv tr tm rw Mem.v = cv tr tp (Proc.hdrAt tr tp f i + 1 + j)
        (if k = 7 then Proc.sbOut else if k = 8 then Proc.rbOut else Proc.alOut) ∧
      cv tr tm rw Mem.inc = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ∧
      cv tr tm rw Mem.ok = cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok ∧
      cv tr tm rw Mem.cc = cv tr tp (Proc.hdrAt tr tp f i + 1 + j)
        (if k = 7 then Proc.cS else if k = 8 then Proc.cR else Proc.cL) := by
  have hL := mLocal_of hH O.mem
  have hLp := pLocal_of hH O.tp_lt O.tp_tab
  have hHt := proc_height hH O.tp_lt O.tp_tab
  obtain ⟨⟨hh0, hh, ht, -⟩, hTb⟩ := I.hdr i hi
  obtain ⟨-, -, -, -, -, -, -, -, m7, e7, m8, e8, m9, e9, -⟩ := Proc.ent_msgs hLp hHt hh0 hh hj
  have hw := ((Proc.round_shape hLp hHt hh0 hh).2.2 j hj).1.1
  rw [ht] at e7 e8 e9
  have hT : cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j < 2013265921 := by unfold T0 at hTb; omega
  intro k hk
  obtain ⟨rw, hrw, ha, hm⟩ := grant_row hH O hw hk (by rcases hk with rfl | rfl | rfl <;> assumption)
  have lt := fun x => cv_lt (tr := tr) (t := tp) (Proc.hdrAt tr tp f i + 1 + j) x
  rcases hk with rfl | rfl | rfl
  · rw [e7] at hm
    have := row_of_msg hL hrw ha hm (by unfold addrOf; omega) hT (lt _) (lt _) (lt _) (lt _) (lt _)
    exact ⟨rw, hrw, ha, this⟩
  · rw [e8] at hm
    have := row_of_msg hL hrw ha hm (by unfold addrOf; omega) hT (lt _) (lt _) (lt _) (lt _) (lt _)
    exact ⟨rw, hrw, ha, this⟩
  · rw [e9] at hm
    have := row_of_msg hL hrw ha hm (by unfold addrOf; omega) hT (lt _) (lt _) (lt _) (lt _) (lt _)
    exact ⟨rw, hrw, ha, this⟩

/-- **The GRANT outcomes of an entry** (in-values `≤ 4,500,000`). -/
theorem grant_sem (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) {f m : Nat} (I : Proc.Inst tr tp f m) (hτ : cv tr tp f Proc.tau < 256)
    {P : InstPub} (SP : ScanPub AP pub (cv tr tp f Proc.tau) P) (PO : ScanPubOk P)
    {allowed : Array Bool} {st : St} (hB : ABnd 4500000 st)
    (hV : InitVals AP tr pub (cv tr tp f Proc.tau) P.n allowed st)
    {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)
    (hSb : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn ≤ 4500000)
    (hRb : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn ≤ 4500000)
    (hAl : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn ≤ 4500000) :
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cS =
      (if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn
        then 1 else 0) ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cR =
      (if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn
        then 1 else 0) ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cL =
      (if allowed[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link]! then 1 else 0) ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbOut =
      (if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok = 1 then
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn - cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc
      else cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn) ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbOut =
      (if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok = 1 then
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn - cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc
      else cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn) ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alOut =
      (if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok = 1 then
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn - cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc
      else cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn) := by
  have hL := mLocal_of hH O.mem
  have hn := PO.n64
  obtain ⟨hsr, hs, hr, hinc⟩ := entry_sr hH O OS SP PO I rfl hi hj
  have hl : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < P.n * P.n := by
    have : (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.s + 1) * P.n ≤ P.n * P.n :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; omega
  have hnn := Nat.mul_le_mul hn hn
  have G := grant_rows hH O I hτ hi hj (by omega) (by omega) (by omega)
  generalize Proc.hdrAt tr tp f i + 1 + j = w at *
  generalize hτd : cv tr tp f Proc.tau = τ at *
  -- the INIT data of a GRANT row's address
  have initOf : ∀ rw, rw < tr.height tm → cv tr tm rw Mem.act = 1 → QT τ P.n (cv tr tm rw Mem.addr) = true →
      cv tr tm rw Mem.isL = (if cv tr tm rw Mem.addr - τ * 16384 < 4096 then 1 else 0) ∧
      (cv tr tm rw Mem.addr - τ * 16384 < 4096 → cv tr tm rw Mem.al =
        if allowed[cv tr tm rw Mem.addr - τ * 16384]! then 1 else 0) := by
    intro rw hrw ha hq
    obtain ⟨f0, hf0r, hff, ea, eal, eil⟩ := seg_init hL hrw ha
    have hf0 : f0 < tr.height tm := by omega
    rw [ea] at hq ⊢
    refine ⟨by rw [eil]; exact init_row_isL hH O.mem hτ hn hV hf0 hff hq, fun hlt => ?_⟩
    rw [eal, ← (Mem.row_init hL hf0 hff).2.1, (init_row_vals hH O.mem hτ hn hB hV hf0 hff hq).2, if_pos hlt]
  obtain ⟨r7, h7, a7, -, g7, ad7, -, vi7, vo7, ic7, o7, c7⟩ := G 7 (Or.inl rfl)
  obtain ⟨r8, h8, a8, -, g8, ad8, -, vi8, vo8, ic8, o8, c8⟩ := G 8 (Or.inr (Or.inl rfl))
  obtain ⟨r9, h9, a9, -, g9, ad9, -, vi9, vo9, ic9, o9, c9⟩ := G 9 (Or.inr (Or.inr rfl))
  simp only [if_true, show (8 : Nat) ≠ 7 from by decide, show (9 : Nat) ≠ 7 from by decide,
    show (9 : Nat) ≠ 8 from by decide, if_false] at ad7 vi7 vo7 c7 ad8 vi8 vo8 c8 ad9 vi9 vo9 c9
  obtain ⟨i7, -⟩ := initOf r7 h7 a7 (by rw [ad7]; exact QT_snd hn hs)
  obtain ⟨i8, -⟩ := initOf r8 h8 a8 (by rw [ad8]; exact QT_rcv hn hr)
  obtain ⟨i9, al9⟩ := initOf r9 h9 a9 (by rw [ad9]; exact QT_link hn hl)
  rw [ad7, show addrOf τ 1 (cv tr tp w Proc.s) - τ * 16384 = 4096 + cv tr tp w Proc.s by
    unfold addrOf; omega, if_neg (by omega)] at i7
  rw [ad8, show addrOf τ 2 (cv tr tp w Proc.r) - τ * 16384 = 8192 + cv tr tp w Proc.r by
    unfold addrOf; omega, if_neg (by omega)] at i8
  have e9 : addrOf τ 0 (cv tr tp w Proc.link) - τ * 16384 = cv tr tp w Proc.link := by unfold addrOf; omega
  rw [ad9, e9, if_pos (by omega)] at i9
  rw [ad9, e9] at al9
  have al9' := al9 (by omega)
  obtain ⟨k7, -, v7⟩ := mem_grant hH O.mem O.cmp h7 g7 (by omega) (by omega)
  obtain ⟨k8, -, v8⟩ := mem_grant hH O.mem O.cmp h8 g8 (by omega) (by omega)
  obtain ⟨k9, -, v9⟩ := mem_grant hH O.mem O.cmp h9 g9 (by omega) (by omega)
  rw [i7, vi7, ic7] at k7
  rw [i8, vi8, ic8] at k8
  rw [i9, if_pos rfl, al9'] at k9
  rw [vo7, o7, vi7, ic7] at v7
  rw [vo8, o8, vi8, ic8] at v8
  rw [vo9, o9, vi9, ic9] at v9
  rw [← c7, k7, ← c8, k8, ← c9, k9]
  simp only [show (0 : Nat) ≠ 1 from by decide, if_false]
  exact ⟨trivial, trivial, trivial, v7, v8, v9⟩

end

end ZkFormal.NearV3.Sched
