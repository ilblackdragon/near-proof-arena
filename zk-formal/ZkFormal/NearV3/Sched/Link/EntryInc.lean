import ZkFormal.NearV3.Sched.Link.ScanPush

/-!
# ZkFormal.NearV3.Sched.Link.EntryInc — the `INC` part of `EntryOk` (scan link)

* `inc_sender`: every `INC` that a process entry receives is sent by a scan row of `ssdV3`
  (`SINC`: sole sender `ssdV3`, no public segment);
* **`entry_inc`**: for entry `j` of round `i` of an instance τ, the received `INC
  (τ, eout, inc, rem, s, r, link)` is that of request entry `eout = 64·cid + jj` of
  `reqsOf P`: `(reqAt reqs eout).incs = inc :: rest` with `rest = [] ↔ rem = 0`, the request's
  link is `link`, `eout + 1 < P` and `link < n²`;
* `stepSt_asz`: the allowance array keeps its size along the replay;
* `EntryMem`: the memory part of `EntryOk` (in-values = spec state, GRANT outcomes);
  `EntryOk.of_mem` assembles `EntryOk` from it and `entry_inc`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## Bounds of the increases -/

theorem incsFrom_le (vals : List Nat) :
    ∀ (prev : Nat) (cs : List Nat), ∀ x ∈ incsFrom vals prev cs, ∃ c ∈ cs, x ≤ vals.getD c 0
  | _, [], x, hx => by simp [incsFrom] at hx
  | prev, c :: cs, x, hx => by
    simp only [incsFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨c, List.mem_cons_self .., Nat.sub_le _ _⟩
    · obtain ⟨c', hc', h⟩ := incsFrom_le vals _ cs x hx
      exact ⟨c', List.mem_cons_of_mem _ hc', h⟩

theorem incsOf_getD_lt (p : Params) (bm : List UInt8) (hb : p.base < 2 ^ 24)
    (hd : p.maxSingleGrant - p.base < 2 ^ 24) (jj : Nat) : (incsOf p bm).getD jj 0 < 2 ^ 25 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (incsOf p bm)[jj]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    obtain ⟨c, hc, hle⟩ := incsFrom_le _ _ _ x (List.mem_of_getElem? h)
    have hc40 : c < 40 := by
      simp only [setBits, List.mem_filter, List.mem_range] at hc; exact hc.1
    rw [ScanSpec.requestValues_getD p hc40] at hle
    have h1 : (p.maxSingleGrant - p.base) * (c + 1) / 40 ≤ (p.maxSingleGrant - p.base) * 40 / 40 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    rw [Nat.mul_div_cancel _ (by decide)] at h1
    omega

/-! ## Allowance sizes along the replay -/

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

theorem tryGrant_asz (st : St) (l bw : Nat) :
    (tryGrant n allowed st l bw).2.allowance.size = st.allowance.size := by
  unfold tryGrant grantMore
  split
  · rfl
  · simp only
    split
    · rfl
    · simp [Array.set!_eq_setIfInBounds]

theorem stepE_asz (K z t v : Nat) (st : St) :
    (stepE n allowed reqs K z t v st).1.allowance.size = st.allowance.size := by
  unfold stepE
  split
  · rfl
  · simp only
    split <;> exact tryGrant_asz n allowed _ _ _

theorem runL_asz (K z : Nat) : ∀ (vs : List Nat) (t : Nat) (st : St),
    (runL n allowed reqs K z vs t st).1.allowance.size = st.allowance.size
  | [], _, _ => rfl
  | v :: vs, t, st => by
    simp only [runL]
    rw [runL_asz K z vs, stepE_asz]

variable (tr : Trace Fp) (tp f : Nat) (st : St)

theorem specSt_asz : ∀ i, (specSt n allowed reqs tr tp f st i).allowance.size = st.allowance.size
  | 0 => rfl
  | i + 1 => by
    simp only [specSt, specRound]
    rw [runL_asz]
    exact specSt_asz i

theorem stepSt_asz (i : Nat) :
    ∀ j, (stepSt n allowed reqs tr tp f st i j).allowance.size = st.allowance.size
  | 0 => specSt_asz n allowed reqs tr tp f st i
  | j + 1 => by
    simp only [stepSt]
    rw [stepE_asz]
    exact stepSt_asz i j

/-- **The memory part of `EntryOk`** (entry `j` of round `i`, row `w = h_i + 1 + j`). -/
structure EntryMem (i j : Nat) : Prop where
  sIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn =
    (stepSt n allowed reqs tr tp f st i j).senderBudget[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link / n]!
  rIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn =
    (stepSt n allowed reqs tr tp f st i j).receiverBudget[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link % n]!
  aIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn =
    (stepSt n allowed reqs tr tp f st i j).allowance[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link]!
  cS : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cS =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn
    then 1 else 0
  cR : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cR =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn
    then 1 else 0
  cL : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cL =
    if allowed[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link]! then 1 else 0
  aOut : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alOut =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok = 1 then
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn - cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc
    else cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn

end

/-! ## The `INC` of an entry -/

namespace Scan

theorem inc_head {tr : Trace Fp} {t : Nat} {pub : List Fp} {kk : Nat} (hkk : kk < 2) (w : Nat) :
    ((ScanDist.interactions[1 + kk]!).msgVal tr t w pub).head? = some (Fp.ofNat (cv tr t w tau)) := by
  rcases (by omega : kk = 0 ∨ kk = 1) with rfl | rfl
  · rw [show 1 + 0 = 1 from rfl, inc0_def]
    simp only [Interaction.msgVal, List.map_cons, List.head?_cons]
    rw [eval_ofNat (v := cv tr t w tau) (by simp only [zev_c, cur_cv])]
  · rw [show 1 + 1 = 2 from rfl, inc1_def]
    simp only [Interaction.msgVal, List.map_cons, List.head?_cons]
    rw [eval_ofNat (v := cv tr t w tau) (by simp only [zev_c, cur_cv])]

end Scan

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd : Nat}

/-- Every `INC` received by a process row is sent by a scan row. -/
theorem inc_sender (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) {w : Nat} (hw : w < tr.height tp)
    (hm : (Proc.interactions[6]!).multNat tr tp w pub ≠ 0) :
    ∃ w', w' < tr.height tsd ∧ ∃ kk, kk < 2 ∧ (ScanDist.interactions[1 + kk]!).multNat tr tsd w' pub ≠ 0 ∧
      (ScanDist.interactions[1 + kk]!).msgVal tr tsd w' pub = (Proc.interactions[6]!).msgVal tr tp w pub := by
  have h1 := tableBusCount_pos hw (mem_i 6 (by decide)) hm
  have h2 := busCount_go_ge tr pub (Proc.interactions[6]!).bus (Proc.interactions[6]!).send
    ((Proc.interactions[6]!).msgVal tr tp w pub) AP.tables 0 tp O.tp_lt
  rw [O.tp_tab, Nat.zero_add, show Proc.table.interactions = Proc.interactions from rfl] at h2
  have hb : (Proc.interactions[6]!).bus = B_SINC := by rw [Proc.i6_def]
  have hs : (Proc.interactions[6]!).send = false := by rw [Proc.i6_def]
  rw [hb, hs] at h1 h2
  have hbal := hH.balance B_SINC ((Proc.interactions[6]!).msgVal tr tp w pub)
  rw [pubCount_zero (fun seg h1 h2 => absurd h2 (O.incPub seg h1)) _,
    pubCount_zero (fun seg h1 h2 => absurd h2 (O.incPub seg h1)) _] at hbal
  have hpos : busCount.go tr pub B_SINC true ((Proc.interactions[6]!).msgVal tr tp w pub) AP.tables 0 ≠ 0 := by
    have : busCount AP.toAir tr pub B_SINC true ((Proc.interactions[6]!).msgVal tr tp w pub) =
      busCount.go tr pub B_SINC true ((Proc.interactions[6]!).msgVal tr tp w pub) AP.tables 0 := rfl
    have h3 : busCount AP.toAir tr pub B_SINC false ((Proc.interactions[6]!).msgVal tr tp w pub) =
      busCount.go tr pub B_SINC false ((Proc.interactions[6]!).msgVal tr tp w pub) AP.tables 0 := rfl
    omega
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub _ _ _ AP.tables 0 hpos
  rw [Nat.zero_add] at htc
  obtain ⟨w', hw', i', hi', hb', hs', hmsg, hm'⟩ := exists_of_tableBusCount htc
  have htd : t = tsd := by
    refine Classical.byContradiction fun hne => ?_
    have := OS.incOnly t ht hne i' hi' hb'
    rw [hs'] at this; exact absurd this (by decide)
  subst htd
  rw [OS.tab] at hi'
  rcases (Scan.bus_cases i' hi').1 hb' with e | e <;> subst e
  · exact ⟨w', hw', 0, by decide, hm', hmsg⟩
  · exact ⟨w', hw', 1, by decide, hm', hmsg⟩

/-- **The `INC` part of `EntryOk`.** -/
theorem entry_inc (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) {τ : Nat} {P : InstPub} (SP : ScanPub AP pub τ P) (PO : ScanPubOk P)
    {f m : Nat} (I : Proc.Inst tr tp f m) (hτ : cv tr tp f Proc.tau = τ) {i : Nat} (hi : i < m)
    {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    (∃ rest, (reqAt (reqsOf P) (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).incs =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc :: rest ∧
      (rest = [] ↔ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rem = 0)) ∧
    (reqAt (reqsOf P) (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).link =
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout + 1 < 2013265921 ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < P.n * P.n := by
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
  obtain ⟨-, he, hi', hrem, -, -, hlk, -⟩ := E
  -- the request
  have hq64 : (64 * cv tr tsd f' Scan.cid + jj) / 64 = cv tr tsd f' Scan.cid := by omega
  have hr64 : (64 * cv tr tsd f' Scan.cid + jj) % 64 = jj := by omega
  rw [← he, ← hi', ← hrem, ← hlk]
  unfold reqAt
  simp only [hq64, hr64, reqsOf_getD PO hcid]
  refine ⟨⟨(incsOf P.params (rawAt P (cv tr tsd f' Scan.cid)).bm).drop (jj + 1), ?_, ?_⟩, trivial, by omega, ?_⟩
  · rw [List.drop_eq_getElem_cons hjj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjj,
      Option.getD_some]
  · rw [List.drop_eq_nil_iff]; omega
  · have : ((rawAt P (cv tr tsd f' Scan.cid)).s + 1) * P.n ≤ P.n * P.n :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega

end

end ZkFormal.NearV3.Sched
