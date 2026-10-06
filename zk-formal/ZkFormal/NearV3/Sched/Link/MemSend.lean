import ZkFormal.NearV3.Sched.Link.MemQ
import ZkFormal.NearV3.Sched.Link.EntryLink
import ZkFormal.NearV3.Sched.Tables.Codec

/-!
# ZkFormal.NearV3.Sched.Link.MemSend — the `SOP` op senders on the addresses of an instance

Stage B step 2. The memory ops (op 1 = READ, op 2 = GRANT) on the addresses of instance τ
(`addrOf τ kind idx`, `τ·2^14 ≤ a < (τ+1)·2^14`) are characterised from the senders' views:

* `OpOwn`: only `sprV3` (`tp`), `ssdV3` (`tsd`) and `schV3` (`tcd`) send on `SOP`;
* `ParSmall` (**public data**, prepD0): every public raw-request record `(τ', 2, …, s, r)` has
  `τ' < 256` and `s, r < 64`; every scan-param record `(τ', 1, …, n, 0, 0)` has `n ≤ 64`;
* `blk_small`: a scan request block (of any instance) has `τ' < 256`, `s, r < 64`,
  `link < 4096`; `ent_small`: so has the `INC` of every process entry (`SINC` balance);
* the codec only sends `INIT`s (op 0), the distribute rows of `ssdV3` too (op `kS = 0`);
* **`op_sent`**: every op message sent on `SOP` with an address in τ's range is a process
  GRANT (`interactions[7..9]`) of an entry row of the instance (`ent_iff`), or the READ of a
  τ request block (`ssdV3` row `f + 19`); every other sender's address lies in another range
  (`τ' ≠ τ`, `τ' < 256`, index `< 2^14`);
* `tauAddrs τ n` / `QT τ n`: the addresses of instance τ with `n` participants (links `< n²`,
  senders and receivers `< n`); **`op_row`**: the same for the memory rows on these
  addresses, and **`mem_timeQ`**: their times are `< 2^29` (process times `< T0 + 2^22`, scan
  times `≤ 2^16`, `INIT` at 0).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## Ownership and public data -/

/-- Only `sprV3` (`tp`), `ssdV3` (`tsd`) and `schV3` (`tcd`) send on `SOP` (STATUS §6.1). -/
structure OpOwn (AP : AirP) (tp tsd tcd : Nat) : Prop where
  lt : tcd < AP.tables.length
  tab : AP.tables[tcd]! = Codec.table
  only : ∀ t, t < AP.tables.length → t ≠ tp → t ≠ tsd → t ≠ tcd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SOP → i.send = false

/-- **Public data** (prepD0 renders these natively): the public raw-request records have
`τ < 256` and `s, r < 64`; the public scan-param records have `n ≤ 64`. -/
structure ParSmall (AP : AirP) (pub : List Fp) : Prop where
  raw : ∀ M : List Fp, 1 ≤ pubCount AP pub B_SPAR true M → M[1]? = some (Fp.ofNat PT_RAW) →
    (M.getD 0 0).toNat < 256 ∧ (M.getD 9 0).toNat < 64 ∧ (M.getD 10 0).toNat < 64
  scan : ∀ M : List Fp, 1 ≤ pubCount AP pub B_SPAR true M → M[1]? = some (Fp.ofNat PT_SCAN) →
    (M.getD 8 0).toNat ≤ 64

/-! ## Generic messages -/

theorem toNat_ofNat_lt' {a : Nat} (h : a < 2013265921) : (Fp.ofNat a).toNat = a := by
  rw [Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt h]

namespace Proc
section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem sop_cases : ∀ i ∈ interactions, i.bus = B_SOP →
    i = interactions[7]! ∨ i = interactions[8]! ∨ i = interactions[9]! := by decide

theorem msg7 (w : Nat) : (interactions[7]!).msgVal tr tp w pub =
    [addrOf (cv tr tp w tau) 1 (cv tr tp w s), cv tr tp w T + cv tr tp w x, OP_GRANT,
      cv tr tp w sbIn, cv tr tp w sbOut, cv tr tp w inc, cv tr tp w ok, cv tr tp w cS].map Fp.ofNat := by
  rw [i7_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aS, ev_tE]

theorem msg8 (w : Nat) : (interactions[8]!).msgVal tr tp w pub =
    [addrOf (cv tr tp w tau) 2 (cv tr tp w r), cv tr tp w T + cv tr tp w x, OP_GRANT,
      cv tr tp w rbIn, cv tr tp w rbOut, cv tr tp w inc, cv tr tp w ok, cv tr tp w cR].map Fp.ofNat := by
  rw [i8_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aR, ev_tE]

theorem msg9 (w : Nat) : (interactions[9]!).msgVal tr tp w pub =
    [addrOf (cv tr tp w tau) 0 (cv tr tp w link), cv tr tp w T + cv tr tp w x, OP_GRANT,
      cv tr tp w alIn, cv tr tp w alOut, cv tr tp w inc, cv tr tp w ok, cv tr tp w cL].map Fp.ofNat := by
  rw [i9_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aL, ev_tE]

theorem msg6 (w : Nat) : (interactions[6]!).msgVal tr tp w pub =
    [cv tr tp w tau, cv tr tp w eout, cv tr tp w inc, cv tr tp w rem, cv tr tp w s, cv tr tp w r,
      cv tr tp w link].map Fp.ofNat := by
  rw [i6_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]

end
end Proc

namespace Scan
section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem ev_c' (w x : Nat) : (c x).eval tr t w pub = Fp.ofNat (cv tr t w x) :=
  eval_ofNat (by simp only [zev_c, cur_cv])

theorem op_msg (w : Nat) : (ScanDist.interactions[4]!).msgVal tr t w pub =
    [16384 * cv tr t w tau + cv tr t w link, cv tr t w cid + cv tr t w kS, cv tr t w kS,
      cv tr t w key, cv tr t w key + cv tr t w bvz, 0, 0, 0].map Fp.ofNat := by
  rw [read_def]
  have e1 : aL.eval tr t w pub = Fp.ofNat (16384 * cv tr t w tau + cv tr t w link) :=
    eval_ofNat (by simp only [aL, zev_add, zev_smul, zev_c, cur_cv]; omega)
  have e2 : (Expr.add (c cid) (c kS)).eval tr t w pub = Fp.ofNat (cv tr t w cid + cv tr t w kS) :=
    eval_ofNat (by simp only [zev_add, zev_c, cur_cv]; omega)
  have e3 : (Expr.add (c key) (c bvz)).eval tr t w pub = Fp.ofNat (cv tr t w key + cv tr t w bvz) :=
    eval_ofNat (by simp only [zev_add, zev_c, cur_cv]; omega)
  have e4 : (k 0).eval tr t w pub = Fp.ofNat 0 := eval_ofNat (by simp [zev_k])
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, e1, e2, e3, e4, ev_c']

theorem inc_msg {kk : Nat} (hkk : kk < 2) (w : Nat) : ∃ X Y Z : Fp,
    (ScanDist.interactions[1 + kk]!).msgVal tr t w pub =
      [Fp.ofNat (cv tr t w tau), X, Y, Z, Fp.ofNat (cv tr t w s), Fp.ofNat (cv tr t w r),
        Fp.ofNat (cv tr t w link)] := by
  rcases (by omega : kk = 0 ∨ kk = 1) with rfl | rfl
  · rw [show 1 + 0 = 1 from rfl, inc0_def]
    exact ⟨eE.eval tr t w pub, (sub val0 (c cur)).eval tr t w pub,
      (sub (sub (c m) (c j)) (k 1)).eval tr t w pub,
      by simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c']⟩
  · rw [show 1 + 1 = 2 from rfl, inc1_def]
    exact ⟨(Expr.add eE (c b0)).eval tr t w pub, (sub val1 (c cm)).eval tr t w pub,
      (sub (sub (sub (c m) (c j)) (c b0)) (k 1)).eval tr t w pub,
      by simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c']⟩

end
end Scan

namespace Codec

theorem sop_cases : ∀ i ∈ interactions, i.bus = B_SOP → i = interactions[10]! := by decide

theorem sop_op {tr : Trace Fp} {t : Nat} {pub : List Fp} (w : Nat) :
    ((interactions[10]!).msgVal tr t w pub)[2]? = some 0 := by
  have : (k OP_INIT).eval tr t w pub = 0 := by
    show Fp.ofNat 0 = 0
    rfl
  simp [interactions, Interaction.msgVal, this]

end Codec

/-! ## Bounds of the scan blocks and of the process entries -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd : Nat}

theorem getD_ofNat_toNat (L : List Nat) (hL : ∀ x ∈ L, x < 2013265921) (i : Nat) :
    ((L.map Fp.ofNat).getD i 0).toNat = L.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : L[i]? with
  | none => rfl
  | some x => exact toNat_ofNat_lt' (hL x (List.mem_of_getElem? h))

/-- **A scan request block** (of any instance) has `τ < 256`, `s, r < 64`, `link < 4096`. -/
theorem blk_small (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (PS : ParSmall AP pub)
    {f : Nat} (hf : f < tr.height tsd) (hq : cv tr tsd f Scan.fQ = 1) :
    cv tr tsd f Scan.tau < 256 ∧ cv tr tsd f Scan.s < 64 ∧ cv tr tsd f Scan.r < 64 ∧
      cv tr tsd f Scan.link < 4096 := by
  have hL := sd_local hH OS
  have hS := Scan.SLocal.of_sd hL
  have h1 := pub_of_row hH OS hf (Scan.par_mult hS hf (Or.inl hq))
  rw [Scan.par_msg] at h1
  have htag := Scan.tag_kS hS hf (Scan.fQ_le_kS hS hf hq)
  have hlt := Scan.parV_lt hS hf
  obtain ⟨a0, a9, a10⟩ := PS.raw _ h1 (by simp [Scan.parV, htag, PT_RAW])
  rw [getD_ofNat_toNat _ hlt] at a0 a9 a10
  simp only [Scan.parV, List.getD_cons_succ, List.getD_cons_zero] at a0 a9 a10
  -- `n` from the section's param row
  obtain ⟨p, hp, hpk, hpc⟩ := Scan.param_of hL f hf hq
  have hpf : p < tr.height tsd := by omega
  have h2 := pub_of_row hH OS hpf (Scan.par_mult hS hpf (Or.inr hpk))
  rw [Scan.par_msg] at h2
  have htagp := Scan.tag_kP hS hpf hpk
  have a8 := PS.scan _ h2 (by simp [Scan.parV, htagp, PT_SCAN])
  rw [getD_ofNat_toNat _ (Scan.parV_lt hS hpf)] at a8
  simp only [Scan.parV, List.getD_cons_succ, List.getD_cons_zero] at a8
  have hnn : cv tr tsd p Scan.chi = cv tr tsd p Scan.nn :=
    Scan.eq_of_gate hS hpf (by simp [Scan.constraints, Scan.shared, Scan.own, Scan.body]) hpk
  have enn : cv tr tsd f Scan.nn ≤ 64 := by
    rw [hpc Scan.nn (by simp [Scan.instCols]), ← hnn]; exact a8
  have hlink := (Scan.row_start hS hf hq).2.2.2.2.2.2.2
  refine ⟨a0, a9, a10, ?_⟩
  have : cv tr tsd f Scan.s * cv tr tsd f Scan.nn ≤ 63 * 64 := Nat.mul_le_mul (by omega) enn
  rw [hlink, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The `INC` of every process entry** (any instance) has `s, r < 64`, `link < 4096`. -/
theorem ent_small (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) (PS : ParSmall AP pub) {w : Nat} (hw : w < tr.height tp)
    (hE : cv tr tp w Proc.kE = 1) :
    cv tr tp w Proc.s < 64 ∧ cv tr tp w Proc.r < 64 ∧ cv tr tp w Proc.link < 4096 := by
  have hm6 : (Proc.interactions[6]!).multNat tr tp w pub ≠ 0 := by
    rw [Mem.multNat_c (by rw [Proc.i6_def]), if_pos hE]; decide
  obtain ⟨w', hw', kk, hkk, hm', hmsg'⟩ := inc_sender hH O OS hw hm6
  have hSD := sd_local hH OS
  have hS := Scan.SLocal.of_sd hSD
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
  obtain ⟨-, b1, b2, b3⟩ := blk_small hH OS PS hf' hq
  obtain ⟨X, Y, Z, hX⟩ := Scan.inc_msg (tr := tr) (t := tsd) (pub := pub) hkk w'
  rw [hX, Proc.msg6] at hmsg'
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg'
  obtain ⟨-, -, -, -, es, er, el, -⟩ := hmsg'
  have es' := (Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)).1 es
  have er' := (Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)).1 er
  have el' := (Proc.ofNat_cv_eq (cv_lt _ _) (cv_lt _ _)).1 el
  rw [hR.2.2.2 Scan.s (by simp [Scan.reqCols])] at es'
  rw [hR.2.2.2 Scan.r (by simp [Scan.reqCols])] at er'
  rw [hR.2.2.2 Scan.link (by simp [Scan.reqCols])] at el'
  omega

end

/-! ## The op senders on the addresses of an instance -/

theorem addr_tau {τ τ' k idx : Nat} (hk : k ≤ 3) (hidx : idx < 4096) {a : Nat}
    (ha : a = addrOf τ' k idx) (h1 : τ * 16384 ≤ a) (h2 : a < τ * 16384 + 16384) : τ' = τ := by
  subst ha; unfold addrOf at *
  rcases Nat.lt_trichotomy τ' τ with e | e | e
  · have := Nat.mul_le_mul_right 16384 (show τ' + 1 ≤ τ by omega); omega
  · exact e
  · have := Nat.mul_le_mul_right 16384 (show τ + 1 ≤ τ' by omega); omega

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd : Nat}

theorem mem_sopSent_row {M : List Fp} (hM : M ∈ sopSent AP tr pub) :
    ∃ t, t < AP.tables.length ∧ ∃ w, w < tr.height t ∧ ∃ i ∈ AP.tables[t]!.interactions,
      i.bus = B_SOP ∧ i.send = true ∧ i.msgVal tr t w pub = M ∧ i.multNat tr t w pub ≠ 0 := by
  have h := List.count_pos_iff.2 hM
  rw [sopSent_count] at h
  unfold busCount at h
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub _ _ M AP.tables 0 (Nat.pos_iff_ne_zero.1 h)
  rw [Nat.zero_add] at htc
  obtain ⟨w, hw, i, hi, hb, hs, hmsg, hm⟩ := exists_of_tableBusCount htc
  exact ⟨t, ht, w, hw, i, hi, hb, hs, hmsg, hm⟩

/-- **The op senders on τ's addresses.** -/
theorem op_sent (hH : HoldsP AP pub tr) (O : SchedOwn AP tp tm tcmp ts tch tg)
    (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd) (PS : ParSmall AP pub)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    {M : List Fp} (hM : M ∈ sopSent AP tr pub) (hop : M[2]? = some 1 ∨ M[2]? = some 2)
    {a : Nat} (ha : M.head? = some (Fp.ofNat a))
    (h1 : cv tr tp f Proc.tau * 16384 ≤ a) (h2 : a < cv tr tp f Proc.tau * 16384 + 16384) :
    (∃ i, i < m ∧ ∃ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr ∧ ∃ k, (k = 7 ∨ k = 8 ∨ k = 9) ∧
        M = (Proc.interactions[k]!).msgVal tr tp (Proc.hdrAt tr tp f i + 1 + j) pub) ∨
      (∃ f', f' < tr.height tsd ∧ cv tr tsd f' Scan.fQ = 1 ∧ cv tr tsd f' Scan.tau = cv tr tp f Proc.tau ∧
        M = (ScanDist.interactions[4]!).msgVal tr tsd (f' + 19) pub) := by
  have hLp := pLocal_of hH O.tp_lt O.tp_tab
  have hHt := proc_height hH O.tp_lt O.tp_tab
  have hτ : cv tr tp f Proc.tau < 256 := htau f hf (Proc.act_of hLp hf (Or.inl hk))
  have ha' : a < 2013265921 := by omega
  obtain ⟨t, ht, w, hw, i, hi, hb, hs, hmsg, hm⟩ := mem_sopSent_row hM
  subst hmsg
  by_cases htp : t = tp
  · subst htp
    rw [O.tp_tab] at hi
    have hE : cv tr t w Proc.kE = 1 := by
      have hmk : i.mult = [c Proc.kE] := by
        rcases Proc.sop_cases i hi hb with e | e | e <;> subst e <;> rfl
      rw [Mem.multNat_c hmk] at hm
      split at hm
      · assumption
      · exact absurd rfl hm
    obtain ⟨hs64, hr64, hl4⟩ := ent_small hH O OS PS hw hE
    have hτw := htau w hw (Proc.act_of hLp hw (Or.inr (Or.inr hE)))
    -- the address and the instance
    have key : ∀ k idx, k ≤ 3 → idx < 4096 →
        (i.msgVal tr t w pub).head? = some (Fp.ofNat (addrOf (cv tr t w Proc.tau) k idx)) →
        cv tr t w Proc.tau = cv tr t f Proc.tau := by
      intro k idx hk3 hidx he
      rw [ha] at he
      have e := (Proc.ofNat_cv_eq ha' (by unfold addrOf; omega)).1 (Option.some.inj he)
      exact addr_tau hk3 hidx e h1 h2
    have hent : cv tr t w Proc.tau = cv tr t f Proc.tau → ∃ i', i' < m ∧ ∃ j, j < cv tr t (Proc.hdrAt tr t f i') Proc.Lr ∧
        w = Proc.hdrAt tr t f i' + 1 + j := fun he =>
      Proc.mem_entRows.1 ((Proc.ent_iff hLp hHt hf hk hc I w).1 ⟨hw, hE, he⟩)
    left
    rcases Proc.sop_cases i hi hb with e | e | e <;> subst e
    · obtain ⟨i', hi', j, hj, rfl⟩ := hent (key 1 (cv tr t w Proc.s) (by omega) (by omega) (by rw [Proc.msg7]; rfl))
      exact ⟨i', hi', j, hj, 7, by omega, rfl⟩
    · obtain ⟨i', hi', j, hj, rfl⟩ := hent (key 2 (cv tr t w Proc.r) (by omega) (by omega) (by rw [Proc.msg8]; rfl))
      exact ⟨i', hi', j, hj, 8, by omega, rfl⟩
    · obtain ⟨i', hi', j, hj, rfl⟩ := hent (key 0 (cv tr t w Proc.link) (by omega) hl4 (by rw [Proc.msg9]; rfl))
      exact ⟨i', hi', j, hj, 9, by omega, rfl⟩
  by_cases htd : t = tsd
  · subst htd
    rw [OS.tab] at hi
    have hi4 := (Scan.bus_cases i hi).2.2 hb
    subst hi4
    have hSD := sd_local hH OS
    have hS := Scan.SLocal.of_sd hSD
    have F := Scan.row_flags hS hw
    have hkS : cv tr t w Scan.kS = 1 := by
      have b := Scan.bool_of hS hw (x := Scan.kS) (by simp [Scan.boolCols, Scan.sharedBool])
      rw [Scan.op_msg] at hop
      simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hop
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b with e | e
      · rw [e] at hop
        rcases hop with h | h
        · exact absurd h (Mem.ofNat_ne (by decide) (by decide) (by decide))
        · exact absurd h (Mem.ofNat_ne (by decide) (by decide) (by decide))
      · exact e
    have hre : cv tr t w Scan.re = 1 := by
      have hre := Scan.bool_of hS hw (x := Scan.re) (by simp [Scan.boolCols, Scan.ownBool])
      have he := eval_one_of_mult (by rw [Scan.read_def]) hm
      rw [Scan.eval_ofNat (v := cv tr t w Scan.re + cv tr t w Scan.kSh)
        (by simp only [zev_add, zev_c, cur_cv]; omega)] at he
      have := ofNat_eq_one (by omega) he
      omega
    obtain ⟨f', rfl, hq⟩ := Scan.re_block hSD hw hre
    have hf' : f' < tr.height t := by omega
    have hR := Scan.shape_all hS hf' hq 19 (by omega)
    obtain ⟨b0, -, -, b3⟩ := blk_small hH OS PS hf' hq
    right
    refine ⟨f', hf', hq, ?_, rfl⟩
    have e1 := hR.2.2.2 Scan.tau (by simp [Scan.reqCols])
    have e2 := hR.2.2.2 Scan.link (by simp [Scan.reqCols])
    have hhead := ha
    rw [Scan.op_msg, e1, e2] at hhead
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hhead
    have e := (Proc.ofNat_cv_eq ha' (by omega)).1 hhead.symm
    exact addr_tau (k := 0) (idx := cv tr t f' Scan.link) (by omega) b3 (by unfold addrOf; omega) h1 h2
  by_cases htc : t = tcd
  · subst htc
    rw [OO.tab] at hi
    have := Codec.sop_cases i hi hb
    subst this
    rw [Codec.sop_op] at hop
    rcases hop with h | h <;> simp at h <;>
      exact absurd h.symm (Mem.ofNat_ne (by decide) (by decide) (by decide))
  · exact absurd hs (by rw [OO.only t ht htp htd htc i hi hb]; decide)

end

end ZkFormal.NearV3.Sched
