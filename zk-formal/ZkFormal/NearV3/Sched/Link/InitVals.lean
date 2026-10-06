import ZkFormal.NearV3.Sched.Link.InitDist

/-!
# ZkFormal.NearV3.Sched.Link.InitVals — `InitVals` from the codec and distribute views (stage C)

**`initVals_of`**: for every instance `τ < |Ps|`, the `INIT` messages sent on `SOP` with an address
in τ's range are, as a multiset, `initMsgs τ n allowed st` with
`st = lpState P.ids P.params P.allowed (codecA0 tr tcd τ) P.seed` (`P = Ps[τ]`), where
`codecA0 tr tcd τ` is the previous allowance decoded by τ's codec block (`preA0`).

Per address `a = τ·2^14 + x` (`busCount` of an `INIT` message `M` with head `a`):
* `SOP` senders are `sprV3` (GRANTs only, op 2), `ssdV3` and `schV3` (`OpOwn`);
* `x < 4096` (link): only the codec sends (a shard row has offset `≥ 4096`); its record ends with
  address `a` are record `x` of τ's unique block (`block_unique`), with the value
  `initRec τ … x` (`codec_init_val`), and that record exists iff `x < n²` (`codec_exists`,
  `codec_hdr`);
* `x ≥ 4096` (budget): only shard rows send (a codec record has offset `< 4096`); the shard rows
  with address `a` receive `shardRec τ P side x'` (`x = 4096·(side + 1) + x'`), so there is
  exactly one when `x' < n` (`shard_exists`, `shard_unique`), with the value `initRec τ … x`
  (`shard_init_val`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

open Classical in
/-- The previous allowances decoded by τ's codec block (`0` without a block). -/
noncomputable def codecA0 (tr : Trace Fp) (tc τ : Nat) : Nat → Nat :=
  if h : ∃ f, f < tr.height tc ∧ cv tr tc f Codec.kF = 1 ∧ cv tr tc f Codec.tau = τ then
    preA0 tr tc (Classical.choose h)
  else fun _ => 0

/-- The hypotheses of the `INIT` link (ownership and `prepD0` facts). -/
structure InitCtx (AP : AirP) (pub : List Fp) (tr : Trace Fp) (tp tm tcmp ts tch tg tsd tcd : Nat)
    (Ps : List InstPub) : Prop where
  hH : HoldsP AP pub tr
  O : SchedOwn AP tp tm tcmp ts tch tg
  OS : ScanOwn AP tsd tp
  OO : OpOwn AP tp tsd tcd
  OC : CodecValOwn AP tcd
  SO : SparOwn AP
  IO : InitOwn AP tcd tsd
  h256 : Ps.length ≤ 256
  hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD)

theorem le_sum_of_mem (g : Nat → Nat) : ∀ {l : List Nat} {r : Nat}, r ∈ l → g r ≤ (l.map g).sum
  | [], _, h => by simp at h
  | a :: l, r, h => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_mem g h; omega

theorem isTauInit_iff {τ : Nat} {M : List Fp} : isTauInit τ M = true ↔
    M[2]? = some 0 ∧ ∃ a : Fp, M.head? = some a ∧ τ * 16384 ≤ a.toNat ∧ a.toNat < τ * 16384 + 16384 := by
  unfold isTauInit
  cases h : M.head? with
  | none => simp
  | some a => simp

theorem initRec_head (τ : Nat) (allowed : Array Bool) (st : St) (x : Nat) :
    ((initRec τ allowed st x).map Fp.ofNat).head? = some (Fp.ofNat (τ * 16384 + x)) := by
  simp [initRec]

theorem initRec_op (τ : Nat) (allowed : Array Bool) (st : St) (x : Nat) :
    ((initRec τ allowed st x).map Fp.ofNat)[2]? = some 0 := by
  simp [initRec, OP_INIT]; rfl

theorem initMsgs_tau {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64) {allowed : Array Bool} {st : St}
    {m : List Fp} (hm : m ∈ initMsgs τ n allowed st) : isTauInit τ m = true := by
  obtain ⟨x, hx, rfl⟩ := (mem_initMsgs hn).1 hm
  have := idxOk_lt hn hx
  refine isTauInit_iff.2 ⟨initRec_op _ _ _ _, _, initRec_head _ _ _ _, ?_⟩
  rw [toNat_ofNat_lt' (by omega)]; omega

theorem nodup_of_map {α β : Type} (g : α → β) : ∀ {l : List α}, (l.map g).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map g h.2⟩

theorem initMsgs_nodup {τ n : Nat} (hτ : τ < 256) (hn : n ≤ 64) (allowed : Array Bool) (st : St) :
    (initMsgs τ n allowed st).Nodup :=
  nodup_of_map _ (initMsgs_heads hτ hn allowed st)

theorem addr_eq {τ τ' y : Nat} (hτ' : τ' < 256) (hy : y < 16384) {a : Fp}
    (ha : some (Fp.ofNat (τ' * 16384 + y)) = some a) (h1 : τ * 16384 ≤ a.toNat)
    (h2 : a.toNat < τ * 16384 + 16384) : τ' = τ ∧ a.toNat = τ * 16384 + y := by
  have e := Option.some.inj ha
  subst e
  rw [toNat_ofNat_lt' (by omega)] at h1 h2 ⊢
  have : τ' = τ := by
    rcases Nat.lt_trichotomy τ' τ with e | e | e
    · have := Nat.mul_le_mul_right 16384 (show τ' + 1 ≤ τ by omega); omega
    · exact e
    · have := Nat.mul_le_mul_right 16384 (show τ + 1 ≤ τ' by omega); omega
  subst this
  exact ⟨rfl, rfl⟩

theorem tbc_zero_of {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp} {b : Nat} {s : Bool}
    {M : List Fp} (h : ∀ w, w < tr.height t → ∀ i ∈ is, i.bus = b → i.send = s →
      i.msgVal tr t w pub = M → i.multNat tr t w pub ≠ 0 → False) :
    tableBusCount is tr t pub b s M = 0 := by
  rcases Nat.eq_zero_or_pos (tableBusCount is tr t pub b s M) with h0 | h0
  · exact h0
  · obtain ⟨w, hw, i, hi, hb, hs, hmsg, hm⟩ := exists_of_tableBusCount (Nat.pos_iff_ne_zero.1 h0)
    exact (h w hw i hi hb hs hmsg hm).elim

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd : Nat}
  {Ps : List InstPub}

namespace InitCtx
variable (C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps)
include C

theorem codecA0_eq (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) {f : Nat} (hf : f < tr.height tcd)
    (hF : cv tr tcd f Codec.kF = 1) : codecA0 tr tcd (cv tr tcd f Codec.tau) = preA0 tr tcd f := by
  have hex : ∃ f', f' < tr.height tcd ∧ cv tr tcd f' Codec.kF = 1 ∧
      cv tr tcd f' Codec.tau = cv tr tcd f Codec.tau := ⟨f, hf, hF, rfl⟩
  unfold codecA0
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  rw [block_unique C.hH C.OC C.SO I Ps fwd hrec (by have := C.h256; omega) h1 h2 hf hF h3]

/-- **Every instance has a codec block** (its public codec record is received, only by `schV3`). -/
theorem codec_exists (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) {τ : Nat} (hτ : τ < Ps.length) :
    ∃ f, f < tr.height tcd ∧ cv tr tcd f Codec.kF = 1 ∧ cv tr tcd f Codec.tau = τ := by
  have hH := C.hH
  have h256 := C.h256
  obtain ⟨M, hMd⟩ : ∃ M, M = (parCodec τ (Ps.getD τ instD)).map Fp.ofNat := ⟨_, rfl⟩
  have hpc : 1 ≤ pubCount AP pub B_SPAR true M := by
    rw [I.count, hrec, hMd, render_par]
    apply List.count_pos_iff.2
    refine List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨τ, List.mem_range.2 hτ, ?_⟩, rfl⟩
    simp [parBlock]
  rw [par_count hH C.OS] at hpc
  unfold busCount at hpc
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub _ _ M AP.tables 0 (Nat.pos_iff_ne_zero.1 hpc)
  rw [Nat.zero_add] at htc
  obtain ⟨w, hw, i, hi, hb, -, hmsg, hm⟩ := exists_of_tableBusCount htc
  have hM1 : M[1]? = some (Fp.ofNat 0) := by rw [hMd]; simp [parCodec]
  by_cases htd : t = tsd
  · subst htd
    exfalso
    rw [C.OS.tab] at hi
    have hi0 := Scan.par_cases i hi hb
    subst hi0
    have hS := Scan.SLocal.of_sd (sd_local hH C.OS)
    have F := Scan.row_flags hS hw
    have he := eval_one_of_mult (by rw [Scan.par_def]) hm
    rw [Scan.eval_ofNat (v := cv tr t w Scan.kP + cv tr t w Scan.fQ + cv tr t w Scan.kSh + cv tr t w Scan.kC)
      (by simp only [zev_add, zev_c, cur_cv, Scan.kSh, Scan.kC]; omega)] at he
    have h1 := ofNat_eq_one (by omega) he
    rw [Scan.par_msg] at hmsg
    have ht := congrArg (·[1]?) hmsg
    simp only [Scan.parV, List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, hM1,
      Option.some.injEq] at ht
    have := ofNat_inj' (by omega) (by decide) ht
    omega
  by_cases htc' : t = tcd
  · subst htc'
    rw [C.OC.tab] at hi
    have hi6 := Codec.par_i i hi hb
    subst hi6
    have hF : cv tr t w Codec.kF = 1 := Codec.one_of_mult (i := Codec.interactions[6]!) rfl hm
    obtain ⟨-, -, -, -, -, m6, -⟩ := Codec.codec_first (codec_local hH C.OC) (codec_h22 hH C.OC) hw hF
    rw [m6, hMd] at hmsg
    have h0 := congrArg List.head? hmsg
    simp only [List.map_cons, List.head?_cons, parCodec, List.cons_append, Option.some.injEq] at h0
    exact ⟨w, hw, hF, ofNat_inj' (cv_lt _ _) (by omega) h0⟩
  · exact absurd hb (C.IO.parRecv t ht htc' htd i hi)

/-- The process table sends no `INIT` (its `SOP` messages are GRANTs). -/
theorem proc_zero {M : List Fp} (hM : M[2]? = some 0) :
    tableBusCount AP.tables[tp]!.interactions tr tp pub B_SOP true M = 0 := by
  apply tbc_zero_of
  intro w _ i hi hb _ hmsg _
  rw [C.O.tp_tab] at hi
  have h2 : ((Proc.interactions[7]!).msgVal tr tp w pub)[2]? = some (Fp.ofNat OP_GRANT) ∧
      ((Proc.interactions[8]!).msgVal tr tp w pub)[2]? = some (Fp.ofNat OP_GRANT) ∧
      ((Proc.interactions[9]!).msgVal tr tp w pub)[2]? = some (Fp.ofNat OP_GRANT) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Proc.msg7]; simp
    · rw [Proc.msg8]; simp
    · rw [Proc.msg9]; simp
  have hne : (0 : Fp) ≠ Fp.ofNat OP_GRANT := Mem.ofNat_ne (a := 0) (by decide) (by decide) (by decide)
  rcases Proc.sop_cases i hi hb with e | e | e <;> subst e <;> rw [hmsg, hM] at h2
  · exact hne (Option.some.inj h2.1)
  · exact hne (Option.some.inj h2.2.1)
  · exact hne (Option.some.inj h2.2.2)

/-- A codec `SOP` send is record `k` of a block, with head `16384·τ_f + k`, `τ_f < |Ps|`,
`k < n_f² ≤ 4096`. -/
theorem codec_send (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) {w : Nat} (hw : w < tr.height tcd)
    (hm : (Codec.interactions[10]!).multNat tr tcd w pub ≠ 0) :
    ∃ f k, f < tr.height tcd ∧ cv tr tcd f Codec.kF = 1 ∧ k < cv tr tcd f Codec.NN ∧
      w = f + 5 + 24 * k + 23 ∧ cv tr tcd f Codec.tau < Ps.length ∧ k < 4096 ∧
      ((Codec.interactions[10]!).msgVal tr tcd w pub).head? =
        some (Fp.ofNat (cv tr tcd f Codec.tau * 16384 + k)) := by
  have hL := codec_local C.hH C.OC
  have hH22 := codec_h22 C.hH C.OC
  have hrd : cv tr tcd w Codec.rend = 1 := Codec.one_of_mult (i := Codec.interactions[10]!) rfl hm
  obtain ⟨f, k, hf, hF, hk, rfl⟩ := Codec.rend_rec hL hH22 hw hrd
  have hτ := (first_par C.hH C.OC C.SO I Ps fwd hrec (by have := C.h256; omega) hf hF).1
  obtain ⟨-, -, hNN, -⟩ := codec_hdr C.hH C.OC C.SO I Ps fwd hrec C.h256 hf hF (C.hP _ hτ)
  have hn := (C.hP _ hτ).n64
  have hk4 : k < 4096 := by
    have := Nat.mul_le_mul hn hn; unfold InstPub.n at hNN; omega
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, -, -, -, -, -, -, msg10, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  refine ⟨f, k, hf, hF, hk, rfl, hτ, hk4, ?_⟩
  rw [msg10]
  simp [Nat.mul_comm]

/-- A shard row's `SOP` send. -/
theorem sd_send {w : Nat} (hw : w < tr.height tsd)
    (hm : (ScanDist.interactions[4]!).multNat tr tsd w pub ≠ 0) {M : List Fp}
    (hmsg : (ScanDist.interactions[4]!).msgVal tr tsd w pub = M) (hM : M[2]? = some 0) :
    cv tr tsd w Dist.kSh = 1 := by
  have hS := Scan.SLocal.of_sd (sd_local C.hH C.OS)
  have F := Scan.row_flags hS hw
  have hkS : cv tr tsd w Scan.kS = 0 := by
    rw [Scan.op_msg] at hmsg
    have h2 := congrArg (·[2]?) hmsg
    simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, hM,
      Option.some.injEq] at h2
    exact (Proc.ofNat_cv_eq (cv_lt _ _) (by decide)).1 h2
  have hre := Scan.bool_of hS hw (x := Scan.re) (by simp [Scan.boolCols, Scan.ownBool])
  have he := eval_one_of_mult (by rw [Scan.read_def]) hm
  rw [Scan.eval_ofNat (v := cv tr tsd w Scan.re + cv tr tsd w Scan.kSh)
    (by simp only [zev_add, zev_c, cur_cv]; omega)] at he
  have := ofNat_eq_one (by omega) he
  have : cv tr tsd w Scan.kSh = 1 := by omega
  exact this

/-- **The send count of a τ-`INIT` message.** -/
theorem tau_count (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) {τ : Nat} (hτ : τ < Ps.length)
    {M : List Fp} (hM : isTauInit τ M = true) :
    busCount AP.toAir tr pub B_SOP true M =
      if M ∈ initMsgs τ (Ps.getD τ instD).n (Ps.getD τ instD).allowed
        (lpState (Ps.getD τ instD).ids (Ps.getD τ instD).params (Ps.getD τ instD).allowed
          (codecA0 tr tcd τ) (Ps.getD τ instD).seed) then 1 else 0 := by
  have hH := C.hH
  have h256 := C.h256
  have PO := C.hP τ hτ
  have hn : (Ps.getD τ instD).n ≤ 64 := PO.n64
  obtain ⟨hM2, a, hMa, ha1, ha2⟩ := isTauInit_iff.1 hM
  have hMl : M.head? = some a := hMa
  have hta : a.toNat < 2013265921 := Fp.toNat_lt _
  -- the codec block of τ
  obtain ⟨fτ, hfτ, hFτ, hττ⟩ := C.codec_exists I fwd hrec hτ
  have hA0 : codecA0 tr tcd τ = preA0 tr tcd fτ := by
    rw [← hττ]; exact C.codecA0_eq I fwd hrec hfτ hFτ
  have hL := codec_local hH C.OC
  have hH22 := codec_h22 hH C.OC
  obtain ⟨-, -, hNNτ, -⟩ := codec_hdr hH C.OC C.SO I Ps fwd hrec h256 hfτ hFτ (by rw [hττ]; exact PO)
  rw [hττ] at hNNτ
  generalize hst : lpState (Ps.getD τ instD).ids (Ps.getD τ instD).params (Ps.getD τ instD).allowed
    (codecA0 tr tcd τ) (Ps.getD τ instD).seed = st
  have hmemI : M ∈ initMsgs τ (Ps.getD τ instD).n (Ps.getD τ instD).allowed st ↔
      ∃ x, idxOk (Ps.getD τ instD).n x = true ∧ a.toNat = τ * 16384 + x ∧
        M = (initRec τ (Ps.getD τ instD).allowed st x).map Fp.ofNat := by
    rw [mem_initMsgs hn]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := idxOk_lt hn hx
      rw [initRec_head] at hMl
      have e := Option.some.inj hMl
      subst e
      exact ⟨x, hx, toNat_ofNat_lt' (by omega), rfl⟩
    · rintro ⟨x, hx, -, rfl⟩; exact ⟨x, hx, rfl⟩
  -- the senders other than ssdV3 / schV3
  have other : ∀ t, t < AP.tables.length → t ≠ tsd → t ≠ tcd →
      tableBusCount AP.tables[t]!.interactions tr t pub B_SOP true M = 0 := by
    intro t ht h1 h2
    by_cases htp : t = tp
    · subst htp; exact C.proc_zero hM2
    · exact tableBusCount_zero (fun i hi hb => by rw [C.OO.only t ht htp h1 h2 i hi hb]; decide)
  have hτ256 : τ < 256 := by omega
  by_cases hlink : a.toNat - τ * 16384 < 4096
  · -- link addresses: the codec only
    have hsd : tableBusCount AP.tables[tsd]!.interactions tr tsd pub B_SOP true M = 0 := by
      apply tbc_zero_of
      intro w hw i hi hb hs hmsg hm
      rw [C.OS.tab] at hi
      have e4 := (Scan.bus_cases i hi).2.2 hb
      subst e4
      have hsh := C.sd_send hw hm hmsg hM2
      obtain ⟨hτw, side, x', hs2, hx', -, hval⟩ := shard_init_val hH C.OS I Ps fwd hrec h256 C.hP hw hsh
        (codecA0 tr tcd τ)
      have hn' := (C.hP _ hτw).n64
      unfold InstPub.n at hx'
      rw [hval] at hmsg
      have hh := congrArg List.head? hmsg
      rw [initRec_head, hMl] at hh
      have := (addr_eq (by omega) (by omega) hh ha1 ha2).2
      omega
    have hb : busCount AP.toAir tr pub B_SOP true M =
        tableBusCount AP.tables[tcd]!.interactions tr tcd pub B_SOP true M := by
      unfold busCount
      have := busCount_go_single tr pub B_SOP true M AP.tables 0 tcd C.OC.lt (fun t ht hne => by
        rw [Nat.zero_add]
        by_cases htd : t = tsd
        · subst htd; exact hsd
        · exact other t ht htd hne)
      simpa using this
    rw [hb, C.OC.tab]
    show tableBusCount Codec.interactions tr tcd pub B_SOP true M = _
    rw [tbc_single Codec.sop_filter]
    -- each nonzero term is record `x` of τ's block
    have term : ∀ w, w < tr.height tcd → (Codec.interactions[10]!).multNat tr tcd w pub ≠ 0 →
        (Codec.interactions[10]!).msgVal tr tcd w pub = M →
        w = fτ + 5 + 24 * (a.toNat - τ * 16384) + 23 ∧ a.toNat - τ * 16384 < cv tr tcd fτ Codec.NN := by
      intro w hw hm hmsg
      obtain ⟨f, k, hf, hF, hk, rfl, hτf, hk4, hh⟩ := C.codec_send I fwd hrec hw hm
      rw [hmsg, hMl] at hh
      obtain ⟨e1, e2⟩ := addr_eq (by omega) (by omega) hh.symm ha1 ha2
      have hff : f = fτ := block_unique hH C.OC C.SO I Ps fwd hrec (by omega) hf hF hfτ hFτ (by rw [e1, hττ])
      subst hff
      exact ⟨by omega, by omega⟩
    have hle : ((List.range (tr.height tcd)).map fun w =>
        if (Codec.interactions[10]!).msgVal tr tcd w pub = M then
          (Codec.interactions[10]!).multNat tr tcd w pub else 0).sum ≤ 1 := by
      apply sum_le_one
      · intro w _
        split
        · exact multNat_le1 (i := Codec.interactions[10]!) rfl
        · omega
      · intro w1 h1 w2 h2 n1 n2
        split at n1
        · split at n2
          · rename_i e1 e2
            rw [(term w1 (List.mem_range.1 h1) n1 e1).1, (term w2 (List.mem_range.1 h2) n2 e2).1]
          · exact absurd rfl n2
        · exact absurd rfl n1
      · exact List.nodup_range
    split
    · -- the expected message is sent by record x of τ's block
      rename_i hmem
      obtain ⟨x, hx, hax, hMx⟩ := hmemI.1 hmem
      have hx4 : x < 4096 := by rw [hax] at hlink; omega
      have hxN : x < cv tr tcd fτ Codec.NN := by
        rw [hNNτ]
        simp only [idxOk, decide_eq_true_eq] at hx
        rcases hx with h | h | h
        · exact h
        · omega
        · omega
      obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hfτ hFτ
      obtain ⟨-, -, -, -, -, -, -, -, m10, -⟩ := Codec.codec_rec_msgs hL (RR x hxN) (RS x hxN)
      have hv := codec_init_val hH C.OC C.SO C.OS C.IO C.O.cmp I Ps fwd hrec h256 C.hP hfτ hFτ hxN
      rw [hττ, ← hA0, hst, ← hMx] at hv
      have hw : fτ + 5 + 24 * x + 23 < tr.height tcd := (RR x hxN 23 (by omega)).1
      have := le_sum_of_mem (fun w => if (Codec.interactions[10]!).msgVal tr tcd w pub = M then
          (Codec.interactions[10]!).multNat tr tcd w pub else 0) (List.mem_range.2 hw)
      simp only [hv, if_true, m10] at this
      omega
    · rename_i hmem
      apply sum_zero_of
      intro w hw
      split
      · rename_i hmsg
        by_cases hm : (Codec.interactions[10]!).multNat tr tcd w pub = 0
        · exact hm
        exfalso
        obtain ⟨hwe, hxN⟩ := term w (List.mem_range.1 hw) hm hmsg
        apply hmem
        have hv := codec_init_val hH C.OC C.SO C.OS C.IO C.O.cmp I Ps fwd hrec h256 C.hP hfτ hFτ hxN
        rw [hττ, ← hA0, hst, ← hwe, hmsg] at hv
        refine hmemI.2 ⟨_, ?_, by omega, hv⟩
        simp only [idxOk, decide_eq_true_eq]; rw [hNNτ] at hxN; left; exact hxN
      · rfl
  · -- budget addresses: the shard rows only
    have hcd : tableBusCount AP.tables[tcd]!.interactions tr tcd pub B_SOP true M = 0 := by
      apply tbc_zero_of
      intro w hw i hi hb hs hmsg hm
      rw [C.OC.tab] at hi
      have e10 := Codec.sop_cases i hi hb
      subst e10
      obtain ⟨f, k, -, -, -, -, hτf, hk4, hh⟩ := C.codec_send I fwd hrec hw hm
      rw [hmsg, hMl] at hh
      have := (addr_eq (by omega) (by omega) hh.symm ha1 ha2).2
      omega
    have hb : busCount AP.toAir tr pub B_SOP true M =
        tableBusCount AP.tables[tsd]!.interactions tr tsd pub B_SOP true M := by
      unfold busCount
      have := busCount_go_single tr pub B_SOP true M AP.tables 0 tsd C.OS.lt (fun t ht hne => by
        rw [Nat.zero_add]
        by_cases htc : t = tcd
        · subst htc; exact hcd
        · exact other t ht hne htc)
      simpa using this
    rw [hb, C.OS.tab]
    show tableBusCount ScanDist.interactions tr tsd pub B_SOP true M = _
    rw [tbc_single ScanDist.sop_filter]
    -- each nonzero term is a shard row of τ with record (side, x')
    have term : ∀ w, w < tr.height tsd → (ScanDist.interactions[4]!).multNat tr tsd w pub ≠ 0 →
        (ScanDist.interactions[4]!).msgVal tr tsd w pub = M →
        cv tr tsd w Dist.kSh = 1 ∧ ∃ side x', side < 2 ∧ x' < (Ps.getD τ instD).n ∧
          a.toNat = τ * 16384 + (4096 * (side + 1) + x') ∧
          Scan.parV tr tsd w = shardRec τ (Ps.getD τ instD) side x' ∧
          M = (initRec τ (Ps.getD τ instD).allowed st (4096 * (side + 1) + x')).map Fp.ofNat := by
      intro w hw hm hmsg
      have hsh := C.sd_send hw hm hmsg hM2
      obtain ⟨hτw, side, x', hs2, hx', hpv, hval⟩ := shard_init_val hH C.OS I Ps fwd hrec h256 C.hP hw hsh
        (codecA0 tr tcd τ)
      have hn' := (C.hP _ hτw).n64
      have hx'' : x' < 64 := by unfold InstPub.n at hx'; omega
      have hh := congrArg List.head? (hval.symm.trans hmsg)
      rw [initRec_head, hMl] at hh
      obtain ⟨e1, e2⟩ := addr_eq (by omega) (by omega) hh ha1 ha2
      rw [e1] at hx' hpv hval
      rw [hst] at hval
      exact ⟨hsh, side, x', hs2, hx', e2, hpv, hval.symm.trans hmsg |>.symm⟩
    have hle : ((List.range (tr.height tsd)).map fun w =>
        if (ScanDist.interactions[4]!).msgVal tr tsd w pub = M then
          (ScanDist.interactions[4]!).multNat tr tsd w pub else 0).sum ≤ 1 := by
      apply sum_le_one
      · intro w _
        split
        · exact multNat_le1 (i := ScanDist.interactions[4]!) rfl
        · omega
      · intro w1 h1 w2 h2 n1 n2
        split at n1
        · split at n2
          · rename_i e1 e2
            obtain ⟨s1, side1, x1, hs1, hx1, ha1', hp1, -⟩ := term w1 (List.mem_range.1 h1) n1 e1
            obtain ⟨s2, side2, x2, hs2, hx2, ha2', hp2, -⟩ := term w2 (List.mem_range.1 h2) n2 e2
            have hsx : side1 = side2 ∧ x1 = x2 := by
              have hn' : (Ps.getD τ instD).n ≤ 64 := hn
              constructor <;> omega
            obtain ⟨rfl, rfl⟩ := hsx
            exact shard_unique hH C.OS I Ps fwd hrec h256 (fun τ h => (C.hP τ h).n64)
              (List.mem_range.1 h1) s1 (List.mem_range.1 h2) s2 (hp1.trans hp2.symm)
          · exact absurd rfl n2
        · exact absurd rfl n1
      · exact List.nodup_range
    split
    · rename_i hmem
      obtain ⟨x, hx, hax, hMx⟩ := hmemI.1 hmem
      have hx4 : 4096 ≤ x := by rw [hax] at hlink; omega
      have hxb : (4096 ≤ x ∧ x < 4096 + (Ps.getD τ instD).n) ∨ (8192 ≤ x ∧ x < 8192 + (Ps.getD τ instD).n) := by
        simp only [idxOk, decide_eq_true_eq] at hx
        have : (Ps.getD τ instD).n * (Ps.getD τ instD).n ≤ 4096 := Nat.mul_le_mul hn hn
        rcases hx with h | h | h
        · omega
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨side, x', hs2, hx', hxe⟩ : ∃ side x', side < 2 ∧ x' < (Ps.getD τ instD).n ∧
          x = 4096 * (side + 1) + x' := by
        rcases hxb with h | h
        · exact ⟨0, x - 4096, by decide, by omega, by omega⟩
        · exact ⟨1, x - 8192, by decide, by omega, by omega⟩
      rw [hxe] at hMx
      obtain ⟨w, hw, hsh, hτw, hpv⟩ := shard_exists hH C.OS I Ps fwd hrec h256 (fun τ h => (C.hP τ h).n64)
        hτ hs2 hx'
      obtain ⟨-, side'', x'', hs'', hx'', hpv'', hval⟩ := shard_init_val hH C.OS I Ps fwd hrec h256 C.hP hw hsh
        (codecA0 tr tcd τ)
      rw [hτw] at hx'' hpv'' hval
      rw [hst] at hval
      obtain ⟨rfl, rfl⟩ := shardRec_inj (by omega) hn hs'' hx'' hs2 hx' (by rw [← hpv'', hpv])
      rw [← hMx] at hval
      have hS := Scan.SLocal.of_sd (sd_local hH C.OS)
      have F := Scan.row_flags hS hw
      have hm1 : (ScanDist.interactions[4]!).multNat tr tsd w pub = 1 := by
        have h1 := multNat_le1 (i := ScanDist.interactions[4]!) (tr := tr) (t := tsd) (r := w) (pub := pub) rfl
        have h2 : (ScanDist.interactions[4]!).multNat tr tsd w pub ≠ 0 := by
          apply Mem.multNat_ne_of (e := .add (c Scan.re) (c Dist.kSh)) rfl
          have hsh' : cv tr tsd w Scan.kSh = 1 := hsh
          rw [Scan.eval_ofNat (v := 1) (by simp only [zev_add, zev_c, cur_cv]; simp only [Scan.kSh] at hsh' F; omega)]
          rfl
        omega
      have := le_sum_of_mem (fun w => if (ScanDist.interactions[4]!).msgVal tr tsd w pub = M then
          (ScanDist.interactions[4]!).multNat tr tsd w pub else 0) (List.mem_range.2 hw)
      simp only [hval, if_true, hm1] at this
      omega
    · rename_i hmem
      apply sum_zero_of
      intro w hw
      split
      · rename_i hmsg
        by_cases hm : (ScanDist.interactions[4]!).multNat tr tsd w pub = 0
        · exact hm
        exfalso
        obtain ⟨-, side, x', hs2, hx', hax, -, hv⟩ := term w (List.mem_range.1 hw) hm hmsg
        apply hmem
        refine hmemI.2 ⟨_, ?_, hax, hv⟩
        simp only [idxOk, decide_eq_true_eq]
        omega
      · rfl

/-- **`InitVals` for instance τ** (stage C). -/
theorem initVals_of (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) {τ : Nat} (hτ : τ < Ps.length) :
    InitVals AP tr pub τ (Ps.getD τ instD).n (Ps.getD τ instD).allowed
      (lpState (Ps.getD τ instD).ids (Ps.getD τ instD).params (Ps.getD τ instD).allowed
        (codecA0 tr tcd τ) (Ps.getD τ instD).seed) := by
  have hn : (Ps.getD τ instD).n ≤ 64 := (C.hP τ hτ).n64
  have hτ256 : τ < 256 := by have := C.h256; omega
  unfold InitVals
  apply List.perm_iff_count.2
  intro M
  rw [(initMsgs_nodup hτ256 hn _ _).count]
  by_cases hM : isTauInit τ M = true
  · rw [List.count_filter hM, sopSent_count, C.tau_count I fwd hrec hτ hM]
  · rw [List.count_eq_zero.2 (fun h => hM (List.mem_filter.1 h).2), if_neg]
    intro hm
    exact hM (initMsgs_tau hτ256 hn hm)

end InitCtx

end

end ZkFormal.NearV3.Sched
