import ZkFormal.NearV3.Sched.Link.SoundFin
import ZkFormal.Near.Extract.ShaFacts

/-!
# ZkFormal.NearV3.Sched.Link.SoundSha — the post sanity hash is `sha256 (h0 ‖ ash)` (stage D step 2)

τ's codec block sends its 64 hash-input bytes on `BYTES` with id `11 + 16τ` (kind `K_SCH = 11`):
the 32 pre bytes of the hash rows (`h0Of τ`), then the 32 `ash` bytes, each received from the
public `SPUBB` record `(τ, 2, j, ash_j)` (`codec_trailer`). It receives the digest
`(11 + 16τ, 64, d)` on `DIGEST` and writes `d` as the post state's hash (`codec_post`).

* `ShaOwn` (ownership, decidable): table `tsha` is the SHA table on `BYTES` / `DIGEST`, the only
  `DIGEST` sender; no public `DIGEST` segment;
* `ShaKind` (**kind registry**, cross-lane): no other table and no public record sends a `BYTES`
  message whose id has kind 11 (`id mod 16 = 11`).

Then (L5's `sha_digest_contract_closed`): **`codec_digest`**: the 64 bytes are bytes and
`d = sha256` of them; **`codec_ash`**: the last 32 are `Ps[τ].ash`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- The SHA table (L5) is table `tsha`, the only `DIGEST` sender; no public `DIGEST` segment. -/
structure ShaOwn (AP : AirP) (tsha : Nat) : Prop where
  lt : tsha < AP.tables.length
  tab : AP.tables[tsha]! = ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST
  dig : ∀ t, t < AP.tables.length → t ≠ tsha → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = ZkFormal.Near.B_DIGEST → i.send = false
  pubDig : ∀ seg ∈ AP.pubSegs, seg.bus ≠ ZkFormal.Near.B_DIGEST

/-- **Kind registry** (cross-lane, assembly): only the codec sends `BYTES` messages of kind 11. -/
structure ShaKind (AP : AirP) (pub : List Fp) (tr : Trace Fp) (tc : Nat) : Prop where
  tabs : ∀ t, t < AP.tables.length → t ≠ tc → ∀ r, r < tr.height t → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = ZkFormal.Near.B_BYTES → i.send = true → i.multNat tr t r pub ≠ 0 →
    ∀ a, (i.msgVal tr t r pub).head? = some a → a.toNat % 16 ≠ 11
  pubs : ∀ M, pubCount AP pub ZkFormal.Near.B_BYTES true M ≠ 0 → ∀ a, M.head? = some a → a.toNat % 16 ≠ 11

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The hash-input byte `j < 64` of the block at `f`. -/
def shaByte (tr : Trace Fp) (t f j : Nat) : Nat :=
  if j < 32 then cv tr t (f + 5 + 24 * cv tr t f NN + j) bpre else cv tr t (f + 5 + 24 * cv tr t f NN + j) bsha

theorem bytes_send_i {i : Interaction} (hi : i ∈ interactions) (hb : i.bus = ZkFormal.Near.B_BYTES)
    (hs : i.send = true) : i = interactions[2]! := by
  rw [i2_def]
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SCMP, B_SPLEN, B_SPOST, B_S0F, B_SPAR, B_SDL, B_SPUBB, B_SOP, B_SFIN, B_SDG, B_SA0,
      ZkFormal.NearV3.B_VBYTES, ZkFormal.Near.B_BYTES, ZkFormal.Near.B_DIGEST]

/-- **A `BYTES` send comes from a hash row of a block, with message `(11 + 16τ, j, byte_j)`.** -/
theorem bytes_row (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {w : Nat} (hw : w < tr.height t)
    (hm : (interactions[2]!).multNat tr t w pub ≠ 0) :
    ∃ f j, f < tr.height t ∧ cv tr t f kF = 1 ∧ j < 64 ∧ w = f + 5 + 24 * cv tr t f NN + j ∧
      (interactions[2]!).msgVal tr t w pub = [11 + 16 * cv tr t f tau, j, shaByte tr t f j].map Fp.ofNat := by
  have K := kinds hL hw
  have hza : 1 ≤ cv tr t w kZ + cv tr t w kA := by
    rcases Nat.eq_zero_or_pos (cv tr t w kZ + cv tr t w kA) with h | h
    · exact absurd (mult_zero (i := interactions[2]!) (by rw [i2_def])
        (by simp only [zev_add, zev_c, cur_cv]; omega)) hm
    · exact h
  obtain ⟨f, hfw, hF, hlt⟩ := codec_cover hL hH w hw (by omega)
  have hf : f < tr.height t := by omega
  obtain ⟨-, -, -, -, -, -, HR, RR, -, -, -, -, -⟩ := codec_block hL hH hf hF
  obtain ⟨T1, T2⟩ := codec_trailer hL hH hf hF
  by_cases h5 : w - f < 5
  · obtain ⟨-, hk, -⟩ := HR (w - f) h5
    rw [show f + (w - f) = w by omega] at hk
    omega
  · by_cases hr : w - f < 5 + 24 * cv tr t f NN
    · obtain ⟨k, hk⟩ : ∃ k, k = (w - f - 5) / 24 := ⟨_, rfl⟩
      obtain ⟨o, ho⟩ : ∃ o, o = (w - f - 5) % 24 := ⟨_, rfl⟩
      have e : f + 5 + 24 * k + o = w := by omega
      have hkN : k < cv tr t f NN := by
        rw [hk]; exact Nat.div_lt_of_lt_mul (by omega)
      have hk1 := (RR k hkN o (by omega)).2.1
      rw [e] at hk1
      omega
    · refine ⟨f, w - (f + 5 + 24 * cv tr t f NN), hf, hF, by omega, by omega, ?_⟩
      unfold shaByte
      by_cases hz : w - (f + 5 + 24 * cv tr t f NN) < 32
      · obtain ⟨-, msg⟩ := T1 _ hz
        rw [show f + 5 + 24 * cv tr t f NN + (w - (f + 5 + 24 * cv tr t f NN)) = w by omega] at msg
        rw [if_pos hz, show f + 5 + 24 * cv tr t f NN + (w - (f + 5 + 24 * cv tr t f NN)) = w by omega]
        exact msg
      · obtain ⟨-, msg, -⟩ := T2 (w - (f + 5 + 24 * cv tr t f NN) - 32) (by omega)
        rw [show f + 5 + 24 * cv tr t f NN + 32 + (w - (f + 5 + 24 * cv tr t f NN) - 32) = w by omega,
          show 32 + (w - (f + 5 + 24 * cv tr t f NN) - 32) = w - (f + 5 + 24 * cv tr t f NN) by omega] at msg
        rw [if_neg hz, show f + 5 + 24 * cv tr t f NN + (w - (f + 5 + 24 * cv tr t f NN)) = w by omega]
        exact msg

end Codec

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem shaLocal_of_holdsP (hH : HoldsP AP pub tr) {tsha : Nat} (SH : ShaOwn AP tsha) :
    ZkFormal.Sha.ShaLocal tr tsha pub where
  log_ge := (hH.logBound tsha SH.lt).1
  log_le := by have := (hH.logBound tsha SH.lt).2; rw [← tables_get SH.lt, SH.tab] at this; exact this
  constr := fun r hr e he => by
    have := local_of_holdsP hH SH.lt r hr e; rw [SH.tab] at this; exact this he

theorem sha_dmult {tsha d : Nat}
    (hm : (ZkFormal.Near.shaDigestI).multNat tr tsha d pub ≠ 0) :
    tr.cell tsha d ZkFormal.Sha.Layout.colDmult = 1 := by
  refine Classical.byContradiction fun hne => hm ?_
  simp [ZkFormal.Near.shaDigestI, Interaction.multNat, Interaction.multNat.go, ZkFormal.Sha.Table.interactions,
    Expr.eval, Expr.evalWith, rowEnv, ZkFormal.Sha.Table.E.c, hne]

theorem sha_fmult {tsha r q : Nat} (hq : q < 16) (h : tr.cell tsha r (ZkFormal.Sha.Layout.colF q) = 1) :
    ((ZkFormal.Sha.Table.interactions ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST)[q]!).multNat tr tsha r pub ≠ 0 := by
  obtain ⟨-, -, -, hmul⟩ := ZkFormal.Near.sha_is_bytes q hq
  rw [Interaction.multNat, hmul]
  simp [Interaction.multNat.go, Expr.eval, Expr.evalWith, rowEnv, h]

/-- **The hash input and digest of a codec block.** -/
theorem codec_digest (hH : HoldsP AP pub tr) {tc tsha : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (SH : ShaOwn AP tsha) (SK : ShaKind AP pub tr tc)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    (∀ j, j < 64 → Codec.shaByte tr tc f j < 256) ∧
      (List.range 32).map (fun j => UInt8.ofNat (cv tr tc (f + 5 + 24 * cv tr tc f Codec.NN) (Codec.reg j))) =
        ArenaCore.sha256 ((List.range 64).map fun j => UInt8.ofNat (Codec.shaByte tr tc f j)) := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  have hlen : Ps.length < 2013265921 := by omega
  have hτ := (first_par hH O SO I Ps fwd hrec hlen hf hF).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, -, m3, msg3, -⟩ := Codec.codec_post hL hH22 hf hF
  generalize hz : f + 5 + 24 * cv tr tc f Codec.NN = z at m3 msg3 hlt
  have hzh : z < tr.height tc := by omega
  -- the digest provider
  obtain ⟨d, hd, hdm, hmsg⟩ : ∃ d, d < tr.height tsha ∧ tr.cell tsha d ZkFormal.Sha.Layout.colDmult = 1 ∧
      ZkFormal.Near.shaDigestI.msgVal tr tsha d pub = (Codec.interactions[3]!).msgVal tr tc z pub := by
    rcases recv_src hH O.lt hzh (by rw [O.tab]; exact codec_mem 3 (by decide))
        (by rw [Codec.i3_def]) (by rw [Codec.i3_def]) (by rw [m3]; exact Nat.one_ne_zero) with
      hp | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩
    · exact absurd (pubCount_zero (s := true) (fun seg h1 h2 => absurd h2 (SH.pubDig seg h1)) _) hp
    · have hts : t' = tsha := Classical.byContradiction fun hne => by
        have := SH.dig t' ht' hne i' hi' hb'; rw [this] at hs'; cases hs'
      rw [hts] at hi' hm' hmsg hr'
      rw [SH.tab] at hi'
      rcases ZkFormal.Near.sha_mem hi' with ⟨-, h⟩ | e
      · rw [h] at hs'; cases hs'
      · subst e
        exact ⟨r', hr', sha_dmult hm', hmsg⟩
  have hLs := shaLocal_of_holdsP hH SH
  obtain ⟨msg, dg, -, hdg, hmsg16, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hLs ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST hd hdm
  rw [show ZkFormal.Near.shaDigestI = (ZkFormal.Sha.Table.interactions ZkFormal.Near.B_BYTES
    ZkFormal.Near.B_DIGEST)[16]! from rfl, hmsg16, msg3] at hmsg
  simp only [List.cons_append, List.map_cons, List.cons.injEq, List.nil_append] at hmsg
  obtain ⟨eid, elen, edg⟩ := hmsg
  have hid : 11 + 16 * cv tr tc f Codec.tau < 2013265921 := by omega
  -- every byte of the SHA message comes from τ's codec block
  have src : ∀ i, i < msg.length → ∃ j, j < 64 ∧ Fp.ofNat j = Fp.ofNat i ∧
      Fp.ofNat (Codec.shaByte tr tc f j) = Fp.ofNat (msg[i]!).toNat := by
    intro i hi
    obtain ⟨rr, hrr, q, hq, hfq, hmq⟩ := hbytes i hi
    obtain ⟨hmem, hbus, hsend, -⟩ := ZkFormal.Near.sha_is_bytes q hq
    rcases recv_src hH SH.lt hrr (by rw [SH.tab]; exact hmem) hbus hsend (sha_fmult hq hfq) with
      hp | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg', hm'⟩
    · exfalso
      rw [hmq] at hp
      have := SK.pubs _ hp _ rfl
      rw [eid, toNat_ofNat_lt' hid] at this
      omega
    · by_cases htc : t' = tc
      · rw [htc] at hi' hm' hmsg' hr'
        rw [O.tab] at hi'
        have e2 := Codec.bytes_send_i hi' hb' hs'
        subst e2
        obtain ⟨f', j, hf', hF', hj, rfl, hmj⟩ := Codec.bytes_row hL hH22 hr' hm'
        rw [hmj, hmq] at hmsg'
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg'
        obtain ⟨a1, a2, a3, -⟩ := hmsg'
        have hτ' := (first_par hH O SO I Ps fwd hrec hlen hf' hF').1
        rw [eid] at a1
        have := ofNat_inj' (by omega) hid a1
        have ef : f' = f := block_unique hH O SO I Ps fwd hrec hlen hf' hF' hf hF (by omega)
        subst ef
        exact ⟨j, hj, a2, a3⟩
      · exfalso
        have := SK.tabs t' ht' htc r' hr' i' hi' hb' hs' hm' _ (by rw [hmsg', hmq]; rfl)
        rw [eid, toNat_ofNat_lt' hid] at this
        omega
  -- the length is 64
  have hle : msg.length ≤ 64 := by
    apply Nat.le_of_not_lt; intro h
    obtain ⟨j, hj, hji, -⟩ := src 64 h
    have := ofNat_inj' (by omega) (by omega) hji; omega
  have hml : msg.length = 64 := ofNat_inj' (by omega) (by omega) elen
  -- the bytes
  have hb : ∀ i, i < 64 → Codec.shaByte tr tc f i = (msg[i]!).toNat := by
    intro i hi
    obtain ⟨j, hj, hji, hv⟩ := src i (by omega)
    have := ofNat_inj' (by omega) (by omega) hji; subst this
    exact ofNat_inj' (by unfold Codec.shaByte; split <;> exact cv_lt _ _)
      (by have := (msg[j]!).toNat_lt; omega) hv
  have hmsgEq : msg = (List.range 64).map fun j => UInt8.ofNat (Codec.shaByte tr tc f j) := by
    apply List.ext_getElem (by simp [hml])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hb i (by omega)]
    rw [getElem!_pos msg i h1]
    exact (UInt8.ofNat_toNat).symm
  refine ⟨fun j hj => by rw [hb j hj]; exact (msg[j]!).toNat_lt, ?_⟩
  rw [← hmsgEq, ← hdg]
  -- the digest bytes
  have hdl : dg.length = 32 := by rw [hdg]; exact ArenaCore.sha256_length _
  apply List.ext_getElem (by simp [hdl])
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  have := congrArg (fun L => L[j]?) edg
  simp only [List.getElem?_map, List.getElem?_range h1, List.getElem?_eq_getElem h2, Option.map_some,
    Option.some.injEq] at this
  have e := ofNat_inj' (by have := (dg[j]).toNat_lt; omega) (cv_lt _ _) this
  simp only [List.getElem_map, List.getElem_range]
  rw [← e]
  exact UInt8.ofNat_toNat

end

end ZkFormal.NearV3.Sched
