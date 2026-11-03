import StateM5a.StSoundB
import StateM5a.StSoundE

/-!
# StateM5a.StSound — the M5b STATE rows are sound (M5a-7 item 3)

For the M5b AIR the prover runs, `A = fullAir D (m5bX host prev post n) nb np` (`M5b.lean`), with
`HostOK host`:

* **`desc_msg`** (one message): if a row receives `DESC(mk, ts, ptr, len)` and
  `SD2(ID_ST + mk, len, ds)`, then `ds = sha256 msg` for a byte list `msg` of length `len` such that
  for every `i < len` the message `HB(ts, ptr + i, msg[i])` was **sent** on `HB` (by the execution
  side).  Proof: the `DESC` sender is the closing `STB` row of the run of message `m = mk`
  (`desc_sent`); the digest is the `SHAS` table's (`sd2_sent`), whose contract
  (`ZkFormal.Sha.sha_digest_contract_closed`, on the second instance) says it is `sha256 msg` with
  every byte `(id, i, msg[i])` received on `SB2`; each such byte was sent by an active `STB` row with
  `ID_ST + m = id` (`sb2_sent`), so `m = mk` (`m < 2^20` rows, `ID_ST + m < p`: no wrap), `j = i`,
  and that row is in the run of `mk`, so it has the closing row's `ts` and `base` (`stb_same`); it
  received `HB(ts, base + j, b)` with `b = msg[i]`.  `len = |msg|` (`|msg| ≤ 2^20` since `j ≤ row`).
  The delivered bytes are `< 256`: they are `UInt8`s of the SHA contract's message, i.e. the `SHAS`
  table itself range-checks every byte it absorbs.
* **`stw_row`** / **`write_sent`** (headline): every `WRITE` message sent on the M5b AIR satisfies
  `WriteOK`: it is `(seg, ts, pairs (sha256 key), pr, vlen, dv)` for an `SREQ(ts, pr, seg, klen, kptr,
  vlen, vptr)` sent by the execution side, `key` the `klen` bytes at `kptr` of call `ts` (`HB`), and
  either `pr = 1` and `dv = pairs (sha256 val)` for the `vlen` bytes `val` at `vptr` of call `ts`
  (`vlen = 0`: `val = []`, via `SHA256_EMPTY = sha256 []`, `StSoundE`), or `pr = 0`, `vlen = 0`,
  `dv = 0^16`.  `write_recv`: the same for every `WRITE` message received (by `WSA`).

No premise beyond `Holds` and `HostOK` (which the prover's AIR satisfies by construction: the host
tape has only `SREQ`/`HB` entries).  No cryptographic assumption.

**Completeness gap (recorded, not fixed):** an empty key (`klen = 0`) has no `STB` run (a run has
`len = j + 1 ≥ 1` bytes), so no `DESC(mk, ts, kptr, 0)` is ever sent and an `STW` row for it cannot
balance; likewise an `STW` row must use `ve = 1` for an empty value.  NEAR allows empty storage
keys, so an honest trace with `storage_write(key = "")` cannot be proved by this AIR.

**What the statement does not say:** that the `HB` bytes are the execution side's memory (one byte
per `(ts, pos)`): that is the producer's memory argument (lane A's `HOSTB`); and that the `SREQ`
message is unique (a request could be served by two `STW` rows if it was sent twice).
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.KcChain StateM5a.Tape StateM5a.M5b NearSpec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- `bs` are the bytes at `ptr, ptr + 1, …` of call `ts`: `HB(ts, ptr + i, bs[i])` was sent for
each `i`. -/
def HBytes (A : Air) (tr : Trace Fp) (pub : List Fp) (ts ptr : Fp) (bs : Bytes) : Prop :=
  ∀ i (h : i < bs.length), [ts, ptr + Fp.ofNat i, Fp.ofNat (bs[i]).toNat] ∈ busList A tr pub B_HB true

/-- **What a `WRITE` message means.** -/
def WriteOK (A : Air) (tr : Trace Fp) (pub : List Fp) (w : List Fp) : Prop :=
  ∃ ts pr seg klen kptr vlen vptr : Fp,
    [ts, pr, seg, klen, kptr, vlen, vptr] ∈ busList A tr pub B_SREQ true ∧
    ∃ (key : Bytes) (dv : List Nat), key.length = klen.toNat ∧ HBytes A tr pub ts kptr key ∧
      ((pr = 1 ∧ ∃ val : Bytes, val.length = vlen.toNat ∧ HBytes A tr pub ts vptr val ∧
          dv = pairs (sha256 val)) ∨
        (pr = 0 ∧ vlen = 0 ∧ dv = List.replicate 16 0)) ∧
      w.map Fp.toNat = [seg.toNat, ts.toNat] ++ pairs (sha256 key) ++ [pr.toNat, vlen.toNat] ++ dv

/-! ## Generic helpers -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem ev_kid (v : Nat) (x : Expr) : ev tr t r pub (K v + x) = (v + ev tr t r pub x) % P := by
  rw [ev_hadd, show K v = Expr.const v from rfl, ev_const, Nat.mod_add_mod]

theorem digest_cols {f : Nat → Expr} {l : Bytes}
    (h : ((List.range 32).map f).map (fun e => e.eval tr t r pub) = l.map (fun x => Fp.ofNat x.toNat)) :
    l.length = 32 ∧ ∀ b, b < 32 → ev tr t r pub (f b) = (l[b]!).toNat := by
  have hl : l.length = 32 := by
    have := congrArg List.length h
    simp only [List.length_map, List.length_range] at this
    omega
  refine ⟨hl, fun b hb => ?_⟩
  have := congrArg (fun l' => l'[b]?) h
  simp only [List.getElem?_map, List.getElem?_range hb, Option.map_some,
    List.getElem?_eq_getElem (show b < l.length by omega)] at this
  have e := congrArg Fp.toNat (Option.some.inj this)
  rw [KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt l[b]; omega)] at e
  change ev tr t r pub (f b) = _ at e
  rw [e, getElem!_pos l b (by omega)]

/-- 32 byte columns as 16 limbs. -/
theorem pack2_ev {f : Nat → Expr} {g : Nat → Nat} (hf : ∀ b, b < 32 → ev tr t r pub (f b) = g b)
    (hg : ∀ b, b < 32 → g b < 256) :
    (pack2 f).map (ev tr t r pub) = (List.range 16).map (fun i => 256 * g (2 * i) + g (2 * i + 1)) := by
  simp only [pack2, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp]
  rw [KeyDigest.ev_limb _ _ (by rw [hf _ (by omega)]; exact hg _ (by omega))
    (by rw [hf _ (by omega)]; exact hg _ (by omega)), hf _ (by omega), hf _ (by omega)]

theorem pairs_range (l : Bytes) (hl : l.length = 32) :
    (List.range 16).map (fun i => 256 * (l[2 * i]!).toNat + (l[2 * i + 1]!).toNat) = pairs l := by
  apply List.ext_getElem?
  intro q
  rcases Nat.lt_or_ge q 16 with h | h
  · rw [KeyDigest.pairs_getElem? _ q (by omega), List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by rw [pairs_length, hl]; omega)]

theorem pack2_digest {f : Nat → Expr} {l : Bytes} (hl : l.length = 32)
    (hf : ∀ b, b < 32 → ev tr t r pub (f b) = (l[b]!).toNat) :
    (pack2 f).map (ev tr t r pub) = pairs l := by
  rw [pack2_ev hf (fun b _ => UInt8.toNat_lt _), pairs_range l hl]

theorem pack2_zero {f : Nat → Expr} (hf : ∀ b, b < 32 → ev tr t r pub (f b) = 0) :
    (pack2 f).map (ev tr t r pub) = List.replicate 16 0 := by
  rw [pack2_ev (g := fun _ => 0) hf (fun _ _ => by decide)]
  decide

theorem empty_lt : ∀ b, b < 32 → SHA256_EMPTY.getD b 0 < 256 := by decide

theorem empty_bytes : ∀ b, b < 32 → (((SHA256_EMPTY.map UInt8.ofNat)[b]!).toNat = SHA256_EMPTY.getD b 0) := by
  decide

end

/-! ## Table access -/

section
variable {D nb np : Nat} {host : List (Nat × Bool × List Nat)} {prev post : NearSpec.Bytes} {n : Nat}

theorem get13 : (fullAir D (m5bX host prev post n) nb np).tables[13]'(by rw [bx_len]; omega) =
    ZkFormal.Sha.Table.table B_SB2 B_SD2 :=
  x_get (t := 13) (k := 1) rfl _ (by rw [m5bX_len]; omega)
theorem get14 : (fullAir D (m5bX host prev post n) nb np).tables[14]'(by rw [bx_len]; omega) = Stb.table :=
  x_get (t := 14) (k := 2) rfl _ (by rw [m5bX_len]; omega)
theorem get15 : (fullAir D (m5bX host prev post n) nb np).tables[15]'(by rw [bx_len]; omega) = Stw.table :=
  x_get (t := 15) (k := 3) rfl _ (by rw [m5bX_len]; omega)

end

/-! ## One message: `DESC` + `SD2` ⇒ `sha256` of `HB` bytes -/

section
variable {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
  {prev post : NearSpec.Bytes} {n : Nat}

theorem stb_hc (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr) :
    ∀ r, r < tr.height 14 → ∀ e ∈ Stb.table.constraints, e.eval tr 14 r pub = 0 := by
  intro r hr e he
  exact hH.constr 14 (by rw [bx_len]; omega) r hr e (by rw [get14]; exact he)

theorem stb_height (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr) :
    tr.height 14 ≤ 2 ^ 20 := by
  have := (hH.logBound 14 (by rw [bx_len]; omega)).2
  rw [get14] at this
  exact Nat.pow_le_pow_right (by decide) this

theorem stw_hc (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr) :
    ∀ r, r < tr.height 15 → ∀ e ∈ Stw.table.constraints, e.eval tr 15 r pub = 0 := by
  intro r hr e he
  exact hH.constr 15 (by rw [bx_len]; omega) r hr e (by rw [get15]; exact he)

/-- **One `STB` message.** -/
theorem desc_msg (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {mk ts ptr len idv : Fp} {ds : List Fp}
    (hD : [mk, ts, ptr, len] ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_DESC false)
    (hS : idv :: len :: ds ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SD2 false)
    (hid : idv.toNat = (ID_ST + mk.toNat) % P) :
    ∃ msg : Bytes, msg.length = len.toNat ∧ ds = (sha256 msg).map (fun x => Fp.ofNat x.toNat) ∧
      HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ts ptr msg := by
  have hc14 := stb_hc hH
  have hH14 := stb_height hH
  -- the closing `STB` row
  obtain ⟨rl, hrl, hll, he⟩ := desc_sent hh (recv_sent hH hD)
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨emk, ets, eptr, -⟩ := he
  have hll' : sv tr 14 rl pub "last" = 1 := eval_one_ev hll
  have hla : sv tr 14 rl pub "act" = 1 := stb_last_act hc14 hrl hll'
  obtain ⟨hmrl, -⟩ := stb_inv hc14 hH14 rl hrl hla
  have hmk : mk.toNat = sv tr 14 rl pub "m" := by rw [emk]; rfl
  -- the `SHAS` digest row
  obtain ⟨d, hd, hdm, he2⟩ := sd2_sent hh (recv_sent hH hS)
  have hL : ZkFormal.Sha.ShaLocal tr 13 pub :=
    ZkFormal.Sha.shaLocal_of_holds hH (busBytes := B_SB2) (busDigest := B_SD2) (by rw [bx_len]; omega) get13
  obtain ⟨mm, dg, -, hdg, hmsg, hbytes⟩ := ZkFormal.Sha.sha_digest_contract_closed hL B_SB2 B_SD2 hd hdm
  rw [hmsg] at he2
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at he2
  obtain ⟨eid, elen, eds⟩ := he2
  -- every message byte comes from a row of the run of `mk`
  have hbyte : ∀ k, k < mm.length → ∃ r', r' < tr.height 14 ∧ sv tr 14 r' pub "act" = 1 ∧
      (Stb.c "j").eval tr 14 r' pub = Fp.ofNat k ∧ (Stb.c "b").eval tr 14 r' pub = Fp.ofNat (mm[k]!).toNat ∧
      sv tr 14 r' pub "m" = sv tr 14 rl pub "m" ∧ sv tr 14 r' pub "j" < 2 ^ 20 := by
    intro k hk
    obtain ⟨r, hr, q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := shas_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 13)
      (by rw [bx_len]; omega) (by rw [get13]; exact hmem) hr hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    obtain ⟨r', hr', ha', e'⟩ := sb2_sent hh (recv_sent hH hmb)
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨e0, e1, e2⟩ := e'
    have ha'' : sv tr 14 r' pub "act" = 1 := eval_one_ev ha'
    obtain ⟨hm', hj'⟩ := stb_inv hc14 hH14 r' hr' ha''
    refine ⟨r', hr', ha'', e1.symm, e2.symm, ?_, by omega⟩
    have h0 := congrArg Fp.toNat e0
    change _ = ev tr 14 r' pub (K ID_ST + Stb.c "m") at h0
    rw [ev_kid, ← eid, hid, hmk, show ID_ST = 67108864 from rfl] at h0
    simp only [sv] at hm' hmrl h0 ⊢
    omega
  have hlen : mm.length ≤ 2 ^ 20 := by
    rcases Nat.lt_or_ge (2 ^ 20) mm.length with h | h
    · obtain ⟨r', -, -, hj, -, -, hjb⟩ := hbyte (2 ^ 20) h
      have := congrArg Fp.toNat hj
      rw [KeyDigest.ofNat_toNat'] at this
      change sv tr 14 r' pub "j" = _ at this
      rw [this] at hjb
      exact absurd hjb (by decide)
    · exact h
  refine ⟨mm, ?_, ?_, ?_⟩
  · rw [elen, KeyDigest.ofNat_toNat', Nat.mod_eq_of_lt (by omega)]
  · rw [eds, hdg]
  · intro i hi
    obtain ⟨r', hr', ha', hj, hb, hm', -⟩ := hbyte i hi
    obtain ⟨-, hts, hbase⟩ := stb_same hc14 hH14 hr' hrl ha' hm' hll'
    have hmb := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 14)
      (by rw [bx_len]; omega) (by rw [get14]; exact stb_hb_r_mem) hr' rfl (ev_one_eval ha')
    have hsent := recv_sent hH hmb
    have e : (rcv B_HB (Stb.c "act") [Stb.c "ts", Stb.c "base" + Stb.c "j", Stb.c "b"]).msgVal tr 14 r' pub =
        [ts, ptr + Fp.ofNat i, Fp.ofNat (mm[i]).toNat] := by
      simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rw [ets]; exact Fp.ext hts
      · show (Stb.c "base").eval tr 14 r' pub + (Stb.c "j").eval tr 14 r' pub = ptr + Fp.ofNat i
        rw [hj, eptr, Fp.ext hbase]
      · rw [hb, getElem!_pos mm i hi]
    rw [e] at hsent
    exact hsent

/-! ## `STW` -/

theorem m_stw_bool_pr : bool (Stw.c "pr") ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_bool_ve : bool (Stw.c "ve") ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_pr_ve : (1 - Stw.c "pr") * Stw.c "ve" ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_pr_vlen : (1 - Stw.c "pr") * Stw.c "vlen" ∈ Stw.constraints := by
  unfold Stw.constraints; simp
theorem m_stw_ve_vlen : Stw.c "ve" * Stw.c "vlen" ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_pr_dv (b : Nat) (hb : b < 32) : (1 - Stw.c "pr") * Stw.c "dv" b ∈ Stw.constraints := by
  unfold Stw.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact Or.inl (Or.inl (Or.inr ⟨b, hb, by simp⟩))
theorem m_stw_ve_dv (b : Nat) (hb : b < 32) :
    Stw.c "ve" * (Stw.c "dv" b - K (SHA256_EMPTY.getD b 0)) ∈ Stw.constraints := by
  unfold Stw.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact Or.inl (Or.inl (Or.inr ⟨b, hb, by simp⟩))
theorem m_stw_bool_ke : bool (Stw.c "ke") ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_ke_klen : Stw.c "ke" * Stw.c "klen" ∈ Stw.constraints := by unfold Stw.constraints; simp
theorem m_stw_ke_dk (b : Nat) (hb : b < 32) :
    Stw.c "ke" * (Stw.c "dk" b - K (SHA256_EMPTY.getD b 0)) ∈ Stw.constraints := by
  unfold Stw.constraints
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨b, hb, rfl⟩

theorem stw_sreq_mem : rcv B_SREQ (Stw.c "act") [Stw.c "ts", Stw.c "pr", Stw.c "seg", Stw.c "klen",
    Stw.c "kptr", Stw.c "vlen", Stw.c "vptr"] ∈ Stw.interactions := memD_mem (by decide)
theorem stw_desck_mem : rcv B_DESC (Stw.c "act" - Stw.c "ke") [Stw.c "mk", Stw.c "ts", Stw.c "kptr", Stw.c "klen"] ∈
    Stw.interactions := memD_mem (by decide)
theorem stw_sd2k_mem : rcv B_SD2 (Stw.c "act" - Stw.c "ke") ([K ID_ST + Stw.c "mk", Stw.c "klen"] ++
    (List.range 32).map fun b => Stw.c "dk" b) ∈ Stw.interactions := memD_mem (by decide)
theorem stw_descv_mem : rcv B_DESC (Stw.c "pr" - Stw.c "ve") [Stw.c "mv", Stw.c "ts", Stw.c "vptr",
    Stw.c "vlen"] ∈ Stw.interactions := memD_mem (by decide)
theorem stw_sd2v_mem : rcv B_SD2 (Stw.c "pr" - Stw.c "ve") ([K ID_ST + Stw.c "mv", Stw.c "vlen"] ++
    (List.range 32).map fun b => Stw.c "dv" b) ∈ Stw.interactions := memD_mem (by decide)

/-- Column `s` of `STW` row `r` (table 15). -/
abbrev wv (tr : Trace Fp) (pub : List Fp) (r : Nat) (s : String) (j : Nat := 0) : Fp :=
  (Stw.c s j).eval tr 15 r pub

/-- A pair of `DESC`/`SD2` receives of an `STW` row (gate `g = 1`). -/
theorem stw_msg (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {r : Nat} (hr : r < tr.height 15) {g : Expr} (sm sl sp sd : String)
    (hD : rcv B_DESC g [Stw.c sm, Stw.c "ts", Stw.c sp, Stw.c sl] ∈ Stw.interactions)
    (hS : rcv B_SD2 g ([K ID_ST + Stw.c sm, Stw.c sl] ++ (List.range 32).map fun b => Stw.c sd b) ∈
      Stw.interactions)
    (hg : g.eval tr 15 r pub = 1) :
    ∃ msg : Bytes, msg.length = (wv tr pub r sl).toNat ∧
      HBytes (fullAir D (m5bX host prev post n) nb np) tr pub (wv tr pub r "ts") (wv tr pub r sp) msg ∧
      (sha256 msg).length = 32 ∧ ∀ b, b < 32 → ev tr 15 r pub (Stw.c sd b) = ((sha256 msg)[b]!).toNat := by
  have hDm := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 15)
    (by rw [bx_len]; omega) (by rw [get15]; exact hD) hr rfl hg
  have hSm := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 15)
    (by rw [bx_len]; omega) (by rw [get15]; exact hS) hr rfl hg
  simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append] at hDm hSm
  obtain ⟨msg, hl, hds, hb⟩ := desc_msg hh hH hDm hSm (by
    show ev tr 15 r pub (K ID_ST + Stw.c sm) = _
    rw [ev_kid]; rfl)
  obtain ⟨hl32, hcols⟩ := digest_cols hds
  exact ⟨msg, hl, hb, hl32, hcols⟩

/-- An `STW` row's key (M5a-8: an empty key `ke = 1` has no `STB` run; `klen = 0`, `dk = sha256 []`). -/
theorem stw_key (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {r : Nat} (hr : r < tr.height 15) (ha : (Stw.c "act").eval tr 15 r pub = 1) :
    ∃ key : Bytes, key.length = (wv tr pub r "klen").toNat ∧
      HBytes (fullAir D (m5bX host prev post n) nb np) tr pub (wv tr pub r "ts") (wv tr pub r "kptr") key ∧
      (sha256 key).length = 32 ∧ ∀ b, b < 32 → ev tr 15 r pub (Stw.c "dk" b) = ((sha256 key)[b]!).toNat := by
  have hc := stw_hc hH r hr
  have h := fun {e : Expr} (he : e ∈ Stw.constraints) => hold rfl hc he
  have hke := bool_le (h m_stw_bool_ke)
  have ha' : ev tr 15 r pub (Stw.c "act") = 1 := eval_one_ev ha
  rcases (show ev tr 15 r pub (Stw.c "ke") = 0 ∨ ev tr 15 r pub (Stw.c "ke") = 1 by omega) with hk | hk
  · have hg : (Stw.c "act" - Stw.c "ke").eval tr 15 r pub = 1 := ev_one_eval (by rw [ev_sub, ha', hk])
    exact stw_msg hh hH hr "mk" "klen" "kptr" "dk" stw_desck_mem stw_sd2k_mem hg
  · have hkl := FieldWsb.wsb_gate hk (h m_stw_ke_klen)
    have hdk : ∀ b, b < 32 → ev tr 15 r pub (Stw.c "dk" b) = ((sha256 [])[b]!).toNat := by
      intro b hb
      have e := eq_of_sub (FieldWsb.wsb_gate hk (h (m_stw_ke_dk b hb)))
      rw [e, show K (SHA256_EMPTY.getD b 0) = Expr.const (SHA256_EMPTY.getD b 0) from rfl, ev_const,
        sha256_empty, empty_bytes b hb]
      apply Nat.mod_eq_of_lt
      have := empty_lt b hb
      omega
    have h32 : (sha256 ([] : Bytes)).length = 32 := by rw [sha256_empty]; rfl
    refine ⟨[], ?_, fun i hi => absurd hi (Nat.not_lt_zero _), h32, hdk⟩
    show 0 = (wv tr pub r "klen").toNat
    exact hkl.symm

/-- **An `STW` row's `WRITE` message.** -/
theorem stw_row (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {r : Nat} (hr : r < tr.height 15) (ha : (Stw.c "act").eval tr 15 r pub = 1) :
    WriteOK (fullAir D (m5bX host prev post n) nb np) tr pub
      ((snd B_WRITE (Stw.c "act") ([Stw.c "seg", Stw.c "ts"] ++ pack2 (fun b => Stw.c "dk" b) ++
        [Stw.c "pr", Stw.c "vlen"] ++ pack2 (fun b => Stw.c "dv" b))).msgVal tr 15 r pub) := by
  have hc := stw_hc hH r hr
  have h := fun {e : Expr} (he : e ∈ Stw.constraints) => hold rfl hc he
  -- the request
  have hq := msg_mem_busList (A := fullAir D (m5bX host prev post n) nb np) (pub := pub) (t := 15)
    (by rw [bx_len]; omega) (by rw [get15]; exact stw_sreq_mem) hr rfl ha
  simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil] at hq
  refine ⟨_, _, _, _, _, _, _, recv_sent hH hq, ?_⟩
  -- the key
  obtain ⟨key, hkl, hkb, hk32, hkc⟩ := stw_key hh hH hr ha
  have hpk := pack2_digest hk32 hkc
  -- the message as naturals
  have hw : ∀ dv : List Nat, (pack2 (fun b => Stw.c "dv" b)).map (ev tr 15 r pub) = dv →
      ((snd B_WRITE (Stw.c "act") ([Stw.c "seg", Stw.c "ts"] ++ pack2 (fun b => Stw.c "dk" b) ++
        [Stw.c "pr", Stw.c "vlen"] ++ pack2 (fun b => Stw.c "dv" b))).msgVal tr 15 r pub).map Fp.toNat =
      [(wv tr pub r "seg").toNat, (wv tr pub r "ts").toNat] ++ pairs (sha256 key) ++
        [(wv tr pub r "pr").toNat, (wv tr pub r "vlen").toNat] ++ dv := by
    intro dv hdv
    simp only [snd, Interaction.msgVal, List.map_map]
    rw [show (Fp.toNat ∘ fun e : Expr => e.eval tr 15 r pub) = ev tr 15 r pub from rfl]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hpk, hdv]
    rfl
  have hpr := bool_le (h m_stw_bool_pr)
  have hve := bool_le (h m_stw_bool_ve)
  rcases (show ev tr 15 r pub (Stw.c "pr") = 0 ∨ ev tr 15 r pub (Stw.c "pr") = 1 by omega) with hp | hp
  · -- a remove
    have g1 : ev tr 15 r pub (1 - Stw.c "pr") = 1 := by rw [ev_sub, ev_one, hp]
    have hvl := FieldWsb.wsb_gate g1 (h m_stw_pr_vlen)
    have hdv0 : ∀ b, b < 32 → ev tr 15 r pub (Stw.c "dv" b) = 0 :=
      fun b hb => FieldWsb.wsb_gate g1 (h (m_stw_pr_dv b hb))
    refine ⟨key, List.replicate 16 0, hkl, hkb, .inr ⟨Fp.ext hp, Fp.ext hvl, rfl⟩, hw _ (pack2_zero hdv0)⟩
  · rcases (show ev tr 15 r pub (Stw.c "ve") = 0 ∨ ev tr 15 r pub (Stw.c "ve") = 1 by omega) with hv | hv
    · -- a non-empty value
      have hg : (Stw.c "pr" - Stw.c "ve").eval tr 15 r pub = 1 :=
        ev_one_eval (by rw [ev_sub, hp, hv])
      obtain ⟨val, hvl, hvb, hv32, hvc⟩ :=
        stw_msg hh hH hr "mv" "vlen" "vptr" "dv" stw_descv_mem stw_sd2v_mem hg
      exact ⟨key, pairs (sha256 val), hkl, hkb, .inl ⟨Fp.ext hp, val, hvl, hvb, rfl⟩,
        hw _ (pack2_digest hv32 hvc)⟩
    · -- an empty value
      have hvl := FieldWsb.wsb_gate hv (h m_stw_ve_vlen)
      have hdv : ∀ b, b < 32 → ev tr 15 r pub (Stw.c "dv" b) = ((sha256 [])[b]!).toNat := by
        intro b hb
        have e := eq_of_sub (FieldWsb.wsb_gate hv (h (m_stw_ve_dv b hb)))
        rw [e, show K (SHA256_EMPTY.getD b 0) = Expr.const (SHA256_EMPTY.getD b 0) from rfl, ev_const,
          sha256_empty, empty_bytes b hb]
        apply Nat.mod_eq_of_lt
        have := empty_lt b hb
        omega
      have h32 : (sha256 ([] : Bytes)).length = 32 := by rw [sha256_empty]; rfl
      refine ⟨key, pairs (sha256 []), hkl, hkb, .inl ⟨Fp.ext hp, [], ?_, ?_, rfl⟩,
        hw _ (pack2_digest h32 hdv)⟩
      · show 0 = (wv tr pub r "vlen").toNat
        exact hvl.symm
      · intro i hi; exact absurd hi (Nat.not_lt_zero _)

/-- **Headline: every `WRITE` message sent on the M5b AIR is a sound STATE write.** -/
theorem write_sent (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {w : List Fp} (hw : w ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_WRITE true) :
    WriteOK (fullAir D (m5bX host prev post n) nb np) tr pub w := by
  obtain ⟨r, hr, ha, rfl⟩ := write_sent_row hh hw
  exact stw_row hh hH hr ha

/-- Every `WRITE` message received (by `WSA`) is a sound STATE write. -/
theorem write_recv (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {w : List Fp} (hw : w ∈ busList (fullAir D (m5bX host prev post n) nb np) tr pub B_WRITE false) :
    WriteOK (fullAir D (m5bX host prev post n) nb np) tr pub w :=
  write_sent hh hH (recv_sent hH hw)

end

end StateM5a.StSound
