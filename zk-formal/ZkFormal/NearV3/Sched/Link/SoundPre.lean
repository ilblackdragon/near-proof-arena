import ZkFormal.NearV3.Sched.Link.SoundIds

/-!
# ZkFormal.NearV3.Sched.Link.SoundPre — the previous state is canonical (`hprev`, stage D step 1)

τ's codec block (unique, `block_unique`) reads the previous `0x0f` value byte by byte: on its
encoding rows `f + i` (`i < L = 37 + 24·N`) it sends `VBYTES (vid, i, bpre_i)` with multiplicity
`pres` (`codec_pre`), `vid` and `pres` received on `S0F` from `upsV3`. With

* `pvOf τ = some [bpre_0 … bpre_{L-1}]` if `pres = 1`, `none` if `pres = 0` (the `VBYTES` bytes),
* `prevOf τ = pvOf τ` as `Bytes`,
* `h0Of τ` = the 32 pre bytes of the hash rows (the SHA input's first half, `codec_trailer`),

**`codec_prevCanon`** proves `PrevCanon Ps[τ].ids (prevOf τ) (codecA0 τ) (h0Of τ)`, the residual
`hprev` of `proc_core'''`:
* present: `codec_pre_encode` gives `State.encode ⟨preLinks, h0⟩`; the ids of `preLinks` are
  `Ps[0].ids` (the `SDL` line, `codec_ids`, `rowLE_idByte`) `= Ps[τ].ids` (one layout,
  `prepD0_ids`); `N = n²` (`codec_hdr`); the allowances are `codecA0 = preA0` (8 bytes, `< 2^64`);
* absent: every pre byte is 0 (`codec_pre`), so `codecA0 = 0` and `h0 = zeroHash = initial.sanityHash`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## Byte strings of rows -/

namespace Codec
variable {tr : Trace Fp} {t : Nat}

theorem rowBytes_map (col : Nat) : ∀ (n r : Nat),
    rowBytes tr t col r n = (List.range n).map fun i => UInt8.ofNat (cv tr t (r + i) col)
  | 0, _ => rfl
  | n + 1, r => by
    rw [rowBytes, rowBytes_map col n (r + 1), List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [show r + 1 + i = r + (i + 1) by omega]

theorem rowBytes_length (col r n : Nat) : (rowBytes tr t col r n).length = n := by
  rw [rowBytes_map]; simp

theorem rowLE_lt (col : Nat) : ∀ {n r : Nat}, (∀ j, j < n → cv tr t (r + j) col < 256) →
    rowLE tr t col r n < 256 ^ n
  | 0, _, _ => by simp [rowLE]
  | n + 1, r, h => by
    simp only [rowLE]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have ih := rowLE_lt col (n := n) (r := r + 1) (fun j hj => by
      have := h (j + 1) (by omega); rwa [show r + (j + 1) = r + 1 + j by omega] at this)
    rw [Nat.pow_succ]
    have : 256 * rowLE tr t col (r + 1) n + 256 ≤ 256 * 256 ^ n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (256 ^ n)]; omega

theorem rowBytes_zero (col : Nat) : ∀ {n r : Nat}, (∀ j, j < n → cv tr t (r + j) col = 0) →
    rowBytes tr t col r n = NearSpec.zeros n
  | 0, _, _ => rfl
  | n + 1, r, h => by
    simp only [rowBytes, NearSpec.zeros]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0, rowBytes_zero col (n := n) (r := r + 1) (fun j hj => by
      have := h (j + 1) (by omega); rwa [show r + (j + 1) = r + 1 + j by omega] at this)]
    rfl

end Codec

/-! ## The previous value of an instance -/

open Classical in
/-- The previous `0x0f` value bytes of τ's codec block, as sent on `VBYTES` (`none` if absent
or without a block). -/
noncomputable def pvOf (tr : Trace Fp) (tc τ : Nat) : Option (List Nat) :=
  if h : ∃ f, f < tr.height tc ∧ cv tr tc f Codec.kF = 1 ∧ cv tr tc f Codec.tau = τ then
    if cv tr tc (Classical.choose h) Codec.pres = 1 then
      some ((List.range (37 + 24 * cv tr tc (Classical.choose h) Codec.NN)).map
        fun i => cv tr tc (Classical.choose h + i) Codec.bpre)
    else none
  else none

/-- The previous state bytes given to the scheduler core. -/
noncomputable def prevOf (tr : Trace Fp) (tc τ : Nat) : Option NearSpec.Bytes :=
  (pvOf tr tc τ).map (List.map UInt8.ofNat)

open Classical in
/-- The previous sanity hash: the pre bytes of τ's hash rows. -/
noncomputable def h0Of (tr : Trace Fp) (tc τ : Nat) : NearSpec.Bytes :=
  if h : ∃ f, f < tr.height tc ∧ cv tr tc f Codec.kF = 1 ∧ cv tr tc f Codec.tau = τ then
    Codec.rowBytes tr tc Codec.bpre (Classical.choose h + 5 + 24 * cv tr tc (Classical.choose h) Codec.NN) 32
  else NearSpec.zeroHash

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- `pvOf` / `h0Of` at a block. -/
theorem pre_block (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    pvOf tr tc (cv tr tc f Codec.tau) =
        (if cv tr tc f Codec.pres = 1 then
          some ((List.range (37 + 24 * cv tr tc f Codec.NN)).map fun i => cv tr tc (f + i) Codec.bpre)
        else none) ∧
      h0Of tr tc (cv tr tc f Codec.tau) =
        Codec.rowBytes tr tc Codec.bpre (f + 5 + 24 * cv tr tc f Codec.NN) 32 := by
  have hex : ∃ f', f' < tr.height tc ∧ cv tr tc f' Codec.kF = 1 ∧ cv tr tc f' Codec.tau = cv tr tc f Codec.tau :=
    ⟨f, hf, hF, rfl⟩
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have e := block_unique hH O SO I Ps fwd hrec hlen h1 h2 hf hF h3
  unfold pvOf h0Of
  rw [dif_pos hex, dif_pos hex, e]
  constructor <;> first | rfl | trivial

/-- **The `VBYTES` traffic of the previous value**: when present, τ's block received
`S0F (τ, 1, vid)` and sends `VBYTES (vid, i, pv_i)` once for each `i < |pv|`; when absent it
received `S0F (τ, 0, vid)` and sends no `VBYTES`. -/
theorem pvOf_vbytes (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    (Codec.interactions[4]!).multNat tr tc f pub = 1 ∧
    (Codec.interactions[4]!).msgVal tr tc f pub =
      [cv tr tc f Codec.tau, cv tr tc f Codec.pres, cv tr tc f Codec.vid].map Fp.ofNat ∧
    (∀ pv, pvOf tr tc (cv tr tc f Codec.tau) = some pv →
      cv tr tc f Codec.pres = 1 ∧ pv.length = 37 + 24 * cv tr tc f Codec.NN ∧
      ∀ i, i < pv.length → (Codec.interactions[0]!).multNat tr tc (f + i) pub = 1 ∧
        (Codec.interactions[0]!).msgVal tr tc (f + i) pub =
          [cv tr tc f Codec.vid, i, pv.getD i 0].map Fp.ofNat) ∧
    (pvOf tr tc (cv tr tc f Codec.tau) = none →
      cv tr tc f Codec.pres = 0 ∧
      ∀ i, i < 37 + 24 * cv tr tc f Codec.NN → (Codec.interactions[0]!).multNat tr tc (f + i) pub = 0) := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  obtain ⟨m4, msg4, -⟩ := Codec.codec_first hL hH22 hf hF
  obtain ⟨hp1, V, -⟩ := Codec.codec_pre hL hH22 hf hF
  have hpv := (pre_block hH O SO I Ps fwd hrec hlen hf hF).1
  refine ⟨m4, msg4, fun pv h => ?_, fun h => ?_⟩
  · rw [hpv] at h
    split at h
    · next hp =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.length_map, List.length_range]
      refine ⟨hp, trivial, fun i hi => ?_⟩
      obtain ⟨m0, msg0⟩ := V i (by omega)
      refine ⟨by rw [m0, hp], ?_⟩
      rw [msg0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    · cases h
  · rw [hpv] at h
    split at h
    · cases h
    · next hp =>
      have hp0 : cv tr tc f Codec.pres = 0 := by omega
      exact ⟨hp0, fun i hi => by rw [(V i (by omega)).1, hp0]⟩

/-- **`hprev`**: the previous state is the canonical encoding of the allowances τ's codec block
decodes. -/
theorem codec_prevCanon {tp tm tcmp ts tch tg tsd tcd : Nat} {Ps : List InstPub}
    (C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps) (DO : SdlOwn AP tcd)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecD : I.recs B_SDL true = (render Ps fwd).dlSend)
    (hsame : ∀ τ, τ < Ps.length → (Ps.getD τ instD).ids = (Ps.getD 0 instD).ids)
    {τ : Nat} (hτ : τ < Ps.length) :
    PrevCanon (Ps.getD τ instD).ids (prevOf tr tcd τ) (codecA0 tr tcd τ) (h0Of tr tcd τ) := by
  have hH := C.hH
  have h256 := C.h256
  have hlen : Ps.length < 2013265921 := by omega
  have hL := codec_local hH C.OC
  have hH22 := codec_h22 hH C.OC
  obtain ⟨f, hf, hF, rfl⟩ := C.codec_exists I fwd hrecP hτ
  have PO := C.hP _ hτ
  have P0 := C.hP 0 (by omega)
  have hA0 := C.codecA0_eq I fwd hrecP hf hF
  obtain ⟨-, -, hNN, -⟩ := codec_hdr hH C.OC C.SO I Ps fwd hrecP h256 hf hF PO
  obtain ⟨hpv, hh0⟩ := pre_block hH C.OC C.SO I Ps fwd hrecP hlen hf hF
  obtain ⟨hp1, -, habs, -, -, hpal, -⟩ := Codec.codec_pre hL hH22 hf hF
  have hids := hsame _ hτ
  generalize hP : Ps.getD (cv tr tcd f Codec.tau) instD = P at hNN hids PO
  unfold prevOf
  rw [hA0, hh0, hpv]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp1 with h0 | h1
  · -- absent
    left
    rw [if_neg (by omega)]
    refine ⟨rfl, fun l => ?_, ?_⟩
    · unfold preA0
      split
      · next hl =>
        apply (Codec.rowLE_zero_iff).2
        intro j hj
        have := habs h0 (5 + 24 * l + 16 + j) (by omega)
        rwa [show f + (5 + 24 * l + 16 + j) = f + 5 + 24 * l + 16 + j by omega] at this
      · rfl
    · show _ = NearSpec.zeros 32
      apply Codec.rowBytes_zero
      intro j hj
      have := habs h0 (5 + 24 * cv tr tcd f Codec.NN + j) (by omega)
      rwa [show f + (5 + 24 * cv tr tcd f Codec.NN + j) = f + 5 + 24 * cv tr tcd f Codec.NN + j by omega]
        at this
  · -- present
    right
    rw [if_pos h1]
    refine ⟨?_, Codec.rowBytes_length _ _ _, fun l => ?_⟩
    · simp only [Option.map_some, Option.some.injEq]
      rw [List.map_map]
      have e1 : ((List.range (37 + 24 * cv tr tcd f Codec.NN)).map
          (UInt8.ofNat ∘ fun i => cv tr tcd (f + i) Codec.bpre)) =
          Codec.rowBytes tr tcd Codec.bpre f (37 + 24 * cv tr tcd f Codec.NN) := by
        rw [Codec.rowBytes_map]; rfl
      rw [e1, Codec.codec_pre_encode hL hH22 hf hF h1]
      congr 2
      -- the links
      unfold Codec.preLinks canonLinks
      rw [hNN, InstPub.n]
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.1 hk
      have hkN : k < cv tr tcd f Codec.NN := by rw [hNN, InstPub.n]; exact hk'
      have hid := rowLE_idByte (ids := P.ids) (r := f + 5 + 24 * k) (k := k)
        (by intro x hx; exact PO.ids64 x hx) (fun o ho => by
          rw [hids]
          exact codec_ids hH C.OC C.SO DO I Ps fwd hrecP hrecD h256 (by have := P0.n64; exact this)
            _ f hf hF rfl k hkN o ho)
      rw [hid.1, hid.2]
      unfold preA0
      rw [if_pos hkN]
    · unfold preA0
      split
      · next hl =>
        have := Codec.rowLE_lt (tr := tr) (t := tcd) Codec.bpre (n := 8)
          (r := f + 5 + 24 * l + 16) (fun j hj => hpal l hl j hj)
        exact this
      · exact Nat.two_pow_pos 64

end

end ZkFormal.NearV3.Sched
