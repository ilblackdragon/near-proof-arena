import ZkFormal.NearV3.Sched.Link.KeyPub
import ZkFormal.NearV3.Sched.View.CodecEnc

/-!
# `SchedVal`: the binding interface with `upsV3` (STATUS-V3-SCHED §9)

The codec is the only sender on `SPLEN` and `SPOST`, and no public segment sends on them. So:
* **`codec_splen_sole`**: every `SPLEN` message received by any table is the codec's
  `(τ, 37 + 24·N)` from an instance's first row, with `1 ≤ N < 2^16`, so the value length is
  `L < 2^24`;
* **`codec_spost_sole`**: every `SPOST` message received by any table is the codec's
  `(τ, pos, bpost)` from a codec row whose encoding gate is set.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- Bus ownership for the `upsV3` interface. -/
structure CodecValOwn (AP : AirP) (tc : Nat) : Prop where
  lt : tc < AP.tables.length
  tab : AP.tables[tc]! = Codec.table
  lenOnly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SPLEN → i.send = false
  lenPub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SPLEN → seg.send = false
  postOnly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SPOST → i.send = false
  postPub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SPOST → seg.send = false

theorem codec_splen_i {i : Interaction} (hi : i ∈ Codec.interactions) (hb : i.bus = B_SPLEN) :
    i = Codec.interactions[5]! := by
  rw [Codec.i5_def]
  simp only [Codec.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SCMP, B_SPLEN, B_SPOST, B_S0F, B_SPAR, B_SDL, B_SPUBB, B_SOP, B_SFIN, B_SDG, B_SA0,
      ZkFormal.NearV3.B_VBYTES, ZkFormal.Near.B_BYTES, ZkFormal.Near.B_DIGEST]

theorem codec_spost_i {i : Interaction} (hi : i ∈ Codec.interactions) (hb : i.bus = B_SPOST) :
    i = Codec.interactions[1]! := by
  rw [Codec.i1_def]
  simp only [Codec.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SCMP, B_SPLEN, B_SPOST, B_S0F, B_SPAR, B_SDL, B_SPUBB, B_SOP, B_SFIN, B_SDG, B_SA0,
      ZkFormal.NearV3.B_VBYTES, ZkFormal.Near.B_BYTES, ZkFormal.Near.B_DIGEST]

/-- **Every received `SPLEN` is the codec's `(τ, L)`, with `L = 37 + 24·N < 2^24`.** -/
theorem codec_splen_sole (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SPLEN) (hs : i.send = false)
    (hm : i.multNat tr t r pub ≠ 0) :
    ∃ f, f < tr.height tc ∧ cv tr tc f Codec.kF = 1 ∧
      i.msgVal tr t r pub = [cv tr tc f Codec.tau, 37 + 24 * cv tr tc f Codec.NN].map Fp.ofNat ∧
      1 ≤ cv tr tc f Codec.NN ∧ 37 + 24 * cv tr tc f Codec.NN < 2 ^ 24 := by
  obtain ⟨f, hf, i', hi', hb', -, hmsg, hm'⟩ := recv_matched hH O.lt O.lenOnly O.lenPub ht hr hi hb hs hm
  rw [O.tab] at hi'
  have e := codec_splen_i hi' hb'
  subst e
  have hL : Codec.CLocal tr tc pub := by
    have := local_of_holdsP hH O.lt; rw [O.tab] at this; exact this
  have hH22 : tr.height tc ≤ 2 ^ 22 := height_le hH O.lt O.tab rfl
  rw [Mem.multNat_c (by rw [Codec.i5_def])] at hm'
  have hF : cv tr tc f Codec.kF = 1 := by
    by_cases h : cv tr tc f Codec.kF = 1
    · exact h
    · simp [h] at hm'
  obtain ⟨hN1, hN2, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, hmsg5, -⟩ := Codec.codec_first hL hH22 hf hF
  refine ⟨f, hf, hF, hmsg.symm.trans hmsg5, hN1, ?_⟩
  omega

/-- **Every received `SPOST` is a codec send `(τ, pos, bpost)` from an encoding row.** -/
theorem codec_spost_sole (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SPOST) (hs : i.send = false)
    (hm : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height tc ∧ (Codec.interactions[1]!).multNat tr tc r' pub ≠ 0 ∧
      i.msgVal tr t r pub =
        [cv tr tc r' Codec.tau, cv tr tc r' Codec.pos, cv tr tc r' Codec.bpost].map Fp.ofNat := by
  obtain ⟨r', hr', i', hi', hb', -, hmsg, hm'⟩ := recv_matched hH O.lt O.postOnly O.postPub ht hr hi hb hs hm
  rw [O.tab] at hi'
  have e := codec_spost_i hi' hb'
  subst e
  refine ⟨r', hr', hm', ?_⟩
  rw [← hmsg, Codec.i1_def]
  simp only [Interaction.msgVal, List.map_cons, List.map_nil]
  simp only [cv, Fp.ofNat_toNat]
  rfl

end ZkFormal.NearV3.Sched
