import ZkFormal.NearV3.Sched.Link.InitLink
import ZkFormal.NearV3.Sched.Link.SoundPrep

/-!
# ZkFormal.NearV3.Sched.Link.SoundIds — the codec's id bytes are the layout's (the `SDL` delay line)

Each codec record `k` receives its 16 id bytes on `SDL` as `(τ, k_lo, k_hi, o, b)` and sends them
on as `(τ + 1, k_lo, k_hi, o, b)` (`codec_post`). The public segment sends
`render`'s `dlRecs 0 ids₀` (`ids₀ = Ps[0].ids`), i.e. `(0, k mod 256, k / 256, o, idByte ids₀ k o)`.
Only the codec has `SDL` interactions (`SdlOwn`). By bus balance every received message has a
sender: for τ = 0 the public records (a codec send has head `τ' + 1 ≠ 0`), for τ + 1 the codec
record `k` of block τ (a public record has head 0). By induction on τ:

* **`codec_ids`**: every codec block's id byte `o` of record `k` is `idByte ids₀ k o`;
* **`rowLE_idByte`**: so the record's sender / receiver id (`rowLE bpost … 8`) is
  `ids₀[k / n]` / `ids₀[k % n]` (ids `< 2^64`).

New hypotheses: ownership `SdlOwn` (decidable) and `PubIdx` with
`recs B_SDL true = (render Ps fwd).dlSend` (R1).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- Only the codec has `SDL` interactions (public segments may send and receive). -/
structure SdlOwn (AP : AirP) (tc : Nat) : Prop where
  only : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus ≠ B_SDL

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- **Every received message has a sender**: a public record or a table send. -/
theorem recv_src {AP : AirP} {pub : List F} {tr : Trace F} (hH : HoldsP AP pub tr) {b : Nat}
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = b) (hs : i.send = false)
    (hm : i.multNat tr t r pub ≠ 0) :
    pubCount AP pub b true (i.msgVal tr t r pub) ≠ 0 ∨
      ∃ t', t' < AP.tables.length ∧ ∃ r', r' < tr.height t' ∧ ∃ i' ∈ AP.tables[t']!.interactions,
        i'.bus = b ∧ i'.send = true ∧ i'.msgVal tr t' r' pub = i.msgVal tr t r pub ∧
        i'.multNat tr t' r' pub ≠ 0 := by
  have hbal := hH.balance b (i.msgVal tr t r pub)
  have hrecv : busCount AP.toAir tr pub b false (i.msgVal tr t r pub) ≠ 0 := by
    have h1 := tableBusCount_pos hr hi hm
    rw [hb, hs] at h1
    have h2 := busCount_go_ge tr pub b false (i.msgVal tr t r pub) AP.tables 0 t ht
    simp only [Nat.zero_add] at h2
    unfold busCount; omega
  by_cases hp : pubCount AP pub b true (i.msgVal tr t r pub) = 0
  · right
    have hsend : busCount AP.toAir tr pub b true (i.msgVal tr t r pub) ≠ 0 := by omega
    obtain ⟨t', ht', hc⟩ := busCount_go_pos tr pub b true _ AP.tables 0 hsend
    simp only [Nat.zero_add] at hc
    obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := exists_of_tableBusCount hc
    exact ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩
  · exact Or.inl hp

end

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem sdl_send_i {i : Interaction} (hi : i ∈ interactions) (hb : i.bus = B_SDL) (hs : i.send = true) :
    i = interactions[8]! := by
  rw [i8_def]
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> subst e <;>
    simp_all [B_SCMP, B_SPLEN, B_SPOST, B_S0F, B_SPAR, B_SDL, B_SPUBB, B_SOP, B_SFIN, B_SDG, B_SA0,
      ZkFormal.NearV3.B_VBYTES, ZkFormal.Near.B_BYTES, ZkFormal.Near.B_DIGEST]

/-- **An `SDL` send comes from an id byte of a record.** -/
theorem sdl_row (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {w : Nat} (hw : w < tr.height t)
    (hm : (interactions[8]!).multNat tr t w pub ≠ 0) :
    ∃ f k o, f < tr.height t ∧ cv tr t f kF = 1 ∧ k < cv tr t f NN ∧ o < 16 ∧
      w = f + 5 + 24 * k + o := by
  have K := kinds hL hw
  have hfs : 1 ≤ cv tr t w fS + cv tr t w fR := by
    rcases Nat.eq_zero_or_pos (cv tr t w fS + cv tr t w fR) with h | h
    · exact absurd (mult_zero (i := interactions[8]!) (by rw [i8_def])
        (by simp only [zev_add, zev_c, cur_cv]; omega)) hm
    · exact h
  obtain ⟨f, hfw, hF, hlt⟩ := codec_cover hL hH w hw (by omega)
  have hf : f < tr.height t := by omega
  obtain ⟨-, -, -, -, -, -, HR, RR, -, ZR, -, AR, -⟩ := codec_block hL hH hf hF
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
      have R := RR k hkN o (by omega)
      have F := rrow_flags hL R (by omega)
      rw [e] at F
      by_cases ho16 : o < 16
      · exact ⟨f, k, o, hf, hF, hkN, ho16, e.symm⟩
      · exfalso
        rw [if_neg (by omega), if_neg (by omega)] at F
        omega
    · by_cases hz : w - f < 5 + 24 * cv tr t f NN + 32
      · obtain ⟨-, hk, -⟩ := ZR (w - f - (5 + 24 * cv tr t f NN)) (by omega)
        rw [show f + 5 + 24 * cv tr t f NN + (w - f - (5 + 24 * cv tr t f NN)) = w by omega] at hk
        omega
      · obtain ⟨-, hk, -⟩ := AR (w - f - (5 + 24 * cv tr t f NN + 32)) (by omega)
        rw [show f + 5 + 24 * cv tr t f NN + 32 + (w - f - (5 + 24 * cv tr t f NN + 32)) = w by omega]
          at hk
        omega

end Codec

/-! ## The public id records -/

theorem render_dlSend (Ps : List InstPub) (fwd : List (Nat × Nat)) :
    (render Ps fwd).dlSend = dlRecs 0 (Ps.getD 0 instD).ids := rfl

theorem idByte_lt (ids : List Nat) (k o : Nat) : idByte ids k o < 256 := by
  unfold idByte; exact Nat.mod_lt _ (by decide)

/-- A public `SDL` record matching a codec message `(τ, k_lo, k_hi, o, b)`. -/
theorem dl_pub {ids : List Nat} (hn : ids.length ≤ 64) {M : List Fp}
    (hM : M ∈ (dlRecs 0 ids).map (·.map Fp.ofNat)) {τ klo khi o b k : Nat}
    (hτ : τ < 2013265921) (hlo : klo < 2013265921) (hhi : khi < 2013265921) (ho : o < 16)
    (hb : b < 2013265921) (hk : (klo + 256 * khi) % 2013265921 = k)
    (e : M = [τ, klo, khi, o, b].map Fp.ofNat) :
    τ = 0 ∧ b = idByte ids k o := by
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hM
  simp only [dlRecs, List.mem_flatMap, List.mem_range, List.mem_map] at hR
  obtain ⟨k', hk', o', ho', rfl⟩ := hR
  have hnn : k' < 4096 := by
    have := Nat.mul_le_mul hn hn; omega
  simp only [b2, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.cons.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := e
  have h1 := ofNat_inj' (by decide) hτ e1
  have h2 := ofNat_inj' (by omega) hlo e2
  have h3 := ofNat_inj' (by omega) hhi e3
  have h4 := ofNat_inj' (by omega) (by omega) e4
  have h5 := ofNat_inj' (by have := idByte_lt ids k' o'; omega) hb e5
  have hkk : k = k' := by
    rw [← hk, ← h2, ← h3]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  subst hkk h4
  exact ⟨h1.symm, h5.symm⟩

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **The `SDL` delay line**: every codec block's id byte `o` of record `k` is
`idByte Ps[0].ids k o`. -/
theorem codec_ids (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (DO : SdlOwn AP tc) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecD : I.recs B_SDL true = (render Ps fwd).dlSend)
    (h256 : Ps.length ≤ 256) (hn0 : (Ps.getD 0 instD).ids.length ≤ 64) :
    ∀ τ f, f < tr.height tc → cv tr tc f Codec.kF = 1 → cv tr tc f Codec.tau = τ →
      ∀ k, k < cv tr tc f Codec.NN → ∀ o, o < 16 →
        cv tr tc (f + 5 + 24 * k + o) Codec.bpost = idByte (Ps.getD 0 instD).ids k o := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  have hlen : Ps.length < 2013265921 := by omega
  -- the sender of a received id byte
  have src : ∀ f, f < tr.height tc → cv tr tc f Codec.kF = 1 → ∀ k, k < cv tr tc f Codec.NN →
      ∀ o, o < 16 →
      (cv tr tc f Codec.tau = 0 ∧
          cv tr tc (f + 5 + 24 * k + o) Codec.bpost = idByte (Ps.getD 0 instD).ids k o) ∨
        ∃ f', f' < tr.height tc ∧ cv tr tc f' Codec.kF = 1 ∧
          cv tr tc f' Codec.tau + 1 = cv tr tc f Codec.tau ∧ k < cv tr tc f' Codec.NN ∧
          cv tr tc (f' + 5 + 24 * k + o) Codec.bpost = cv tr tc (f + 5 + 24 * k + o) Codec.bpost := by
    intro f hf hF k hk o ho
    obtain ⟨-, -, hid, -⟩ := Codec.codec_post hL hH22 hf hF
    obtain ⟨hkk, m7, msg7, -, -⟩ := hid k hk o ho
    have hw : f + 5 + 24 * k + o < tr.height tc := by
      obtain ⟨-, -, -, -, -, -, -, RR, -⟩ := Codec.codec_block hL hH22 hf hF
      exact (RR k hk o (by omega)).1
    have hτf : cv tr tc f Codec.tau < Ps.length := (first_par hH O SO I Ps fwd hrecP hlen hf hF).1
    rcases recv_src hH O.lt hw (by rw [O.tab]; exact codec_mem 7 (by decide))
        (by rw [Codec.i7_def]) (by rw [Codec.i7_def]) (by rw [m7]; exact Nat.one_ne_zero) with hp | hs
    · left
      rw [I.count, hrecD, render_dlSend] at hp
      have hmem := List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
      exact dl_pub hn0 hmem (cv_lt _ _) (cv_lt _ _) (cv_lt _ _) ho (cv_lt _ _) hkk msg7
    · right
      obtain ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩ := hs
      have htc : t' = tc := Classical.byContradiction fun hne => DO.only t' ht' hne i' hi' hb'
      rw [htc] at hi' hm' hmsg hr'
      rw [O.tab] at hi'
      have e8 := Codec.sdl_send_i hi' hb' hs'
      subst e8
      obtain ⟨f', k', o', hf', hF', hk', ho', rfl⟩ := Codec.sdl_row hL hH22 hr' hm'
      obtain ⟨-, -, hid', -⟩ := Codec.codec_post hL hH22 hf' hF'
      obtain ⟨hkk', -, -, -, msg8⟩ := hid' k' hk' o' ho'
      rw [msg8, msg7] at hmsg
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
      obtain ⟨e1, e2, e3, e4, e5, -⟩ := hmsg
      have hτf' : cv tr tc f' Codec.tau < Ps.length := (first_par hH O SO I Ps fwd hrecP hlen hf' hF').1
      have h1 := ofNat_inj' (by omega) (cv_lt _ _) e1
      have h2 := ofNat_inj' (cv_lt _ _) (cv_lt _ _) e2
      have h3 := ofNat_inj' (cv_lt _ _) (cv_lt _ _) e3
      have h4 := ofNat_inj' (by omega) (by omega) e4
      have h5 := ofNat_inj' (cv_lt _ _) (cv_lt _ _) e5
      have hkeq : k' = k := by rw [← hkk', ← hkk, h2, h3]
      subst hkeq h4
      exact ⟨f', hf', hF', h1, hk', h5⟩
  intro τ
  induction τ with
  | zero =>
    intro f hf hF hτ k hk o ho
    rcases src f hf hF k hk o ho with ⟨-, h⟩ | ⟨f', -, -, h1, -⟩
    · exact h
    · omega
  | succ τ ih =>
    intro f hf hF hτ k hk o ho
    rcases src f hf hF k hk o ho with ⟨h0, -⟩ | ⟨f', hf', hF', h1, hk', h⟩
    · omega
    · rw [← h]; exact ih f' hf' hF' (by omega) k hk' o ho

end

/-! ## Little-endian ids -/

theorem rowLE_digits {tr : Trace Fp} {t col : Nat} (x : Nat) :
    ∀ (w r s : Nat), (∀ j, j < w → cv tr t (r + j) col = x / 256 ^ (s + j) % 256) →
      Codec.rowLE tr t col r w = x / 256 ^ s % 256 ^ w
  | 0, r, s, _ => by simp [Codec.rowLE, Nat.mod_one]
  | w + 1, r, s, h => by
    simp only [Codec.rowLE]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0, rowLE_digits x w (r + 1) (s + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rw [show r + (j + 1) = r + 1 + j by omega, show s + (j + 1) = s + 1 + j by omega] at this
      exact this)]
    rw [Nat.pow_succ 256 s, ← Nat.div_div_eq_div_mul, Nat.pow_succ 256 w, Nat.mul_comm (256 ^ w) 256,
      Nat.mod_mul]

/-- **The sender / receiver id of a codec record** (`codec_ids`). -/
theorem rowLE_idByte {tr : Trace Fp} {t : Nat} {ids : List Nat} (hids : ∀ x ∈ ids, x < 2 ^ 64)
    {r k : Nat} (h : ∀ o, o < 16 → cv tr t (r + o) Codec.bpost = idByte ids k o) :
    Codec.rowLE tr t Codec.bpost r 8 = ids.getD (k / ids.length) 0 ∧
      Codec.rowLE tr t Codec.bpost (r + 8) 8 = ids.getD (k % ids.length) 0 := by
  have lt : ∀ i, ids.getD i 0 < 2 ^ 64 := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hx : ids[i]? with
    | none => simp
    | some x => exact hids x (List.mem_of_getElem? hx)
  constructor
  · rw [rowLE_digits (ids.getD (k / ids.length) 0) 8 r 0 (fun j hj => by
      rw [h j (by omega)]; unfold idByte; simp [show j < 8 from hj, Nat.mod_eq_of_lt hj])]
    simp only [Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (lt _)
  · rw [rowLE_digits (ids.getD (k % ids.length) 0) 8 (r + 8) 0 (fun j hj => by
      rw [Nat.add_assoc, h (8 + j) (by omega)]; unfold idByte
      simp only [show ¬ (8 + j < 8) by omega, if_false, Nat.zero_add]
      rw [show (8 + j) % 8 = j by omega])]
    simp only [Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (lt _)

end ZkFormal.NearV3.Sched
