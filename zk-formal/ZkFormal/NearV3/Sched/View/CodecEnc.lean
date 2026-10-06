import ZkFormal.NearV3.Sched.View.CodecRec

/-!
# ZkFormal.NearV3.Sched.View.CodecEnc — the encoding and the trailer of an instance of `schV3`

For an instance block (`codec_block`) at first row `f`, `N = NN`, `τ = tau` of row `f`,
`L = 5 + 24N + 32` encoding rows `f … f + L − 1` (`pos = i` on row `f + i`), `z = f + 5 + 24N`
the first hash row, `z + 32` the first ash row:

* **`codec_first`**: the first row's `S0F (τ, pres, vid)`, `SPLEN (τ, 37 + 24N)`,
  `SPAR (τ, 0, n, N₀, N₁, base₀₋₂, fair₀₋₂)` and `base`, `fair` from their bytes (mod `P`);
* **`codec_post`**: `SPOST (τ, i, bpost)` once on every encoding row; the post bytes are
  `[0] ++ u32 N` (header), per record the 16 id bytes received on the delay line
  `SDL (τ, klo, khi, o, b)` (and passed on as `SDL (τ + 1, …)`, `klo + 256·khi ≡ k`) and
  `u64 afin` (allowance, `afin < 2^24`), then the 32 bytes of the received `DIGEST`;
* **`codec_pre`**: `VBYTES (vid, i, bpre)` with multiplicity `pres` on every encoding row;
  `pres = 0 ⇒` every pre byte is 0; header and id pre bytes are `pres·bpost`; allowance pre bytes
  are bytes; hash-row pre bytes are the SHA input bytes `bsha`;
* **`codec_trailer`**: hash row `j` sends `BYTES (11 + 16τ, j, bpre)`; ash row `j` sends
  `BYTES (11 + 16τ, 32 + j, b)` for the byte `b` it receives in the public record
  `SPUBB (τ, 2, j, b, 0, 0, 0)`.
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

/-- Byte `j` of `leN w x`. -/
theorem leN_getD : ∀ (w x j : Nat), j < w → ((NearSpec.leN w x).getD j 0).toNat = x / 256 ^ j % 256
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | w + 1, x, 0, _ => by simp [NearSpec.leN]
  | w + 1, x, j + 1, h => by
    simp only [NearSpec.leN, List.getD_cons_succ]
    rw [leN_getD w (x / 256) j (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ j)]

/-- The header bytes `[0] ++ u32 N` for `N < 65536`. -/
theorem hdr_bytes {N j : Nat} (hN : N < 65536) (hj : j < 5) :
    (([0] ++ NearSpec.u32 N).getD j 0).toNat =
      [0, N % 256, N / 256, 0, 0].getD j 0 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with h | h | h | h | h <;> subst h
  · rfl
  · simp only [List.singleton_append, List.getD_cons_succ, NearSpec.u32]
    rw [leN_getD 4 N 0 (by omega)]; simp
  · simp only [List.singleton_append, List.getD_cons_succ, NearSpec.u32]
    rw [leN_getD 4 N 1 (by omega)]; simp; omega
  · simp only [List.singleton_append, List.getD_cons_succ, NearSpec.u32]
    rw [leN_getD 4 N 2 (by omega)]; simp; omega
  · simp only [List.singleton_append, List.getD_cons_succ, NearSpec.u32]
    rw [leN_getD 4 N 3 (by omega)]; simp; omega

/-- The allowance bytes `u64 a` for `a = b₀ + 256·b₁ + 65536·b₂`, `bᵢ < 256`. -/
theorem alw_bytes {b0 b1 b2 o : Nat} (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (ho : o < 8) :
    ((NearSpec.u64 (b0 + 256 * b1 + 65536 * b2)).getD o 0).toNat = [b0, b1, b2, 0, 0, 0, 0, 0].getD o 0 := by
  unfold NearSpec.u64
  rw [leN_getD 8 _ o ho]
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7)
    with h | h | h | h | h | h | h | h <;> subst h <;> simp <;> omega

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem i0_def : interactions[0]! = Interaction.mk ZkFormal.NearV3.B_VBYTES [c vbg]
    [c vid, c pos, c bpre] true := rfl
theorem i1_def : interactions[1]! = Interaction.mk B_SPOST [encG] [c tau, c pos, c bpost] true := rfl
theorem i2_def : interactions[2]! = Interaction.mk ZkFormal.Near.B_BYTES [.add (c kZ) (c kA)]
    [shaId, c sj, c bsha] true := rfl
theorem i3_def : interactions[3]! = Interaction.mk ZkFormal.Near.B_DIGEST [c dgg]
    ([shaId, k 64] ++ (List.range 32).map fun i => c (reg i)) false := rfl
theorem i4_def : interactions[4]! = Interaction.mk B_S0F [c kF] [c tau, c pres, c vid] false := rfl
theorem i5_def : interactions[5]! = Interaction.mk B_SPLEN [c kF]
    [c tau, .add (k 37) (smul 24 (c NN))] true := rfl
theorem i6_def : interactions[6]! = Interaction.mk B_SPAR [c kF]
    [c tau, k 0, c nn, c (reg 1), c (reg 2), c (reg 5), c (reg 6), c (reg 7), c (reg 8),
      c (reg 9), c (reg 10)] false := rfl
theorem i7_def : interactions[7]! = Interaction.mk B_SDL [.add (c fS) (c fR)]
    [c tau, c klo, c khi, oE, c bpost] false := rfl
theorem i8_def : interactions[8]! = Interaction.mk B_SDL [.add (c fS) (c fR)]
    [.add (c tau) (k 1), c klo, c khi, oE, c bpost] true := rfl

theorem ev_shaId (w : Nat) : shaId.eval tr t w pub = Fp.ofNat (11 + 16 * cv tr t w tau) :=
  ev_of (by simp only [shaId, zev_add, zev_smul, zev_c, zev_k, cur_cv, K_SCH]; omega)

/-! ## First row -/

/-- **First row of an instance.** -/
theorem codec_first (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) :
    (interactions[4]!).multNat tr t f pub = 1 ∧
    (interactions[4]!).msgVal tr t f pub = [cv tr t f tau, cv tr t f pres, cv tr t f vid].map Fp.ofNat ∧
    (interactions[5]!).multNat tr t f pub = 1 ∧
    (interactions[5]!).msgVal tr t f pub = [cv tr t f tau, 37 + 24 * cv tr t f NN].map Fp.ofNat ∧
    (interactions[6]!).multNat tr t f pub = 1 ∧
    (interactions[6]!).msgVal tr t f pub =
      [cv tr t f tau, 0, cv tr t f nn, cv tr t f NN % 256, cv tr t f NN / 256, cv tr t f (reg 5),
        cv tr t f (reg 6), cv tr t f (reg 7), cv tr t f (reg 8), cv tr t f (reg 9),
        cv tr t f (reg 10)].map Fp.ofNat ∧
    cv tr t f base = (cv tr t f (reg 5) + 256 * cv tr t f (reg 6) + 65536 * cv tr t f (reg 7)) %
      2013265921 ∧
    cv tr t f fair = (cv tr t f (reg 8) + 256 * cv tr t f (reg 9) + 65536 * cv tr t f (reg 10)) %
      2013265921 := by
  obtain ⟨-, -, -, -, -, -, -, hb, hfa⟩ := first_row hL hf hF
  obtain ⟨-, -, hN, b1, b2, -⟩ := codec_block hL hH hf hF
  have m : zev (tenv tr t f pub) (c kF) = 1 := by simp only [zev_c, cur_cv]; rw [hF]; rfl
  refine ⟨mult_of rfl m, ?_, mult_of rfl m, ?_, mult_of rfl m, ?_, hb, hfa⟩
  · rw [i4_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
  · rw [i5_def]
    have e : (Expr.add (k 37) (smul 24 (c NN))).eval tr t f pub = Fp.ofNat (37 + 24 * cv tr t f NN) :=
      ev_of (by simp only [zev_add, zev_smul, zev_c, zev_k, cur_cv]; omega)
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, e]
  · rw [i6_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k]
    rw [show cv tr t f NN % 256 = cv tr t f (reg 1) by omega,
      show cv tr t f NN / 256 = cv tr t f (reg 2) by omega]

/-! ## Post bytes -/

/-- **Post bytes.** -/
theorem codec_post (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) :
    -- SPOST on every encoding row
    (∀ i, i < 5 + 24 * cv tr t f NN + 32 →
      (interactions[1]!).multNat tr t (f + i) pub = 1 ∧
      (interactions[1]!).msgVal tr t (f + i) pub =
        [cv tr t f tau, i, cv tr t (f + i) bpost].map Fp.ofNat) ∧
    -- header
    (∀ j, j < 5 → cv tr t (f + j) bpost = (([0] ++ NearSpec.u32 (cv tr t f NN)).getD j 0).toNat) ∧
    -- id bytes: the delay line
    (∀ k, k < cv tr t f NN → ∀ o, o < 16 →
      (cv tr t (f + 5 + 24 * k + o) klo + 256 * cv tr t (f + 5 + 24 * k + o) khi) % 2013265921 = k ∧
      (interactions[7]!).multNat tr t (f + 5 + 24 * k + o) pub = 1 ∧
      (interactions[7]!).msgVal tr t (f + 5 + 24 * k + o) pub =
        [cv tr t f tau, cv tr t (f + 5 + 24 * k + o) klo, cv tr t (f + 5 + 24 * k + o) khi, o,
          cv tr t (f + 5 + 24 * k + o) bpost].map Fp.ofNat ∧
      (interactions[8]!).multNat tr t (f + 5 + 24 * k + o) pub = 1 ∧
      (interactions[8]!).msgVal tr t (f + 5 + 24 * k + o) pub =
        [cv tr t f tau + 1, cv tr t (f + 5 + 24 * k + o) klo, cv tr t (f + 5 + 24 * k + o) khi, o,
          cv tr t (f + 5 + 24 * k + o) bpost].map Fp.ofNat) ∧
    -- allowance bytes
    (∀ k, k < cv tr t f NN →
      cv tr t (f + 5 + 24 * k + 23) afin < 2 ^ 24 ∧
      ∀ o, o < 8 → cv tr t (f + 5 + 24 * k + 16 + o) bpost =
        ((NearSpec.u64 (cv tr t (f + 5 + 24 * k + 23) afin)).getD o 0).toNat) ∧
    -- digest
    (interactions[3]!).multNat tr t (f + 5 + 24 * cv tr t f NN) pub = 1 ∧
    (interactions[3]!).msgVal tr t (f + 5 + 24 * cv tr t f NN) pub =
      ([11 + 16 * cv tr t f tau, 64] ++
        (List.range 32).map fun i => cv tr t (f + 5 + 24 * cv tr t f NN) (reg i)).map Fp.ofNat ∧
    (∀ j, j < 32 → cv tr t (f + 5 + 24 * cv tr t f NN + j) bpost =
      cv tr t (f + 5 + 24 * cv tr t f NN) (reg j)) := by
  obtain ⟨hN1, hN, hNe, b1, b2, -, HR, RR, -, ZR, hdg, -⟩ := codec_block hL hH hf hF
  -- every encoding row
  have enc : ∀ i, i < 5 + 24 * cv tr t f NN + 32 →
      f + i < tr.height t ∧ cv tr t (f + i) kH + cv tr t (f + i) kR + cv tr t (f + i) kZ = 1 ∧
      cv tr t (f + i) pos = i ∧ IC tr t (f + i) f := by
    intro i hi
    by_cases h5 : i < 5
    · obtain ⟨hw, hk, hp, hic, -⟩ := HR i h5
      have := kinds hL hw
      exact ⟨hw, by omega, hp, hic⟩
    · by_cases hr : i < 5 + 24 * cv tr t f NN
      · obtain ⟨hw, hk, -, -, -, hp, hic⟩ := RR ((i - 5) / 24) (by omega) ((i - 5) % 24) (by omega)
        have e : f + 5 + 24 * ((i - 5) / 24) + (i - 5) % 24 = f + i := by omega
        rw [e] at hw hk hp hic
        have := kinds hL hw
        exact ⟨hw, by omega, by rw [hp]; omega, hic⟩
      · obtain ⟨hw, hk, -, hp, hic, -⟩ := ZR (i - 5 - 24 * cv tr t f NN) (by omega)
        have e : f + 5 + 24 * cv tr t f NN + (i - 5 - 24 * cv tr t f NN) = f + i := by omega
        rw [e] at hw hk hp hic
        have := kinds hL hw
        exact ⟨hw, by omega, by rw [hp]; omega, hic⟩
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun k hk o ho => ?_, fun k hk => ?_, ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨hw, he, hp, hic⟩ := enc i hi
    refine ⟨mult_of rfl (by simp only [encG, zev_add, zev_c, cur_cv]; omega), ?_⟩
    rw [i1_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
    rw [hic tau (by simp [instCols]), hp]
  · obtain ⟨hw, hk, -, -, hreg⟩ := HR j hj
    obtain ⟨-, -, h0, h3, h4, -⟩ := first_row hL hf hF
    rw [hdr_bytes hN hj, (hdr_row hL hw hk).1, hreg 0 (by omega), Nat.zero_add]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with h | h | h | h | h <;> subst h
    · exact h0
    · show _ = cv tr t f NN % 256; omega
    · show _ = cv tr t f NN / 256; omega
    · exact h3
    · exact h4
  · have R := RR k hk o (by omega)
    have F := rrow_flags hL R (by omega)
    obtain ⟨hw, hkR, -, hg, hki, -, hic⟩ := R
    have hτ := hic tau (by simp [instCols])
    obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c kR) (sub (c kidx) (.add (c klo) (smul 256 (c khi)))))
      (by simp [constraints, cRec])
    zs c1 [hkR]
    have := lt (tr := tr) (t := t) (f + 5 + 24 * k + o) kidx
    have hsr : cv tr t (f + 5 + 24 * k + o) fS + cv tr t (f + 5 + 24 * k + o) fR = 1 := by
      rw [F.1, F.2.1]; split <;> split <;> omega
    have hoE : oE.eval tr t (f + 5 + 24 * k + o) pub = Fp.ofNat o :=
      ev_of (by
        simp only [oE, zev_add, zev_smul, zev_c, cur_cv]
        rw [F.2.1, hg]; split <;> omega)
    have m : zev (tenv tr t (f + 5 + 24 * k + o) pub) (.add (c fS) (c fR)) = 1 := by
      simp only [zev_add, zev_c, cur_cv]; omega
    refine ⟨by
        have hk' : (k : Int) = cv tr t (f + 5 + 24 * k + o) kidx := by rw [hki]
        generalize cv tr t (f + 5 + 24 * k + o) klo = a at c1 ⊢
        generalize cv tr t (f + 5 + 24 * k + o) khi = b at c1 ⊢
        omega,
      mult_of rfl m, ?_, mult_of rfl m, ?_⟩
    · rw [i7_def]
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, hoE]
      rw [hτ]
    · rw [i8_def]
      have e : (Expr.add (c tau) (ZkFormal.Chacha.Table.E.k 1)).eval tr t (f + 5 + 24 * k + o) pub = Fp.ofNat (cv tr t f tau + 1) :=
        ev_of (by simp only [zev_add, zev_c, zev_k, cur_cv]; rw [hτ]; omega)
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, hoE, e]
  · have hR := RR k hk
    obtain ⟨-, -, hafin, hz, -⟩ := alw_walk hL hR
    have By := fun o (ho : o < 24) => bytes hL (hR o ho).1 (by
      have := kinds hL (hR o ho).1; have := (hR o ho).2.1; omega)
    have b16 := (By 16 (by omega)).2.1; have b17 := (By 17 (by omega)).2.1
    have b18 := (By 18 (by omega)).2.1
    refine ⟨by rw [hafin]; omega, fun o ho => ?_⟩
    rw [hafin, alw_bytes b16 b17 b18 ho]
    rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7)
      with h | h | h | h | h | h | h | h <;> subst h
    · rfl
    · rfl
    · rfl
    · exact hz 19 (by omega) (by omega)
    · exact hz 20 (by omega) (by omega)
    · exact hz 21 (by omega) (by omega)
    · exact hz 22 (by omega) (by omega)
    · exact hz 23 (by omega) (by omega)
  · exact mult_of rfl (by simp only [zev_c, cur_cv]; rw [hdg]; rfl)
  · obtain ⟨-, -, -, -, hic, -⟩ := ZR 0 (by omega)
    have hτ : cv tr t (f + 5 + 24 * cv tr t f NN) tau = cv tr t f tau := by
      have := hic tau (by simp [instCols]); simpa using this
    rw [i3_def]
    simp only [Interaction.msgVal, List.map_append, List.map_cons, List.map_nil, ev_shaId, ev_k,
      List.map_map, hτ]
    congr 2
    funext i
    exact ev_c _ _
  · obtain ⟨hw, hk, -, -, -, hreg⟩ := ZR j hj
    obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c kZ) (sub (c bpost) (c (reg 0)))) (by simp [constraints, cTrl])
    zs c1 [hk]
    have := lt (tr := tr) (t := t) (f + 5 + 24 * cv tr t f NN + j) bpost
    have := lt (tr := tr) (t := t) (f + 5 + 24 * cv tr t f NN + j) (reg 0)
    rw [← Nat.zero_add j, ← hreg 0 (by omega)]
    rw [Nat.zero_add]
    omega

end

end ZkFormal.NearV3.Sched.Codec
