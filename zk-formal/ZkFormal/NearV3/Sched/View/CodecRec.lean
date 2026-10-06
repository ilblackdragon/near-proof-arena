import ZkFormal.NearV3.Sched.View.CodecLink

/-!
# ZkFormal.NearV3.Sched.View.CodecRec — the link pass and the messages of a record of `schV3`

Record `k` of an instance block: rows `w = f + 5 + 24k` (start, `rs`), `b = w + 18` (allowance
byte 2: `A0` receive, comparator), `e = w + 23` (end, `rend`).

* `rec_data`: `al, gb, srcC, hasC, useC` are the same on the 24 rows;
* **`codec_link`**: with the comparator's answer `cb = [MA ≤ apR + fair]` at `b` (the link layer
  supplies it from `cmp_sound` on the `SCMP` message of `b`, see `codec_rec_msgs`) and
  `apR + fair < P`: `a1 = bigR ? MA : min(apR + fair, MA)`, `g2 = al·base`,
  `a2 + al·base ≡ a1 (mod P)`, `a2 = a1 − al·base` when `al·base ≤ a1`;
* **`codec_rec_msgs`**: `SDG (τ, k, al, gb, srcC, hasC, useC)` received at `w`;
  `SA0 (τ, srcC, apR, bigR)` received at `b` with multiplicity `hasC` (`hasC = 0 ⇒ apR = bigR = 0`);
  `SCMP (apR + fair, MA, cb)` at `b`; `INIT (16384τ + k, 0, OP_INIT, al, a2, g2, 0, 1)` on `SOP` (`c = 1`: a link address),
  `FIN (16384τ + k, afin, gfin)` on `SFIN`, `SA0 (τ, k, ap, bF)` sent with multiplicity `useC`
  (`ap` = the three low pre allowance bytes LE, `bF` = some higher pre byte nonzero) at `e`;
  in instance 0 the forwarding `SCMP (gfin + gb, ft, 1)` and `SPUBB (τ, 4, klo, khi, ft₀, ft₁, ft₂)`
  at `e` (none in other instances).
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Evaluation of messages and multiplicities -/

theorem ev_c (w x : Nat) : (c x).eval tr t w pub = Fp.ofNat (cv tr t w x) :=
  (Fp.ofNat_toNat _).symm

theorem ev_k (w v : Nat) : (k v).eval tr t w pub = Fp.ofNat v := rfl

theorem ev_of {e : Expr} {w v : Nat} (h : zev (tenv tr t w pub) e = (v : Int)) :
    e.eval tr t w pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

theorem mult_of {i : Interaction} {e : Expr} {w : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr t w pub) e = 1) : i.multNat tr t w pub = 1 := by
  unfold Interaction.multNat
  rw [hm]
  simp only [Interaction.multNat.go]
  rw [ev_of (v := 1) (by rw [h]; rfl)]
  rfl

theorem mult_zero {i : Interaction} {e : Expr} {w : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr t w pub) e = 0) : i.multNat tr t w pub = 0 := by
  unfold Interaction.multNat
  rw [hm]
  simp only [Interaction.multNat.go]
  rw [ev_of (v := 0) (by rw [h]; rfl)]
  decide

theorem mult_bit {i : Interaction} {e : Expr} {w x : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr t w pub) e = (cv tr t w x : Int)) (hx : cv tr t w x ≤ 1) :
    i.multNat tr t w pub = cv tr t w x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with h0 | h1
  · rw [h0]; exact mult_zero hm (by rw [h, h0]; rfl)
  · rw [h1]; exact mult_of hm (by rw [h, h1]; rfl)

theorem i9_def : interactions[9]! = Interaction.mk B_SPUBB [.add (c kA) (c fwg)]
    [c tau, .add (smul 2 (c kA)) (smul 4 (c fwg)), c pm0, c pm1, c (fb 0), c (fb 1), c (fb 2)] false := rfl
theorem i10_def : interactions[10]! = Interaction.mk B_SOP [c rend]
    [aLE, k 0, k OP_INIT, c al, c a2, c g2, k 0, k 1] true := rfl
theorem i11_def : interactions[11]! = Interaction.mk B_SFIN [c rend] [aLE, c afin, c gfin] false := rfl
theorem i12_def : interactions[12]! = Interaction.mk B_SDG [c rs]
    [c tau, c kidx, c al, c gb, c srcC, c hasC, c useC] false := rfl
theorem i13_def : interactions[13]! = Interaction.mk B_SA0 [c u0g] [c tau, c kidx, c ap, c bF] true := rfl
theorem i14_def : interactions[14]! = Interaction.mk B_SA0 [c a0g] [c tau, c srcC, c apR, c bigR] false := rfl
theorem i15_def : interactions[15]! = Interaction.mk B_SCMP [c cg] [c cx, c cy, c cbit] true := rfl

/-! ## Record data -/

/-- **Record data** is the same on the record's 24 rows. -/
theorem rec_data (hL : CLocal tr t pub) {f k : Nat} (hR : ∀ o, o < 24 → RRow tr t f k o) {x : Nat}
    (hx : x ∈ [al, gb, srcC, hasC, useC]) :
    ∀ o, o < 24 → cv tr t (f + 5 + 24 * k + o) x = cv tr t (f + 5 + 24 * k) x := by
  intro o
  induction o with
  | zero => intro _; rfl
  | succ o ih =>
    intro ho
    have hR' := hR o (by omega)
    have F := rrow_flags hL hR' (by omega)
    have hrd : cv tr t (f + 5 + 24 * k + o) rend = 0 := by rw [F.2.2.2.2.1, if_neg (by omega)]
    have := (rec_next hL hR'.1 hR'.2.1 hrd hx).2
    rw [show f + 5 + 24 * k + (o + 1) = f + 5 + 24 * k + o + 1 by omega, this]
    exact ih (by omega)

/-! ## The link pass -/

/-- **Link pass at a record end.** -/
theorem codec_link (hL : CLocal tr t pub) {f k : Nat} (hR : ∀ o, o < 24 → RRow tr t f k o)
    (hcb : cv tr t (f + 5 + 24 * k + 18) cb =
      (if MA ≤ cv tr t (f + 5 + 24 * k + 18) apR + cv tr t f fair then 1 else 0))
    (hb : cv tr t (f + 5 + 24 * k + 18) apR + cv tr t f fair < 2013265921) :
    cv tr t (f + 5 + 24 * k + 23) a1 =
        (if cv tr t (f + 5 + 24 * k + 18) bigR = 1 then MA
          else min (cv tr t (f + 5 + 24 * k + 18) apR + cv tr t f fair) MA) ∧
      cv tr t (f + 5 + 24 * k + 23) al ≤ 1 ∧
      cv tr t (f + 5 + 24 * k + 23) g2 = cv tr t (f + 5 + 24 * k + 23) al * cv tr t f base ∧
      (cv tr t (f + 5 + 24 * k + 23) a2 + cv tr t (f + 5 + 24 * k + 23) al * cv tr t f base) %
        2013265921 = cv tr t (f + 5 + 24 * k + 23) a1 ∧
      (cv tr t (f + 5 + 24 * k + 23) al * cv tr t f base ≤ cv tr t (f + 5 + 24 * k + 23) a1 →
        cv tr t (f + 5 + 24 * k + 23) a2 =
          cv tr t (f + 5 + 24 * k + 23) a1 - cv tr t (f + 5 + 24 * k + 23) al * cv tr t f base) := by
  obtain ⟨-, -, -, -, hapR, hbigR, hcb'⟩ := alw_walk hL hR
  have F := rrow_flags hL (hR 23 (by omega)) (by omega)
  have hrd : cv tr t (f + 5 + 24 * k + 23) rend = 1 := by rw [F.2.2.2.2.1]; rfl
  have hic := (hR 23 (by omega)).2.2.2.2.2.2
  have hfair : cv tr t (f + 5 + 24 * k + 23) fair = cv tr t f fair := hic fair (by simp [instCols])
  have hbase : cv tr t (f + 5 + 24 * k + 23) base = cv tr t f base := hic base (by simp [instCols])
  obtain ⟨-, -, -, ba, bc, bg, A1, A2, A3, L0, L1, -⟩ := rend_row hL (hR 23 (by omega)).1 hrd
  rw [hbigR] at A1 A2 A3 bg
  rw [hcb'] at A2 A3 bc
  have hfair' : cv tr t (f + 5 + 24 * k + 23) fair = cv tr t f fair := hfair
  rw [hapR, hfair'] at A3
  rw [hbase] at L1
  have hbase' := lt (tr := tr) (t := t) f base
  have ha1 := lt (tr := tr) (t := t) (f + 5 + 24 * k + 23) a1
  have ha2 := lt (tr := tr) (t := t) (f + 5 + 24 * k + 23) a2
  have hg2 := lt (tr := tr) (t := t) (f + 5 + 24 * k + 23) g2
  refine ⟨?_, ba, ?_, ?_, ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bg with h | h
    · rw [if_neg (by omega)]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bc with h' | h'
      · rw [A3 h h', Nat.mod_eq_of_lt hb]
        rw [hcb] at h'
        split at h'
        · omega
        · exact (Nat.min_eq_left (by omega)).symm
      · rw [A2 h h']
        rw [hcb] at h'
        split at h'
        · next hle => exact (Nat.min_eq_right hle).symm
        · omega
    · rw [if_pos h, A1 h]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ba with h | h
    · rw [h, (L0 h).2]; simp
    · rw [h, (L1 h).2]; simp
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ba with h | h
    · rw [h, (L0 h).1]; simp; exact ha1
    · rw [h, Nat.one_mul]; exact (L1 h).1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ba with h | h
    · rw [h, (L0 h).1]; simp
    · intro hle
      have := (L1 h).1
      rw [h, Nat.one_mul] at hle ⊢
      omega

/-! ## The messages of a record -/

/-- **Record messages.** -/
theorem codec_rec_msgs (hL : CLocal tr t pub) {f k : Nat} (hR : ∀ o, o < 24 → RRow tr t f k o)
    (hrs : cv tr t (f + 5 + 24 * k) rs = 1) :
    -- SDG at the record start
    (interactions[12]!).multNat tr t (f + 5 + 24 * k) pub = 1 ∧
    (interactions[12]!).msgVal tr t (f + 5 + 24 * k) pub =
      [cv tr t f tau, k, cv tr t (f + 5 + 24 * k + 23) al, cv tr t (f + 5 + 24 * k + 23) gb,
        cv tr t (f + 5 + 24 * k + 23) srcC, cv tr t (f + 5 + 24 * k + 23) hasC,
        cv tr t (f + 5 + 24 * k + 23) useC].map Fp.ofNat ∧
    -- A0 receive and the comparator at byte 2
    cv tr t (f + 5 + 24 * k + 23) hasC ≤ 1 ∧
    (interactions[14]!).multNat tr t (f + 5 + 24 * k + 18) pub = cv tr t (f + 5 + 24 * k + 23) hasC ∧
    (interactions[14]!).msgVal tr t (f + 5 + 24 * k + 18) pub =
      [cv tr t f tau, cv tr t (f + 5 + 24 * k + 23) srcC, cv tr t (f + 5 + 24 * k + 18) apR,
        cv tr t (f + 5 + 24 * k + 18) bigR].map Fp.ofNat ∧
    (cv tr t (f + 5 + 24 * k + 23) hasC = 0 →
      cv tr t (f + 5 + 24 * k + 18) apR = 0 ∧ cv tr t (f + 5 + 24 * k + 18) bigR = 0) ∧
    (interactions[15]!).multNat tr t (f + 5 + 24 * k + 18) pub = 1 ∧
    (interactions[15]!).msgVal tr t (f + 5 + 24 * k + 18) pub =
      [(cv tr t (f + 5 + 24 * k + 18) apR + cv tr t f fair) % 2013265921, MA,
        cv tr t (f + 5 + 24 * k + 18) cb].map Fp.ofNat ∧
    -- INIT, FIN, A0 send at the record end
    (interactions[10]!).multNat tr t (f + 5 + 24 * k + 23) pub = 1 ∧
    (interactions[10]!).msgVal tr t (f + 5 + 24 * k + 23) pub =
      [16384 * cv tr t f tau + k, 0, OP_INIT, cv tr t (f + 5 + 24 * k + 23) al,
        cv tr t (f + 5 + 24 * k + 23) a2, cv tr t (f + 5 + 24 * k + 23) g2, 0, 1].map Fp.ofNat ∧
    (interactions[11]!).multNat tr t (f + 5 + 24 * k + 23) pub = 1 ∧
    (interactions[11]!).msgVal tr t (f + 5 + 24 * k + 23) pub =
      [16384 * cv tr t f tau + k, cv tr t (f + 5 + 24 * k + 23) afin,
        cv tr t (f + 5 + 24 * k + 23) gfin].map Fp.ofNat ∧
    (interactions[13]!).multNat tr t (f + 5 + 24 * k + 23) pub =
      (if cv tr t (f + 5 + 24 * k + 23) useC = 1 then 1 else 0) ∧
    (interactions[13]!).msgVal tr t (f + 5 + 24 * k + 23) pub =
      [cv tr t f tau, k,
        cv tr t (f + 5 + 24 * k + 16) bpre + 256 * cv tr t (f + 5 + 24 * k + 17) bpre +
          65536 * cv tr t (f + 5 + 24 * k + 18) bpre,
        (if cv tr t (f + 5 + 24 * k + 19) bpre = 0 ∧ cv tr t (f + 5 + 24 * k + 20) bpre = 0 ∧
            cv tr t (f + 5 + 24 * k + 21) bpre = 0 ∧ cv tr t (f + 5 + 24 * k + 22) bpre = 0 ∧
            cv tr t (f + 5 + 24 * k + 23) bpre = 0 then 0 else 1)].map Fp.ofNat ∧
    -- forwarding (instance 0 only)
    (cv tr t f tau = 0 →
      (interactions[15]!).multNat tr t (f + 5 + 24 * k + 23) pub = 1 ∧
      (interactions[15]!).msgVal tr t (f + 5 + 24 * k + 23) pub =
        [(cv tr t (f + 5 + 24 * k + 23) gfin + cv tr t (f + 5 + 24 * k + 23) gb) % 2013265921,
          (cv tr t (f + 5 + 24 * k + 23) (fb 0) + 256 * cv tr t (f + 5 + 24 * k + 23) (fb 1) +
            65536 * cv tr t (f + 5 + 24 * k + 23) (fb 2)) % 2013265921, 1].map Fp.ofNat ∧
      (interactions[9]!).multNat tr t (f + 5 + 24 * k + 23) pub = 1 ∧
      (interactions[9]!).msgVal tr t (f + 5 + 24 * k + 23) pub =
        [0, 4, cv tr t (f + 5 + 24 * k + 23) klo, cv tr t (f + 5 + 24 * k + 23) khi,
          cv tr t (f + 5 + 24 * k + 23) (fb 0), cv tr t (f + 5 + 24 * k + 23) (fb 1),
          cv tr t (f + 5 + 24 * k + 23) (fb 2)].map Fp.ofNat) ∧
    (cv tr t f tau ≠ 0 →
      (interactions[15]!).multNat tr t (f + 5 + 24 * k + 23) pub = 0 ∧
      (interactions[9]!).multNat tr t (f + 5 + 24 * k + 23) pub = 0) := by
  obtain ⟨hap, hbF, -, -, -, -, -⟩ := alw_walk hL hR
  have D := fun x hx o ho => rec_data hL hR (x := x) hx o ho
  have R0 := hR 0 (by omega); have R18 := hR 18 (by omega); have R23 := hR 23 (by omega)
  have F18 := rrow_flags hL R18 (by omega)
  have F23 := rrow_flags hL R23 (by omega)
  have hA18 : cv tr t (f + 5 + 24 * k + 18) fA = 1 := by rw [F18.2.2.1]; rfl
  have he18 : cv tr t (f + 5 + 24 * k + 18) e2 = 1 := by rw [F18.2.2.2.2.2]; rfl
  have hrd : cv tr t (f + 5 + 24 * k + 23) rend = 1 := by rw [F23.2.2.2.2.1]; rfl
  obtain ⟨-, -, -, -, hz, ha0, bh, hcx, hcy, hcbit, hcg, -⟩ := b2_row hL R18.1 hA18 he18
  obtain ⟨hA23, -, -, -, -, -, -, -, -, -, -, -, hu0, hfw, hcg23, hfwd⟩ := rend_row hL R23.1 hrd
  have hτ := fun o (ho : o < 24) => (hR o ho).2.2.2.2.2.2 tau (by simp [instCols])
  have hki := fun o (ho : o < 24) => (hR o ho).2.2.2.2.1
  have hfair := (hR 18 (by omega)).2.2.2.2.2.2 fair (by simp [instCols])
  have hk23 : cv tr t (f + 5 + 24 * k + 23) kA = 0 := by
    have := kinds hL R23.1; have := R23.2.1; omega
  have hz23 : cv tr t (f + 5 + 24 * k + 23) zt = 1 ↔ cv tr t f tau = 0 := by
    rw [← hτ 23 (by omega)]; exact zt_iff hL R23.1 (by have := kinds hL R23.1; have := R23.2.1; omega)
  have bz := bool_of hL R23.1 (x := zt) (by simp [boolCols])
  -- record data at the start / byte 2 equal its value at the end
  have d0 : ∀ x ∈ [al, gb, srcC, hasC, useC], cv tr t (f + 5 + 24 * k) x = cv tr t (f + 5 + 24 * k + 23) x :=
    fun x hx => (D x hx 23 (by omega)).symm
  have d18 : ∀ x ∈ [al, gb, srcC, hasC, useC],
      cv tr t (f + 5 + 24 * k + 18) x = cv tr t (f + 5 + 24 * k + 23) x :=
    fun x hx => (D x hx 18 (by omega)).trans (D x hx 23 (by omega)).symm
  have hτ0 : cv tr t (f + 5 + 24 * k) tau = cv tr t f tau := by
    have := hτ 0 (by omega); simpa using this
  have hk0 : cv tr t (f + 5 + 24 * k) kidx = k := by have := hki 0 (by omega); simpa using this
  have aL23 : aLE.eval tr t (f + 5 + 24 * k + 23) pub = Fp.ofNat (16384 * cv tr t f tau + k) :=
    ev_of (by simp only [aLE, zev_add, zev_smul, zev_c, cur_cv]; rw [hτ 23 (by omega), hki 23 (by omega)]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mult_of (i := interactions[12]!) rfl (by simp only [zev_c, cur_cv]; rw [hrs]; rfl)
  · rw [i12_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
    rw [hτ0, hk0, d0 al (by simp), d0 gb (by simp), d0 srcC (by simp), d0 hasC (by simp),
      d0 useC (by simp)]
  · rw [← d18 hasC (by simp)]; exact bh
  · rw [← d18 hasC (by simp)]
    exact mult_bit (i := interactions[14]!) rfl (by simp only [zev_c, cur_cv]; rw [ha0]) bh
  · rw [i14_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
    rw [hτ 18 (by omega), d18 srcC (by simp)]
  · intro h; rw [← d18 hasC (by simp)] at h; exact hz h
  · exact mult_of (i := interactions[15]!) rfl (by simp only [zev_c, cur_cv]; rw [hcg]; rfl)
  · rw [i15_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
    rw [hcx, hcy, hcbit, hfair]
  · exact mult_of (i := interactions[10]!) rfl (by simp only [zev_c, cur_cv]; rw [hrd]; rfl)
  · rw [i10_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, aL23]
  · exact mult_of (i := interactions[11]!) rfl (by simp only [zev_c, cur_cv]; rw [hrd]; rfl)
  · rw [i11_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, aL23]
  · have hu := lt (tr := tr) (t := t) (f + 5 + 24 * k + 23) useC
    split
    · next h => exact mult_of (i := interactions[13]!) rfl (by simp only [zev_c, cur_cv]; rw [hu0, h]; rfl)
    · next h =>
      unfold Interaction.multNat
      simp only [i13_def, Interaction.multNat.go, ev_c]
      rw [hu0, if_neg]
      intro he
      apply h
      have := congrArg Fp.toNat he
      rw [Fp.toNat_ofNat] at this
      have h1 : (1 : Fp).toNat = 1 := rfl
      have hu' : cv tr t (f + 5 + 24 * k + 23) useC < P := Fp.toNat_lt _
      rw [h1, Nat.mod_eq_of_lt hu'] at this
      exact this
  · rw [i13_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
    rw [hτ 23 (by omega), hki 23 (by omega), hap, hbF]
  · intro h0
    have hzt : cv tr t (f + 5 + 24 * k + 23) zt = 1 := hz23.2 h0
    obtain ⟨hcx', hcy', hcbit', hpm0, hpm1⟩ := hfwd hzt
    refine ⟨mult_of (i := interactions[15]!) rfl (by simp only [zev_c, cur_cv]; rw [hcg23, hzt]; rfl),
      ?_, mult_of (i := interactions[9]!) rfl
        (by simp only [zev_add, zev_c, cur_cv]; rw [hk23, hfw, hzt]; rfl), ?_⟩
    · rw [i15_def]
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c]
      rw [hcx', hcy', hcbit']
    · rw [i9_def]
      have e2 : (Expr.add (smul 2 (c kA)) (smul 4 (c fwg))).eval tr t (f + 5 + 24 * k + 23) pub =
          Fp.ofNat 4 :=
        ev_of (by simp only [zev_add, zev_smul, zev_c, cur_cv]; rw [hk23, hfw, hzt]; rfl)
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, e2]
      rw [hτ 23 (by omega), h0, hpm0, hpm1]
  · intro h0
    have hzt : cv tr t (f + 5 + 24 * k + 23) zt = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bz with h | h
      · exact h
      · exact absurd (hz23.1 h) h0
    exact ⟨mult_zero (i := interactions[15]!) rfl (by simp only [zev_c, cur_cv]; rw [hcg23, hzt]; rfl),
      mult_zero (i := interactions[9]!) rfl (by simp only [zev_add, zev_c, cur_cv]; rw [hk23, hfw, hzt]; rfl)⟩

end

end ZkFormal.NearV3.Sched.Codec
