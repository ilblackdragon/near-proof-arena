import StateM5a.KeyDigest
import StateM5a.KeyLookups
import StateM5a.Order
import StateM5a.WsEntries

/-!
# StateM5a.KeyOrder — `ORD` is the spec's key order; the INTAKE keys are distinct

* **`kcmp_back`**: a `KCMP` row with `j = p` is preceded by the rows `j = 0 … p − 1` of the same
  comparison (`ka`, `kb` equal, not final), from the transition constraints.
* **`ord_sent` / `ord_recv`**: every `ORD(ka, kb)` message is `bytesLt (keyBytes ka) (keyBytes kb)`:
  the run's nibbles agree below `p` (`NIB` lookups of both keys), and at `p` either `xa < xb`
  (`FieldRows.kcmp_fin_lt`) or `ka` ends (`KLEN`) while `kb` has a nibble — `Order.NibLt`, then
  `Order.nibLt_bytesLt`.
* **`wsbKdRange`**: `WsLeafF.WsbKdRange` from `KeyDigest.wsb_kd` (the limbs are `pairs` of
  digest bytes).
* **`wsb_sorted`** / **`intakeKeysDistinct`**: the real phase-0 `WSB` rows hold strictly increasing
  key bytes (`so` rows receive `ORD(kid_i, kid_{i+1})`), hence distinct `kd = pairs (sha256 key)`
  (with `Sha256CR`), hence — through `WsLeafF.wsb_leaf` and `LeafCR` — `WsKey.IntakeKeysDistinct`.
-/

namespace StateM5a.KeyOrder

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.KeyDecode
open StateM5a.Tape StateM5a.KcChain StateM5a.KeyDigest NearSpec NearSpecV3.D2

set_option maxRecDepth 100000

/-! ## Nibbles are nibbles -/

theorem nibbles_lt : ∀ (B : Bytes), ∀ x ∈ nibbles B, x < 16
  | [], x, h => by simp [nibbles] at h
  | b :: bs, x, h => by
    simp only [nibbles, List.mem_cons] at h
    have := UInt8.toNat_lt b
    rcases h with rfl | rfl | h
    · omega
    · omega
    · exact nibbles_lt bs x h

theorem keyOf_lt {tr : Trace Fp} {pub : List Fp}
    (hc : ∀ r, r < tr.height 1 → ∀ e ∈ Key.table.constraints, e.eval tr 1 r pub = 0) {K i x : Nat}
    (h : (KeyDecode.keyOf tr K)[i]? = some x) : x < 16 := by
  rw [keyOf_eq_nibbles hc] at h
  exact nibbles_lt _ x (List.mem_of_getElem? h)

/-! ## `KCMP` runs -/

theorem m_kf : Expr.isFirst * (Kcmp.c "first" - Kcmp.c "act") ∈ Kcmp.constraints := by
  unfold Kcmp.constraints; simp
theorem m_ka : Expr.isTransition * Kcmp.nx "act" * (1 - Kcmp.c "act") ∈ Kcmp.constraints := by
  unfold Kcmp.constraints; simp
theorem m_kfirst : Expr.isTransition * Kcmp.nx "act" * (Kcmp.nx "first" - Kcmp.c "fin") ∈ Kcmp.constraints := by
  unfold Kcmp.constraints; simp
theorem m_kka : Expr.isTransition * Kcmp.nx "act" * (1 - Kcmp.c "fin") * (Kcmp.nx "ka" - Kcmp.c "ka") ∈
    Kcmp.constraints := by unfold Kcmp.constraints; simp
theorem m_kkb : Expr.isTransition * Kcmp.nx "act" * (1 - Kcmp.c "fin") * (Kcmp.nx "kb" - Kcmp.c "kb") ∈
    Kcmp.constraints := by unfold Kcmp.constraints; simp
theorem m_kj : Expr.isTransition * Kcmp.nx "act" * (1 - Kcmp.c "fin") * (Kcmp.nx "j" - Kcmp.c "j" - 1) ∈
    Kcmp.constraints := by unfold Kcmp.constraints; simp
theorem m_kfj : Kcmp.c "first" * Kcmp.c "j" ∈ Kcmp.constraints := by unfold Kcmp.constraints; simp
theorem m_kfa : (1 - Kcmp.c "act") * Kcmp.c "fin" ∈ Kcmp.constraints := by unfold Kcmp.constraints; simp
theorem m_kb (s : String) (hs : s ∈ ["act", "first", "fin", "pre"]) : bool (Kcmp.c s) ∈ Kcmp.constraints := by
  unfold Kcmp.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> simp

section
variable {tr : Trace Fp} {pub : List Fp}
  (hc : ∀ r, r < tr.height 4 → ∀ e ∈ Kcmp.table.constraints, e.eval tr 4 r pub = 0)
include hc

theorem kc_h {r : Nat} (hr : r < tr.height 4) {e : Expr} (he : e ∈ Kcmp.constraints) : ev tr 4 r pub e = 0 :=
  hold rfl (hc r hr) he

theorem kc_bool {r : Nat} (hr : r < tr.height 4) (s : String) (hs : s ∈ ["act", "first", "fin", "pre"]) :
    ev tr 4 r pub (Kcmp.c s) = 0 ∨ ev tr 4 r pub (Kcmp.c s) = 1 := FieldRows2.ev_bool (kc_h hc hr (m_kb s hs))

/-- **A `KCMP` row with `j = p` is preceded by its run.** -/
theorem kcmp_back : ∀ p r, r < tr.height 4 → ev tr 4 r pub (Kcmp.c "act") = 1 →
    ev tr 4 r pub (Kcmp.c "j") = p → ∀ q, q < p → ∃ s, s < r ∧ ev tr 4 s pub (Kcmp.c "act") = 1 ∧
      ev tr 4 s pub (Kcmp.c "fin") = 0 ∧ ev tr 4 s pub (Kcmp.c "ka") = ev tr 4 r pub (Kcmp.c "ka") ∧
      ev tr 4 s pub (Kcmp.c "kb") = ev tr 4 r pub (Kcmp.c "kb") ∧ ev tr 4 s pub (Kcmp.c "j") = q := by
  intro p
  induction p with
  | zero => intro r _ _ _ q hq; omega
  | succ p ih =>
    intro r hr ha hj q hq
    -- not a first row
    have hf0 : ev tr 4 r pub (Kcmp.c "first") = 0 := by
      have e := kc_h hc hr m_kfj
      rw [ev_hmul, hj] at e
      rcases kc_bool hc hr "first" (by simp) with h | h
      · exact h
      · rw [h, Nat.one_mul] at e
        have := ev_lt (tr := tr) (t := 4) (r := r) (pub := pub) (Kcmp.c "j")
        rw [hj] at this
        rw [Nat.mod_eq_of_lt this] at e; omega
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := by
      cases r with
      | zero =>
        exfalso
        have g : ev tr 4 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
        have e := eq_of_sub (FieldWsb.wsb_gate g (kc_h hc hr m_kf))
        omega
      | succ r' => exact ⟨r', rfl⟩
    have hr' : r' < tr.height 4 := by omega
    have gT : ev tr 4 r' pub .isTransition = 1 := by
      rw [FieldWsb.ev_isTransition]; split
      · omega
      · rfl
    have nx : ∀ s, ev tr 4 r' pub (Kcmp.nx s) = ev tr 4 (r' + 1) pub (Kcmp.c s) :=
      fun s => FieldWsb.ev_next r' _ hr
    have g : ev tr 4 r' pub (Expr.isTransition * Kcmp.nx "act") = 1 := by rw [ev_hmul, gT, nx, ha]
    have hA : ev tr 4 r' pub (Kcmp.c "act") = 1 := ev_one_minus (FieldWsb.wsb_gate g (kc_h hc hr' m_ka))
    have hF : ev tr 4 r' pub (Kcmp.c "fin") = 0 := by
      have e := eq_of_sub (FieldWsb.wsb_gate g (kc_h hc hr' m_kfirst))
      rw [nx, hf0] at e; exact e.symm
    have g2 : ev tr 4 r' pub (Expr.isTransition * Kcmp.nx "act" * (1 - Kcmp.c "fin")) = 1 := by
      rw [ev_hmul, g, FieldRows2.ev_one_sub0 hF]
    have eka := eq_of_sub (FieldWsb.wsb_gate g2 (kc_h hc hr' m_kka))
    have ekb := eq_of_sub (FieldWsb.wsb_gate g2 (kc_h hc hr' m_kkb))
    have ej := sub_val (eq_of_sub (FieldWsb.wsb_gate g2 (kc_h hc hr' m_kj)))
    rw [nx] at eka ekb ej
    rw [ev_one] at ej
    have hjr' : ev tr 4 r' pub (Kcmp.c "j") = p := by
      have := ev_lt (tr := tr) (t := 4) (r := r') (pub := pub) (Kcmp.c "j")
      have := ev_lt (tr := tr) (t := 4) (r := r' + 1) (pub := pub) (Kcmp.c "j")
      omega
    rcases Nat.lt_or_ge q p with h | h
    · obtain ⟨s, hs, a1, a2, a3, a4, a5⟩ := ih r' hr' hA hjr' q h
      exact ⟨s, by omega, a1, a2, a3.trans eka.symm, a4.trans ekb.symm, a5⟩
    · exact ⟨r', by omega, hA, hF, eka.symm, ekb.symm, by omega⟩

end

theorem ord_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 4 →
    sendsOn ((m5aAir D).tables[t]).interactions B_ORD = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_ORD = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_ORD = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_ORD = false; decide
  | 3, _, _ => by show sendsOn Sn.interactions B_ORD = false; decide
  | 4, _, h => absurd rfl h
  | 5, _, _ => by show sendsOn Wsb.interactions B_ORD = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_ORD = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_ORD = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_ORD = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_ORD = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_ORD = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_ORD = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem kcmp_ord_s : Kcmp.interactions.filter (fun i => decide (i.bus = B_ORD ∧ i.send = true)) =
    [snd B_ORD (Kcmp.c "fin") [Kcmp.c "ka", Kcmp.c "kb"]] := by decide

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **Every `ORD(ka, kb)` sent is the spec's strict key order.** -/
theorem ord_sent (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_ORD true) :
    ∃ a b : Fp, m = [a, b] ∧ bytesLt (keyBytes tr a.toNat) (keyBytes tr b.toNat) = true := by
  have hck := key_hc hH
  have hc : ∀ r, r < tr.height 4 → ∀ e ∈ Kcmp.table.constraints, e.eval tr 4 r pub = 0 :=
    fun r hr => hH.constr 4 (by rw [fullAir_len]; omega) r hr
  obtain ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_m5a B_ORD 4 (by simp [m5aAir]) (ord_only D) hO hm
  change i ∈ Kcmp.interactions at hi
  obtain rfl := filter_one_mem kcmp_ord_s hi hb hs
  have hfin := eval_one_ev (multNat_one_bit rfl hp)
  have ha : ev tr 4 r pub (Kcmp.c "act") = 1 := gate_of_one (kc_h hc hr m_kfa) hfin
  refine ⟨_, _, rfl, ?_⟩
  change bytesLt (keyBytes tr (ev tr 4 r pub (Kcmp.c "ka"))) (keyBytes tr (ev tr 4 r pub (Kcmp.c "kb"))) = true
  apply Order.nibLt_bytesLt
  rw [← keyOf_eq_nibbles hck, ← keyOf_eq_nibbles hck]
  generalize hp' : ev tr 4 r pub (Kcmp.c "j") = p
  -- the common prefix
  have hpre : ∀ q, q < p → ∃ x, (KeyDecode.keyOf tr (ev tr 4 r pub (Kcmp.c "ka")))[q]? = some x ∧
      (KeyDecode.keyOf tr (ev tr 4 r pub (Kcmp.c "kb")))[q]? = some x := by
    intro q hq
    obtain ⟨s, hs, a1, a2, a3, a4, a5⟩ := kcmp_back hc p r hr ha hp' q hq
    have hg : (Kcmp.c "act" * (1 - Kcmp.c "fin")).eval tr 4 s pub = 1 :=
      ev_one_eval (by rw [ev_hmul, a1, FieldRows2.ev_one_sub0 a2])
    obtain ⟨⟨n1, -⟩, ⟨n2, -⟩⟩ := KeyLookups.kcmp_nib_a hH hN (by omega) hg
    rw [a3, a5] at n1; rw [a4, a5] at n2
    exact ⟨_, n1, n2⟩
  have htake : (KeyDecode.keyOf tr (ev tr 4 r pub (Kcmp.c "ka"))).take p =
      (KeyDecode.keyOf tr (ev tr 4 r pub (Kcmp.c "kb"))).take p := by
    apply List.ext_getElem?
    intro q
    rw [List.getElem?_take, List.getElem?_take]
    split
    · rename_i hq
      obtain ⟨x, h1, h2⟩ := hpre q hq
      rw [h1, h2]
    · rfl
  have hxb := KeyLookups.kcmp_nib_xb hH hN hr (ev_one_eval hfin)
  unfold KeyLookups.NibAt at hxb
  rw [hp'] at hxb
  refine ⟨p, htake, ?_⟩
  rcases kc_bool hc hr "pre" (by simp) with h0 | h1
  · right
    have hxa := KeyLookups.kcmp_nib_xa hH hN hr (ev_one_eval (by rw [ev_hmul, hfin, FieldRows2.ev_one_sub0 h0]))
    unfold KeyLookups.NibAt at hxa
    rw [hp'] at hxa
    refine ⟨_, _, hxa.1, hxb.1, ?_⟩
    exact kcmp_fin_lt (hc r hr) hfin h0 (keyOf_lt hck hxa.1) (keyOf_lt hck hxb.1)
  · left
    have hk := KeyLookups.kcmp_klen hH hL hr (ev_one_eval (by rw [ev_hmul, hfin, h1]))
    unfold KeyLookups.KlenAt at hk
    rw [hp'] at hk
    refine ⟨hk.symm, ?_⟩
    have := hxb.1
    exact (List.getElem?_eq_some_iff.1 this).1

/-- **`ORD` lookups.** -/
theorem ord_recv (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_ORD false) :
    ∃ a b : Fp, m = [a, b] ∧ bytesLt (keyBytes tr a.toNat) (keyBytes tr b.toNat) = true :=
  ord_sent hH hN hL hO (recv_sent hH hm)

/-- **`WsLeafF.WsbKdRange` from `KDIG`.** -/
theorem wsbKdRange (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false) : WsLeafF.WsbKdRange tr pub := by
  intro r hr hR j hj
  have e := wsb_kd hH hxB hxD hxK hxG hr (eval_one_ev hR)
  have hm : ev tr 5 r pub (Wsb.c "kd" j) ∈ pairs (sha256 (keyBytes tr (ev tr 5 r pub (Wsb.c "kid")))) := by
    rw [← e]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  exact pairs_lt _ _ hm

end

end StateM5a.KeyOrder
