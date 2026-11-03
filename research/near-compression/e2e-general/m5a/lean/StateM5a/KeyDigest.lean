import StateM5a.KcChain
import ZkFormal.Sha.Sound
import ZkFormal.Sha.Compose

/-!
# StateM5a.KeyDigest — `KDIG` is the SHA-256 of the key bytes

A `KEY` row closing key `kid` (`last = 1`) receives `SHA_DIGEST(ID_KEY + kid, j + 1, dg)` and
provides `KDIG(kid, pack2 dg)`.  The digest's sender is the SHA-256 table (`ZkFormal.Sha`), whose
contract (`sha_digest_contract_closed`) says `dg = sha256 m` for a message `m` every byte of which
the table *received* on `SHA_BYTES` as `(id, i, m[i])`.  Those byte messages were *sent* by
`KEY`, `BR`, `SN` or `SNC` rows (`sb_only`); only a `KEY` row of key `kid` uses the id
`ID_KEY + kid`:

* `BR` / `SN` rows hash under `ID_BR + 2·rid (+1)` / `ID_SN + 2·rid (+1)` with `rid` the row index
  (`rid_row`);
* an `SNC` row hashes under `ID_SN + 2·rid (+1)` with `rid` some `SN` row's index — the `KC` chain
  (`snc_rid`: the chunk-1 row got its `KC` from an `SN` row, chunk `c + 1` from chunk `c`, with
  `KcChain.snc_c_range`);

so `m = keyBytes tr kid` (`KeyDecode.keyRows_get` / `keyRows_length`).  **`kdig_recv`**: every
`KDIG` message received is `(x, limbs)` with `limbs = pairs (sha256 (keyBytes tr x))` (16-bit
big-endian limbs).  No cryptographic assumption.
-/

namespace StateM5a.KeyDigest

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.DepthBound StateM5a.Tape StateM5a.KcChain NearSpec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Senders -/

theorem sb_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ∉ [1, 2, 3, 8] →
    sendsOn ((m5aAir D).tables[t]).interactions B_SHA_BYTES = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_SHA_BYTES = false; decide
  | 1, _, h => absurd (by simp) h
  | 2, _, h => absurd (by simp) h
  | 3, _, h => absurd (by simp) h
  | 4, _, _ => by show sendsOn Kcmp.interactions B_SHA_BYTES = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_SHA_BYTES = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_SHA_BYTES = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_SHA_BYTES = false; decide
  | 8, _, h => absurd (by simp) h
  | 9, _, _ => by show sendsOn Rng.interactions B_SHA_BYTES = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_SHA_BYTES = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_SHA_BYTES = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem sd_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 0 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SHA_DIGEST = false
  | 0, _, h => absurd rfl h
  | 1, _, _ => by show sendsOn Key.interactions B_SHA_DIGEST = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_SHA_DIGEST = false; decide
  | 3, _, _ => by show sendsOn Sn.interactions B_SHA_DIGEST = false; decide
  | 4, _, _ => by show sendsOn Kcmp.interactions B_SHA_DIGEST = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_SHA_DIGEST = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_SHA_DIGEST = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_SHA_DIGEST = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_SHA_DIGEST = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_SHA_DIGEST = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_SHA_DIGEST = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_SHA_DIGEST = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

/-- The `SHA_BYTES` sends of `BR` / `SN` use the row's two message ids. -/
theorem br_sb_ids : Br.interactions.all (fun i => !(decide (i.bus = B_SHA_BYTES) && i.send) ||
    decide (i.msg.head? = some Br.idO) || decide (i.msg.head? = some Br.idN)) = true := by decide
theorem sn_sb_ids : Sn.interactions.all (fun i => !(decide (i.bus = B_SHA_BYTES) && i.send) ||
    decide (i.msg.head? = some Sn.idO) || decide (i.msg.head? = some Sn.idN)) = true := by decide

def sncIdO : Expr := K ID_SN + sm 2 (Snc.c "rid")
def sncIdN : Expr := K ID_SN + sm 2 (Snc.c "rid") + 1

theorem snc_sb_ids : Snc.interactions.all (fun i => !(decide (i.bus = B_SHA_BYTES) && i.send) ||
    (List.range 32).any (fun m =>
      (decide (i.mult = [Snc.c "gO" * Snc.c "ha" m]) && decide (i.msg.head? = some sncIdO)) ||
      (decide (i.mult = [Snc.c "gN" * Snc.c "ha" m]) && decide (i.msg.head? = some sncIdN)))) = true := by
  decide

theorem key_sb_s : Key.interactions.filter (fun i => decide (i.bus = B_SHA_BYTES ∧ i.send = true)) =
    [snd B_SHA_BYTES (Key.c "act") [K ID_KEY + Key.c "kid", Key.c "j", sm 16 (Key.c "hi") + Key.c "lo"]] := by
  decide

theorem key_sd_r_mem : rcv B_SHA_DIGEST (Key.c "last") ([K ID_KEY + Key.c "kid", Key.c "j" + 1] ++
    (List.range 32).map fun b => Key.c "dg" b) ∈ Key.interactions := memD_mem (by decide)

theorem key_kdig_s : Key.interactions.filter (fun i => decide (i.bus = B_KDIG ∧ i.send = true)) =
    [sndBits B_KDIG (Key.bits "mdig") (Key.c "kid" :: pack2 fun b => Key.c "dg" b)] := by decide

theorem sha_sd_s : shaTable.interactions.filter (fun i => decide (i.bus = B_SHA_DIGEST ∧ i.send = true)) =
    [(ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[16]!] := by decide

theorem sha_rcv (q : Nat) (hq : q < 16) :
    (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! ∈ shaTable.interactions ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).bus = B_SHA_BYTES ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).send = false ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).mult =
      [Expr.col (ZkFormal.Sha.Layout.colF q) false] := by
  have hl : q < (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST).length := by
    simp [ZkFormal.Sha.Table.interactions]; omega
  have he : (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! =
      (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q] := by
    simp [getElem!_def, List.getElem?_eq_getElem hl]
  rw [he]
  refine ⟨List.getElem_mem hl, ?_⟩
  simp [ZkFormal.Sha.Table.interactions, List.getElem_append, hq, ZkFormal.Sha.Table.E.c]

/-! ## Generic -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- Senders among a set of tables. -/
theorem sender_set (b : Nat) (ts : List Nat)
    (hS : ∀ t (ht : t < (m5aAir D).tables.length), t ∉ ts →
      sendsOn ((m5aAir D).tables[t]).interactions b = false)
    (hx : ∀ T ∈ extra, sendsOn T.interactions b = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub b true) :
    ∃ t ∈ ts, ∃ ht : t < (m5aAir D).tables.length, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((m5aAir D).tables[t]).interactions, i.bus = b ∧ i.send = true ∧
        0 < i.multNat tr t r pub ∧ m = i.msgVal tr t r pub := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    by_cases e : t ∈ ts
    · exact ⟨t, e, hlt, r, hr, i, hi, hb, hs, hp, rfl⟩
    · exact (not_sends (hS t hlt e) hi hb hs).elim
  · have hmem : (fullAir D extra nb np).tables[t] ∈ extra := by
      simp only [fullAir]
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem ..
    exact (not_sends (hx _ hmem) hi hb hs).elim

theorem head_eval {i : Interaction} {e : Expr} (h : i.msg.head? = some e) {t r : Nat} :
    (i.msgVal tr t r pub).head? = some (e.eval tr t r pub) := by
  simp only [Interaction.msgVal, List.head?_map, h, Option.map_some]

/-- A `rid` column that counts rows (`isFirst·rid = 0`, `rid' = rid + 1`). -/
theorem rid_row {t c : Nat} (hlog : tr.log t ≤ 20)
    (h0 : ev tr t 0 pub (.isFirst * Expr.col c false) = 0)
    (h1 : ∀ r, r + 1 < tr.height t →
      ev tr t r pub (.isTransition * (Expr.col c true - Expr.col c false - 1)) = 0) :
    ∀ r, r < tr.height t → ev tr t r pub (Expr.col c false) = r := by
  have hH : tr.height t ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  intro r
  induction r with
  | zero =>
    intro _
    have g : ev tr t 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
    exact FieldWsb.wsb_gate g h0
  | succ r ih =>
    intro hr
    have g : ev tr t r pub .isTransition = 1 := by
      rw [FieldWsb.ev_isTransition]; split
      · omega
      · rfl
    have e := sub_val (eq_of_sub (FieldWsb.wsb_gate g (h1 r hr)))
    rw [FieldWsb.ev_next r c hr, ih (by omega), ev_one] at e
    rw [e, Nat.mod_eq_of_lt (by omega)]

theorem m_br_rid0 : Expr.isFirst * Br.c "rid" ∈ Br.constraints := by unfold Br.constraints; simp
theorem m_br_rid1 : Expr.isTransition * (Br.nx "rid" - Br.c "rid" - 1) ∈ Br.constraints := by
  unfold Br.constraints; simp
theorem m_sn_rid0 : Expr.isFirst * Sn.c "rid" ∈ Sn.constraints := by unfold Sn.constraints; simp
theorem m_sn_rid1 : Expr.isTransition * (Sn.nx "rid" - Sn.c "rid" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

theorem br_rid (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "rid") = r := by
  have hc := fun r hr => tbl_br D extra nb np hH r (List.mem_range.2 hr)
  exact rid_row (hH.logBound 2 (by rw [fullAir_len]; omega)).2
    (hold rfl (hc 0 (Nat.two_pow_pos _)) m_br_rid0)
    (fun r hr => hold rfl (hc r (by omega)) m_br_rid1)

theorem sn_rid (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "rid") = r := by
  have hc := fun r hr => tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  exact rid_row (hH.logBound 3 (by rw [fullAir_len]; omega)).2
    (hold rfl (hc 0 (Nat.two_pow_pos _)) m_sn_rid0)
    (fun r hr => hold rfl (hc r (by omega)) m_sn_rid1)

/-! ## The `SNC` row ids come from `SN` rows -/

theorem snc_rid (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) :
    ∀ v r, r < tr.height 8 → ev tr 8 r pub (Snc.c "act") = 1 → ev tr 8 r pub (Snc.c "c") = v →
      ev tr 8 r pub (Snc.c "rid") < 2 ^ 20 := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  intro v
  induction v with
  | zero =>
    intro r hr ha hv
    have := (snc_c_range hH hxK hr ha).1; omega
  | succ v ih =>
    intro r hr ha hv
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 8) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact snc_kc_r_mem) hr rfl (ev_one_eval ha)
    rcases sender_m5a2 B_KC 3 8 (by simp [m5aAir]) (by simp [m5aAir]) (kc_only D) hxK
        (recv_sent hH hm) with ⟨t, ht, i, hi, hb, hs, hp, he⟩ | ⟨t, ht, i, hi, hb, hs, hp, he⟩
    · change i ∈ Sn.interactions at hi
      obtain rfl := filter_one_mem sn_kc_s hi hb hs
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e := toNat_eq he.1
      rw [e, sn_rid hH t ht]
      omega
    · change i ∈ Snc.interactions at hi
      obtain rfl := filter_one_mem snc_kc_s hi hb hs
      have hmo := multNat_one_bit rfl hp
      have hta := snc_more_act (snc_hc hH t ht) (eval_one_ev hmo)
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e0 := toNat_eq he.1
      have e1 := toNat_eq he.2.1
      obtain ⟨h1, h2⟩ := snc_c_range hH hxK ht hta
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)] at e1
      rw [e0]
      exact ih t ht hta (by omega)

/-- An `SNC` byte send fires only on an active row. -/
theorem snc_ha_act {r : Nat} (hc : ∀ e ∈ Snc.table.constraints, e.eval tr 8 r pub = 0) {g : Expr} (m : Nat)
    (hm : m < 32) (h : (g * Snc.c "ha" m).eval tr 8 r pub = 1) : ev tr 8 r pub (Snc.c "act") = 1 := by
  have hb : ev tr 8 r pub (Snc.c "ha" m) = ev tr 8 r pub (Snc.a (2 * m)) := eq_of_sub (snc_h hc (by
    unfold Snc.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search m hm))
  have ha := bool_le (snc_h hc (m_snc_abool (2 * m) (by omega)))
  have h1 := eval_one_ev h
  rw [ev_hmul] at h1
  have hne : ev tr 8 r pub (Snc.c "ha" m) ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
  have h2 : ev tr 8 r pub (Snc.a (2 * m)) = 1 := by omega
  rw [← eq_of_sub (snc_h hc m_snc_a0)]
  exact snc_a_down hc (2 * m) (by omega) h2

/-! ## The message a `KEY` digest row hashed -/

theorem ev_id {t r : Nat} (base : Nat) (x : Expr) (hx : ev tr t r pub x < 2 ^ 21) (hb : base < 2 ^ 26) :
    ev tr t r pub (K base + x) = base + ev tr t r pub x := by
  rw [ev_hadd, show K base = Expr.const base from rfl, ev_const, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem ev_id2 {t r : Nat} (base : Nat) (x : Expr) (hx : ev tr t r pub x < 2 ^ 20) (hb : base < 2 ^ 26) :
    ev tr t r pub (K base + sm 2 x) = base + 2 * ev tr t r pub x := by
  rw [ev_id base _ (by rw [ev_sm2 _ (by omega)]; omega) hb, ev_sm2 _ (by omega)]

theorem ev_id2' {t r : Nat} (base : Nat) (x : Expr) (hx : ev tr t r pub x < 2 ^ 20) (hb : base < 2 ^ 26) :
    ev tr t r pub (K base + sm 2 x + 1) = base + 2 * ev tr t r pub x + 1 := by
  rw [ev_hadd, ev_id2 base x hx hb, ev_one, Nat.mod_eq_of_lt (by omega)]

/-- **A byte hashed under `ID_KEY + kid`** (`kid < 2^20`) comes from the `KEY` row `i` of key
`kid`. -/
theorem key_byte (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {kid : Nat} (hkid : kid < 2 ^ 20) {id x y : Fp} (hid : id.toNat = ID_KEY + kid)
    (hm : [id, x, y] ∈ busList (fullAir D extra nb np) tr pub B_SHA_BYTES false) :
    x.toNat < 2 ^ 20 ∧ (keyBytes tr kid)[x.toNat]? = some (UInt8.ofNat y.toNat) ∧ y.toNat < 256 := by
  have hlog := key_log hH
  have hc := key_hc hH
  have hH1 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  obtain ⟨t, hts, ht, r, hr, i, hi, hb, hs, hp, he⟩ := sender_set B_SHA_BYTES [1, 2, 3, 8] (sb_only D) hxB
    (recv_sent hH hm)
  have hhead := congrArg List.head? he
  simp only [List.head?_cons] at hhead
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hts
  rcases hts with rfl | rfl | rfl | rfl
  · -- `KEY`
    change i ∈ Key.interactions at hi
    obtain rfl := filter_one_mem key_sb_s hi hb hs
    have ha := eval_one_ev (multNat_one_bit rfl hp)
    obtain ⟨hk, hj, -, -⟩ := key_inv hc hlog r hr ha
    simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e0 := congrArg Fp.toNat he.1
    have e1 := congrArg Fp.toNat he.2.1
    have e2 := congrArg Fp.toNat he.2.2.1
    change id.toNat = ev tr 1 r pub (K ID_KEY + Key.c "kid") at e0
    change x.toNat = ev tr 1 r pub (Key.c "j") at e1
    change y.toNat = ev tr 1 r pub (sm 16 (Key.c "hi") + Key.c "lo") at e2
    rw [ev_id _ _ (by rw [ev_kc]; omega) (by decide), hid, ev_kc] at e0
    have hkd : kid = kc tr r "kid" := by simp [ID_KEY] at e0; omega
    obtain ⟨hhi, hlo, h256, -⟩ := KeyField.key_row_nibbles (hc r hr)
    have h256' : 16 * kc tr r "hi" + kc tr r "lo" < 256 := h256
    have ey : y.toNat = 16 * kc tr r "hi" + kc tr r "lo" := by
      rw [e2, ev_hadd, ev_kc, show sm 16 (Key.c "hi") = Expr.mul (.const 16) (Key.c "hi") from rfl, ev_mul,
        ev_const, ev_kc]
      change (16 % P * kc tr r "hi" % P + kc tr r "lo") % P = _
      rw [show 16 % P = 16 from rfl, Nat.mod_eq_of_lt (show 16 * kc tr r "hi" < P by omega),
        Nat.mod_eq_of_lt (show 16 * kc tr r "hi" + kc tr r "lo" < P by omega)]
    rw [ev_kc] at e1
    refine ⟨by omega, ?_, by omega⟩
    have hg := keyRows_get hc hlog hr ha
    rw [e1, hkd]
    unfold keyBytes
    rw [List.getElem?_map, hg, ey]
    rfl
  · -- `BR`: ids `ID_BR + 2·rid (+1)`
    change i ∈ Br.interactions at hi
    have := List.all_eq_true.1 br_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have hrid := br_rid hH r hr
    rcases this with h | h
    · rw [head_eval h] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid")) at this
      rw [ev_id2 _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_KEY, ID_BR] at this; omega
    · rw [head_eval h] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_KEY, ID_BR] at this; omega
  · -- `SN`
    change i ∈ Sn.interactions at hi
    have := List.all_eq_true.1 sn_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have hrid := sn_rid hH r hr
    rcases this with h | h
    · rw [head_eval h] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid")) at this
      rw [ev_id2 _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_KEY, ID_SN] at this; omega
    · rw [head_eval h] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_KEY, ID_SN] at this; omega
  · -- `SNC`: an active row, whose `rid` is an `SN` row index
    change i ∈ Snc.interactions at hi
    have := List.all_eq_true.1 snc_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨mm, hmm, h | h⟩ := this
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      rw [head_eval h.2] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid")) at this
      rw [ev_id2 _ _ hrid (by decide), hid] at this
      simp [ID_KEY, ID_SN] at this; omega
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      rw [head_eval h.2] at hhead
      have := congrArg (fun o => o.map Fp.toNat) hhead
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid") + 1) at this
      rw [ev_id2' _ _ hrid (by decide), hid] at this
      simp [ID_KEY, ID_SN] at this; omega

end

/-! ## `KDIG` -/

theorem ofNat_toNat' (n : Nat) : (Fp.ofNat n).toNat = n % 2013265921 := Fp.toNat_ofNat n

theorem pairs_getElem? : ∀ (l : Bytes) (i : Nat), 2 * i + 1 < l.length →
    (pairs l)[i]? = some (256 * (l[2 * i]!).toNat + (l[2 * i + 1]!).toNat)
  | a :: b :: rest, 0, _ => by simp [pairs]
  | a :: b :: rest, i + 1, h => by
    simp only [pairs, List.getElem?_cons_succ]
    rw [pairs_getElem? rest i (by simp at h; omega)]
    simp [show 2 * (i + 1) = 2 * i + 2 by omega]
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **The digest a closing `KEY` row receives is `sha256` of its key's bytes.** -/
theorem key_digest (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r : Nat} (hr : r < tr.height 1) (hl : kc tr r "last" = 1) :
    ∀ b, b < 32 → kc tr r "dg" b = ((sha256 (keyBytes tr (kc tr r "kid")))[b]!).toNat ∧
      (sha256 (keyBytes tr (kc tr r "kid"))).length = 32 := by
  have hlog := key_log hH
  have hc := key_hc hH
  have hH1 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have ha : kc tr r "act" = 1 := gate_of_one (key_h hc hr m_last_act) hl
  obtain ⟨hk, hj, -, -⟩ := key_inv hc hlog r hr ha
  -- the digest receive
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 1) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact key_sd_r_mem) hr rfl
    (ev_one_eval (show ev tr 1 r pub (Key.c "last") = 1 from hl))
  obtain ⟨d, hd, i, hi, hb, hs, hp, he⟩ := sender_m5a B_SHA_DIGEST 0 (by simp [m5aAir]) (sd_only D) hxD
    (recv_sent hH hm)
  change i ∈ shaTable.interactions at hi
  obtain rfl := filter_one_mem sha_sd_s hi hb hs
  have hdm : tr.cell 0 d ZkFormal.Sha.Layout.colDmult = 1 := by
    have := multNat_one_bit (g := Expr.col ZkFormal.Sha.Layout.colDmult false) (by decide) hp
    exact this
  have hL : ZkFormal.Sha.ShaLocal tr 0 pub :=
    ZkFormal.Sha.shaLocal_of_holds hH (t := 0) (busBytes := B_SHA_BYTES) (busDigest := B_SHA_DIGEST)
      (by rw [fullAir_len]; omega) rfl
  obtain ⟨mm, dg, -, hdg, hmsg, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hL B_SHA_BYTES B_SHA_DIGEST hd hdm
  rw [hmsg] at he
  simp only [rcv, Interaction.msgVal, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq] at he
  obtain ⟨eid, elen, edg⟩ := he
  have hid : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = ID_KEY + kc tr r "kid" := by
    rw [← eid]
    exact ev_id _ _ (by rw [ev_kc]; omega) (by decide) |>.trans (by rw [ev_kc])
  -- every message byte is the key's byte
  have hbyte : ∀ k, k < mm.length → k % 2013265921 < 2 ^ 20 ∧
      (keyBytes tr (kc tr r "kid"))[k % 2013265921]? = some mm[k]! := by
    intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    obtain ⟨h1, h2, -⟩ := key_byte hH hxB hxK (by omega) hid hmb
    rw [ofNat_toNat'] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2, ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega), UInt8.ofNat_toNat]
  have hlen : mm.length ≤ 2 ^ 20 := by
    rcases Nat.lt_or_ge (2 ^ 20) mm.length with h | h
    · have := (hbyte (2 ^ 20) h).1
      rw [Nat.mod_eq_of_lt (by decide)] at this
      omega
    · exact h
  have elen' : mm.length = kc tr r "j" + 1 := by
    have := congrArg Fp.toNat elen
    change ev tr 1 r pub (Key.c "j" + 1) = _ at this
    rw [ev_succ_small _ (by rw [ev_kc]; omega), ev_kc, ofNat_toNat',
      Nat.mod_eq_of_lt (show mm.length < 2013265921 by omega)] at this
    omega
  have hkb : (keyBytes tr (kc tr r "kid")).length = kc tr r "j" + 1 := by
    unfold keyBytes
    rw [List.length_map, keyRows_length hc hlog hr ha hl]
  have hmm : mm = keyBytes tr (kc tr r "kid") := by
    apply List.ext_getElem?
    intro k
    rcases Nat.lt_or_ge k mm.length with h | h
    · have := (hbyte k h).2
      rw [Nat.mod_eq_of_lt (by omega)] at this
      rw [this, List.getElem?_eq_getElem h, getElem!_def, List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none h, List.getElem?_eq_none (by omega)]
  subst hmm
  have hdl : dg.length = 32 := by
    have := congrArg List.length edg
    simp at this; omega
  intro b hb
  refine ⟨?_, by show (ArenaCore.sha256 _).length = 32; rw [← hdg]; exact hdl⟩
  have := congrArg (fun l => (l[b]?).map Fp.toNat) edg
  simp only [List.getElem?_map, List.getElem?_range hb, Option.map_some, List.getElem?_eq_getElem
    (show b < dg.length by omega)] at this
  have e := Option.some.inj this
  change ev tr 1 r pub (Key.c "dg" b) = _ at e
  rw [ev_kc r "dg" b, ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt dg[b]; omega)] at e
  show _ = ((ArenaCore.sha256 _)[b]!).toNat
  rw [e, ← hdg, getElem!_def, List.getElem?_eq_getElem (show b < dg.length by omega)]

end

theorem ev_limb {tr : Trace Fp} {t r : Nat} {pub : List Fp} (a b : Expr) (ha : ev tr t r pub a < 256)
    (hb : ev tr t r pub b < 256) : ev tr t r pub (K 256 * a + b) = 256 * ev tr t r pub a + ev tr t r pub b := by
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const, show 256 % 2013265921 = 256 from rfl,
    Nat.mod_eq_of_lt (show 256 * ev tr t r pub a < 2013265921 by omega),
    Nat.mod_eq_of_lt (show 256 * ev tr t r pub a + ev tr t r pub b < 2013265921 by omega)]

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **Every `KDIG` message sent is `(kid, pairs (sha256 (keyBytes kid)))`.** -/
theorem kdig_sent (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_KDIG true) :
    ∃ x ls, m = x :: ls ∧ ls.map Fp.toNat = pairs (sha256 (keyBytes tr x.toNat)) := by
  have hc := key_hc hH
  obtain ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ :=
    sender_m5a B_KDIG 1 (by simp [m5aAir]) (key_only D B_KDIG (.inr (.inr rfl))) hxG hm
  change i ∈ Key.interactions at hi
  obtain rfl := filter_one_mem key_kdig_s hi hb hs
  obtain ⟨b, hbm, hbe⟩ := multNat_pos _ hp
  obtain ⟨k, hk, rfl⟩ := mem_bits hbm
  have hl : kc tr r "last" = 1 := gate_of_one (key_h hc hr (m_mdig k hk)) (eval_one_ev hbe)
  have hd := key_digest hH hxB hxD hxK hr hl
  refine ⟨_, _, rfl, ?_⟩
  show _ = pairs (sha256 (keyBytes tr (kc tr r "kid")))
  have hlen : (sha256 (keyBytes tr (kc tr r "kid"))).length = 32 := (hd 0 (by decide)).2
  apply List.ext_getElem?
  intro q
  rcases Nat.lt_or_ge q 16 with h | h
  · rw [pairs_getElem? _ q (by omega)]
    simp only [sndBits, Interaction.msgVal, List.map_map, pack2, List.getElem?_map, List.getElem?_range h,
      Option.map_some, Function.comp]
    congr 1
    have e1 := (hd (2 * q) (by omega)).1
    have e2 := (hd (2 * q + 1) (by omega)).1
    have l1 := UInt8.toNat_lt ((sha256 (keyBytes tr (kc tr r "kid")))[2 * q]!)
    have l2 := UInt8.toNat_lt ((sha256 (keyBytes tr (kc tr r "kid")))[2 * q + 1]!)
    change ev tr 1 r pub (K 256 * Key.c "dg" (2 * q) + Key.c "dg" (2 * q + 1)) = _
    rw [ev_limb _ _ (by rw [ev_kc r "dg" (2 * q), e1]; omega) (by rw [ev_kc r "dg" (2 * q + 1), e2]; omega),
      ev_kc r "dg" (2 * q), ev_kc r "dg" (2 * q + 1), e1, e2]
  · rw [List.getElem?_eq_none (by simp [sndBits, pack2]; omega),
      List.getElem?_eq_none (by rw [pairs_length, hlen]; omega)]

/-- **`KDIG` lookups**: every received `KDIG` message is `(kid, pairs (sha256 (keyBytes kid)))`. -/
theorem kdig_recv (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_KDIG false) :
    ∃ x ls, m = x :: ls ∧ ls.map Fp.toNat = pairs (sha256 (keyBytes tr x.toNat)) :=
  kdig_sent hH hxB hxD hxK hxG (recv_sent hH hm)

theorem wsb_kdig_mem : rcv B_KDIG (Wsb.c "real") (Wsb.c "kid" :: Wsb.vec "kd" 16) ∈ Wsb.interactions :=
  memD_mem (by decide)

/-- **A real `WSB` row's `kd` limbs are `pairs (sha256 (keyBytes kid))`** (so `< 2^16`). -/
theorem wsb_kd (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false)
    {r : Nat} (hr : r < tr.height 5) (hreal : ev tr 5 r pub (Wsb.c "real") = 1) :
    (List.range 16).map (fun u => ev tr 5 r pub (Wsb.c "kd" u)) =
      pairs (sha256 (keyBytes tr (ev tr 5 r pub (Wsb.c "kid")))) := by
  have hm := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 5) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact wsb_kdig_mem) hr rfl (ev_one_eval hreal)
  obtain ⟨x, ls, he, hls⟩ := kdig_recv hH hxB hxD hxK hxG hm
  simp only [rcv, Interaction.msgVal, List.map_cons, List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [show ev tr 5 r pub (Wsb.c "kid") = ((Wsb.c "kid").eval tr 5 r pub).toNat from rfl, ← hls]
  simp [Wsb.vec, List.map_map, Function.comp]
  intro a _; rfl

theorem pairs_lt16 (l : Bytes) : ∀ x ∈ pairs l, x < 2 ^ 16 := pairs_lt l

end

end StateM5a.KeyDigest
