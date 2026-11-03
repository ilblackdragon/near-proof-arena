import StateM5a.SnDigest
import StateM5a.SnContChain

/-!
# StateM5a.SnContByte — who sends a byte under the ids of an `SN` head (any `cont`)

`cont_byte`: a byte received on `SHA_BYTES` under `ID_SN + 2·r0 + par` was sent either by `SN`
row `r0` (from its `serBytes` block led by `idO` / `idN`), or by an active `SNC` row `s` with
`rid = r0`, at serialization offset `5 + 32·c + m` (`m < 32`, `ha_m = 1`), carrying `hp_m`.
(`SnDigest.sn_byte` is the `cont = 0` case, where the second alternative is void.)
-/

namespace StateM5a.SnContByte

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest

local notation "P" => 2013265921

set_option maxRecDepth 100000

def sncSB (g : Expr) (id : Expr) (m : Nat) : Interaction :=
  snd B_SHA_BYTES (g * Snc.c "ha" m) [id, 5 + sm 32 (Snc.c "c") + K m, Snc.c "hp" m]

theorem snc_sb_eq : Snc.interactions.all (fun i => !(decide (i.bus = B_SHA_BYTES) && i.send) ||
    (List.range 32).any (fun m => decide (i = sncSB (Snc.c "gO") sncIdO m) ||
      decide (i = sncSB (Snc.c "gN") sncIdN m))) = true := by
  decide

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem snc_ha_one {r : Nat} (hc : ∀ e ∈ Snc.table.constraints, e.eval tr 8 r pub = 0) {g : Expr} (m : Nat)
    (hm : m < 32) (h : (g * Snc.c "ha" m).eval tr 8 r pub = 1) : ev tr 8 r pub (Snc.c "ha" m) = 1 := by
  have hb : ev tr 8 r pub (Snc.c "ha" m) = ev tr 8 r pub (Snc.a (2 * m)) :=
    eq_of_sub (snc_h hc (SnContChain.m_snc_ha m hm))
  have ha := bool_le (snc_h hc (m_snc_abool (2 * m) (by omega)))
  have h1 := eval_one_ev h
  rw [ev_hmul] at h1
  have hne : ev tr 8 r pub (Snc.c "ha" m) ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
  omega

/-- The `SNC` alternative of `cont_byte`. -/
def SncSent (tr : Trace Fp) (pub : List Fp) (r0 : Nat) (x y : Fp) : Prop :=
  ∃ s, s < tr.height 8 ∧ ∃ m, m < 32 ∧ ev tr 8 s pub (Snc.c "act") = 1 ∧
    ev tr 8 s pub (Snc.c "rid") = r0 ∧ ev tr 8 s pub (Snc.c "ha" m) = 1 ∧
    1 ≤ ev tr 8 s pub (Snc.c "c") ∧ ev tr 8 s pub (Snc.c "c") ≤ 2 ^ 20 ∧
    x.toNat = 5 + 32 * ev tr 8 s pub (Snc.c "c") + m ∧ y = (Snc.c "hp" m).eval tr 8 s pub

theorem ev_snc_pos {s m : Nat} (hc : ev tr 8 s pub (Snc.c "c") ≤ 2 ^ 20) (hm : m < 32) :
    ev tr 8 s pub (5 + sm 32 (Snc.c "c") + K m) = 5 + 32 * ev tr 8 s pub (Snc.c "c") + m := by
  have e1 : ev tr 8 s pub (sm 32 (Snc.c "c")) = 32 * ev tr 8 s pub (Snc.c "c") := by
    change ev tr 8 s pub (Expr.mul (.const 32) _) = _
    rw [ev_mul, ev_const, show 32 % P = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e2 : ev tr 8 s pub (5 + sm 32 (Snc.c "c")) = 5 + 32 * ev tr 8 s pub (Snc.c "c") := by
    rw [ev_hadd, e1, show ev tr 8 s pub (5 : Expr) = 5 from ev_const 5]
    exact Nat.mod_eq_of_lt (by omega)
  have e3 : ev tr 8 s pub (K m) = m := by
    rw [show ev tr 8 s pub (K m) = m % P from ev_const m]; exact Nat.mod_eq_of_lt (by omega)
  rw [ev_hadd, e2, e3]
  exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 4000000 in
/-- **A byte hashed under `ID_SN + 2·r0 + par`** was sent by `SN` row `r0` (its `idO` / `idN`
sends) or by an `SNC` chunk of `r0` (`SncSent`). -/
theorem cont_byte (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r0 par : Nat} (hr0 : r0 < tr.height 3) (hpar : par ≤ 1)
    {id x y : Fp} (hid : id.toNat = ID_SN + 2 * r0 + par)
    (hm : [id, x, y] ∈ busList (fullAir D extra nb np) tr pub B_SHA_BYTES false) :
    (∃ i ∈ Sn.interactions, i.bus = B_SHA_BYTES ∧ i.send = true ∧
      i.msg.head? = some (if par = 0 then Sn.idO else Sn.idN) ∧
      0 < i.multNat tr 3 r0 pub ∧ [id, x, y] = i.msgVal tr 3 r0 pub) ∨ SncSent tr pub r0 x y := by
  have hlog := key_log hH
  have hc := key_hc hH
  have hH1 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
  have hlt := Fp.toNat_lt id
  obtain ⟨t, hts, ht, r, hr, i, hi, hb, hs, hp, he⟩ := sender_lo [1, 2, 3, 8] (sb_only D) hxB
    (recv_sent hH hm) (by rw [hid, show ID_SN = 50331648 from rfl, show ID_ST = 67108864 from rfl]; omega)
  have hhead := congrArg List.head? he
  simp only [List.head?_cons] at hhead
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hts
  rcases hts with rfl | rfl | rfl | rfl
  · -- `KEY`: ids below `ID_KEY + 2^20`
    change i ∈ Key.interactions at hi
    obtain rfl := filter_one_mem key_sb_s hi hb hs
    have ha := eval_one_ev (multNat_one_bit rfl hp)
    obtain ⟨hk, -, -, -⟩ := key_inv hc hlog r hr ha
    simp only [snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e0 := congrArg Fp.toNat he.1
    change id.toNat = ev tr 1 r pub (K ID_KEY + Key.c "kid") at e0
    rw [ev_id _ _ (by rw [ev_kc]; omega) (by decide), hid, ev_kc] at e0
    simp [ID_KEY, ID_SN] at e0; omega
  · -- `BR`: ids from `ID_BR`
    change i ∈ Br.interactions at hi
    have := List.all_eq_true.1 br_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have hrid := br_rid hH r hr
    rcases this with h | h
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid")) at this
      rw [ev_id2 _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_SN, ID_BR] at this ⊢; omega
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_SN, ID_BR] at this ⊢; omega
  · -- `SN`
    left
    change i ∈ Sn.interactions at hi
    have := List.all_eq_true.1 sn_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have hrid := sn_rid hH r hr
    rcases this with h | h
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid")) at this
      rw [ev_id2 _ _ (by omega) (by decide), hid, hrid] at this
      have hr0' : r0 = r := by omega
      have hp0 : par = 0 := by omega
      subst hr0' hp0
      exact ⟨i, hi, hb, hs, by rw [h]; rfl, hp, he⟩
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      have hr0' : r0 = r := by omega
      have hp0 : par = 1 := by omega
      subst hr0' hp0
      exact ⟨i, hi, hb, hs, by rw [h]; rfl, hp, he⟩
  · -- `SNC`: a chunk of `r0`
    right
    change i ∈ Snc.interactions at hi
    have := List.all_eq_true.1 snc_sb_eq i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at this
    have hcs := snc_hc hH r hr
    obtain ⟨mm, hmm, h | h⟩ := this
    · subst h
      have hg := multNat_one_bit rfl hp
      have hha := snc_ha_one hcs mm hmm hg
      have ha := snc_ha_act hcs mm hmm hg
      have hrid := snc_rid hH hxK _ r hr ha rfl
      obtain ⟨c1, c2⟩ := snc_c_range hH hxK hr ha
      simp only [sncSB, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e0 := congrArg Fp.toNat he.1
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid")) at e0
      rw [ev_id2 _ _ hrid (by decide), hid] at e0
      have e1 := congrArg Fp.toNat he.2.1
      change x.toNat = ev tr 8 r pub (5 + sm 32 (Snc.c "c") + K mm) at e1
      rw [ev_snc_pos (by omega) hmm] at e1
      exact ⟨r, hr, mm, hmm, ha, by omega, hha, c1, by omega, e1, he.2.2.1⟩
    · subst h
      have hg := multNat_one_bit rfl hp
      have hha := snc_ha_one hcs mm hmm hg
      have ha := snc_ha_act hcs mm hmm hg
      have hrid := snc_rid hH hxK _ r hr ha rfl
      obtain ⟨c1, c2⟩ := snc_c_range hH hxK hr ha
      simp only [sncSB, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e0 := congrArg Fp.toNat he.1
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid") + 1) at e0
      rw [ev_id2' _ _ hrid (by decide), hid] at e0
      have e1 := congrArg Fp.toNat he.2.1
      change x.toNat = ev tr 8 r pub (5 + sm 32 (Snc.c "c") + K mm) at e1
      rw [ev_snc_pos (by omega) hmm] at e1
      exact ⟨r, hr, mm, hmm, ha, by omega, hha, c1, by omega, e1, he.2.2.1⟩

end

end StateM5a.SnContByte
