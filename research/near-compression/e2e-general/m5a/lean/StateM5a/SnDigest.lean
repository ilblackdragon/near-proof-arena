import StateM5a.SnSer

/-!
# StateM5a.SnDigest — a hashing `SN` head's bytes and digest from `Holds`

An `SN` row hashing its old node (`gsha`) or its final new node (`gfin = gnew − nref`) receives
`SHA_DIGEST(id, serLen, digest)` from the SHA-256 table; by its contract
(`ZkFormal.Sha.sha_digest_contract_closed`) `digest = sha256 m` for a message `m` every byte of
which was received on `SHA_BYTES` as `(id, i, m[i])`.  The id is `ID_SN + 2·rid` (old) or `+ 1`
(new), `rid` the row index.  For a head whose key does not continue (`cont = 0`):

* **`snc_cont`**: an active `SNC` row's `rid` is an `SN` row with `cont = 1` (the `KC` chain down
  to its index-1 message, which only a continuing `SN` head sends) — so no `SNC` row sends under
  this row's ids;
* **`sn_byte`**: every byte hashed under those ids was sent by this row's `Sn.serBytes` block;
* **`sn_node`**: `m = snSerF` (`SnSer.sn_ser_ok` places each send), so every `snSerF` entry is a
  byte and the received digest is `sha256 snSerF`.

No cryptographic assumption.
-/

namespace StateM5a.SnDigest

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The `SN` interactions of one node -/

theorem sn_sb_old : Sn.interactions.filter
    (fun i => decide (i.bus = B_SHA_BYTES ∧ i.send = true ∧ i.msg.head? = some Sn.idO)) =
    Sn.serBytes Sn.idO (Sn.c "gsha") (fun t => Sn.c "x" t) (fun b => Sn.c "mem" b) := by
  decide

theorem sn_sb_new : Sn.interactions.filter
    (fun i => decide (i.bus = B_SHA_BYTES ∧ i.send = true ∧ i.msg.head? = some Sn.idN)) =
    Sn.serBytes Sn.idN Sn.gfin (fun t => Sn.c "nx" t) (fun b => Sn.c "nmem" b) := by
  decide

theorem sn_sd_old : rcv B_SHA_DIGEST (Sn.c "gsha")
    ([Sn.idO, Sn.serLen] ++ (List.range 32).map fun b => Sn.c "ho" b) ∈ Sn.interactions :=
  memD_mem (by decide)

theorem sn_sd_new : rcv B_SHA_DIGEST Sn.gfin
    ([Sn.idN, Sn.serLen] ++ (List.range 32).map fun b => Sn.c "hn" b) ∈ Sn.interactions :=
  memD_mem (by decide)

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-! ## `SNC` rows belong to continuing heads -/

/-- **An active `SNC` row's `rid` is an `SN` row whose key continues.** -/
theorem snc_cont (hH : Holds (fullAir D extra nb np) pub tr)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) :
    ∀ v r, r < tr.height 8 → ev tr 8 r pub (Snc.c "act") = 1 → ev tr 8 r pub (Snc.c "c") = v →
      ∃ s, s < tr.height 3 ∧ ev tr 8 r pub (Snc.c "rid") = s ∧ ev tr 3 s pub (Sn.c "cont") = 1 := by
  have hH8 : tr.height 8 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (snc_log hH)
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
      have hco := eval_one_ev (multNat_one_bit rfl hp)
      simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
      have e := toNat_eq he.1
      exact ⟨t, ht, by rw [e, sn_rid hH t ht], hco⟩
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

/-! ## Who sent a byte under an `SN` id -/

/-- **A byte hashed under `ID_SN + 2·r0 + par`** of a head with `cont = 0` was sent by `SN` row
`r0`, from the `SHA_BYTES` sends led by `idO` (`par = 0`) / `idN` (`par = 1`). -/
theorem sn_byte (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r0 par : Nat} (hr0 : r0 < tr.height 3) (hcont : ev tr 3 r0 pub (Sn.c "cont") = 0) (hpar : par ≤ 1)
    {id x y : Fp} (hid : id.toNat = ID_SN + 2 * r0 + par)
    (hm : [id, x, y] ∈ busList (fullAir D extra nb np) tr pub B_SHA_BYTES false) :
    ∃ i ∈ Sn.interactions, i.bus = B_SHA_BYTES ∧ i.send = true ∧
      i.msg.head? = some (if par = 0 then Sn.idO else Sn.idN) ∧
      0 < i.multNat tr 3 r0 pub ∧ [id, x, y] = i.msgVal tr 3 r0 pub := by
  have hlog := key_log hH
  have hc := key_hc hH
  have hH1 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
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
  · -- `SNC`: its `rid` is a continuing head, so not `r0`
    change i ∈ Snc.interactions at hi
    have := List.all_eq_true.1 snc_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨mm, hmm, h | h⟩ := this
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      obtain ⟨s, hs3, hsr, hsc⟩ := snc_cont hH hxK _ r hr ha rfl
      have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h.2))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid")) at this
      rw [ev_id2 _ _ hrid (by decide), hid] at this
      have : s = r0 := by omega
      subst this; omega
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      obtain ⟨s, hs3, hsr, hsc⟩ := snc_cont hH hxK _ r hr ha rfl
      have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h.2))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid") + 1) at this
      rw [ev_id2' _ _ hrid (by decide), hid] at this
      have : s = r0 := by omega
      subst this; omega

/-! ## The node's message -/

theorem ev_serLenS {r : Nat} (hpl : ev tr 3 r pub (Sn.c "hplen") ≤ 33) (hL : ev tr 3 r pub (Sn.c "isL") ≤ 1) :
    ev tr 3 r pub Sn.serLen = 45 + ev tr 3 r pub (Sn.c "hplen") + 4 * ev tr 3 r pub (Sn.c "isL") := by
  unfold Sn.serLen
  rw [ev_hadd, ev_hadd, show ev tr 3 r pub (45 : Expr) = 45 from ev_const 45, ev3_sm]
  omega

/-- **A hashing `SN` head's message is `snSerF`** (generic in the node's columns): every entry is a
byte, and the received digest is its SHA-256. -/
theorem sn_node (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r par : Nat} (hr : r < tr.height 3) (hpar : par ≤ 1)
    {id g : Expr} {x mb hb : Nat → Expr}
    (hid : ev tr 3 r pub id = ID_SN + 2 * r + par)
    (hidE : (if par = 0 then Sn.idO else Sn.idN) = id)
    (hsd : rcv B_SHA_DIGEST g ([id, Sn.serLen] ++ (List.range 32).map hb) ∈ Sn.interactions)
    (hsb : ∀ i ∈ Sn.interactions, i.bus = B_SHA_BYTES → i.send = true → i.msg.head? = some id →
      i ∈ Sn.serBytes id g x mb)
    (hg : ev tr 3 r pub g = 1) (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    (∀ v ∈ snSerF tr pub r x mb, v.toNat < 256) ∧
      bytesOf ((pack2 hb).map (nE tr pub r)) =
        sha256 ((snSerF tr pub r x mb).map fun v => UInt8.ofNat v.toNat) := by
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hpl := FieldRows2.sn_hplen hc hA hcont
  have hkl := (FieldRows2.sn_flags hc hcont).1
  -- the digest receive and the SHA-256 contract
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact hsd) hr rfl (ev_one_eval hg)
  obtain ⟨d, hd, i, hi, hbd, hs, hp, he⟩ := sender_m5a B_SHA_DIGEST 0 (by simp [m5aAir]) (sd_only D) hxD
    (recv_sent hH hm)
  change i ∈ shaTable.interactions at hi
  obtain rfl := filter_one_mem sha_sd_s hi hbd hs
  have hdm : tr.cell 0 d ZkFormal.Sha.Layout.colDmult = 1 :=
    multNat_one_bit (g := Expr.col ZkFormal.Sha.Layout.colDmult false) (by decide) hp
  have hLc : ZkFormal.Sha.ShaLocal tr 0 pub :=
    ZkFormal.Sha.shaLocal_of_holds hH (t := 0) (busBytes := B_SHA_BYTES) (busDigest := B_SHA_DIGEST)
      (by rw [fullAir_len]; omega) rfl
  obtain ⟨mm, dg, -, hdg, hmsg, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hLc B_SHA_BYTES B_SHA_DIGEST hd hdm
  rw [hmsg] at he
  simp only [rcv, Interaction.msgVal, List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at he
  obtain ⟨eid, elen, edg⟩ := he
  have hcid : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = ID_SN + 2 * r + par := by
    rw [← eid]; exact hid
  -- every message byte sits at its `snSerF` position
  have hbyte : ∀ k, k < mm.length → k % P < (snSerF tr pub r x mb).length ∧
      (snSerF tr pub r x mb)[k % P]? = some (Fp.ofNat (mm[k]!).toNat) := by
    intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    obtain ⟨j, hj, hjb, hjs, hjh, hjp, hjm⟩ := sn_byte hH hxB hxK hr hcont hpar hcid hmb
    rw [hidE] at hjh
    obtain ⟨pe, ve, hpe, hlt, hget⟩ := sn_ser_ok hc hA hcont hg (hsb j hj hjb hjs hjh) hjp
    rw [Interaction.msgVal, hpe] at hjm
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hjm
    obtain ⟨-, e1, e2⟩ := hjm
    have ek : k % P = ev tr 3 r pub pe := by
      have := congrArg Fp.toNat e1; rw [ofNat_toNat'] at this; exact this
    rw [ek, hget, e2.1]
    exact ⟨hlt, rfl⟩
  -- the message is `snSerF`
  have hSl := snSerF_length (tr := tr) (pub := pub) (r := r) (x := x) (mb := mb)
  have hlen : mm.length = (snSerF tr pub r x mb).length := by
    have e := congrArg Fp.toNat elen
    rw [ofNat_toNat'] at e
    change ev tr 3 r pub Sn.serLen = _ at e
    rw [ev_serLenS (by omega) hL, ← hSl] at e
    rcases Nat.lt_or_ge (snSerF tr pub r x mb).length mm.length with h | h
    · have := (hbyte _ h).1
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at e; omega
  have hget : ∀ k, k < mm.length → (snSerF tr pub r x mb)[k]? = some (Fp.ofNat (mm[k]!).toNat) :=
    fun k hk => by have := (hbyte k hk).2; rwa [Nat.mod_eq_of_lt (by omega)] at this
  have hS : ∀ v ∈ snSerF tr pub r x mb, v.toNat < 256 := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have := hget k (by omega)
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [this, ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega)]
    exact UInt8.toNat_lt _
  have hmm : (snSerF tr pub r x mb).map (fun v => UInt8.ofNat v.toNat) = mm := by
    apply List.ext_getElem?
    intro k
    rcases Nat.lt_or_ge k mm.length with h | h
    · rw [List.getElem?_map, hget k h, Option.map_some, ofNat_toNat',
        Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega), UInt8.ofNat_toNat,
        getElem!_def, List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
  refine ⟨hS, ?_⟩
  rw [hmm, show sha256 mm = dg from hdg.symm]
  -- the digest bytes
  have hdl : dg.length = 32 := by
    have := congrArg List.length edg
    simp at this; omega
  have hdb : ∀ b, b < 32 → ev tr 3 r pub (hb b) = (dg[b]!).toNat := by
    intro b hb'
    have := congrArg (fun l => (l[b]?).map Fp.toNat) edg
    simp only [List.getElem?_map, List.getElem?_range hb', Option.map_some, List.getElem?_eq_getElem
      (show b < dg.length by omega)] at this
    have e := Option.some.inj this
    change ev tr 3 r pub (hb b) = _ at e
    have hlt := UInt8.toNat_lt (dg[b]'(by omega))
    rw [e, ofNat_toNat', Nat.mod_eq_of_lt (by omega), getElem!_def,
      List.getElem?_eq_getElem (show b < dg.length by omega)]
  rw [bytesOf_pack3 hb (fun b h => by rw [hdb b h]; exact UInt8.toNat_lt _)]
  apply List.ext_getElem?
  intro b
  rcases Nat.lt_or_ge b 32 with h | h
  · rw [List.getElem?_map, List.getElem?_range h, Option.map_some, hdb b h, UInt8.ofNat_toNat, getElem!_def,
      List.getElem?_eq_getElem (show b < dg.length by omega)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end

end StateM5a.SnDigest
