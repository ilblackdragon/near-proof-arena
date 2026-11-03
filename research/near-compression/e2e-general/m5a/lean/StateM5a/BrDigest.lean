import StateM5a.VerStore
import StateM5a.BrSer

/-!
# StateM5a.BrDigest — `BrHashed` from `Holds`: a hashing `BR` row's digest is its node's SHA-256

A `BR` row that hashes its old node (`gsha`) or its final new node (`gfin = gnew − nref`) receives
`SHA_DIGEST(id, serLen, digest)` from the SHA-256 table, whose contract
(`ZkFormal.Sha.sha_digest_contract_closed`) says `digest = sha256 m` for a message `m` every byte
of which was received on `SHA_BYTES` as `(id, i, m[i])`.  The id is `ID_BR + 2·rid` (old) or
`+ 1` (new) with `rid` the row index, so the only sender of those bytes is this row's
`Br.serBytes` block for that node (`br_byte`; `KEY` / `SN` / `SNC` ids are disjoint, as in
`KeyDigest.key_byte`).  `BrSer.ser_ok` places each byte send at its position of `serF`, so
`m = serF` (as bytes; every `serF` entry is then a byte, `BrSer.serBytes_of`) and
`BrSer.grec_hashed` gives the record `Hashed` to the digest.

**`brHashed`**: `Holds` (with the extra tables silent on `SHA_BYTES` / `SHA_DIGEST` / `KC`) gives
`VerStore.BrHashed`.  No cryptographic assumption.
-/

namespace StateM5a.BrDigest

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.KcChain
open StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.BrSer StateM5a.VerStore

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The `BR` interactions of one node -/

theorem br_sb_old : Br.interactions.filter
    (fun i => decide (i.bus = B_SHA_BYTES ∧ i.send = true ∧ i.msg.head? = some Br.idO)) =
    Br.serBytes Br.idO (Br.c "gsha") (Br.c "gsha" * Br.c "hasv") (Br.c "hasv") (fun t => Br.c "vl" t)
      (fun t => Br.c "vh" t) (fun i => Br.c "f" i) Br.rank (fun i b => Br.ch i b) (fun b => Br.c "mem" b) := by
  decide

theorem br_sb_new : Br.interactions.filter
    (fun i => decide (i.bus = B_SHA_BYTES ∧ i.send = true ∧ i.msg.head? = some Br.idN)) =
    Br.serBytes Br.idN Br.gfin (Br.gfin * Br.c "nhv") (Br.c "nhv") (fun t => Br.c "nvl" t)
      (fun t => Br.c "nvh" t) (fun i => Br.c "nf" i) Br.nrank Br.newch (fun b => Br.c "nmem" b) := by
  decide

theorem br_sd_old : rcv B_SHA_DIGEST (Br.c "gsha")
    ([Br.idO, Br.serLen (Br.c "hasv") fun i => Br.c "f" i] ++ (List.range 32).map fun b => Br.c "ho" b) ∈
    Br.interactions := memD_mem (by decide)

theorem br_sd_new : rcv B_SHA_DIGEST Br.gfin
    ([Br.idN, Br.serLen (Br.c "nhv") fun i => Br.c "nf" i] ++ (List.range 32).map fun b => Br.c "hn" b) ∈
    Br.interactions := memD_mem (by decide)

theorem mem_of_filter {l L : List Interaction} {p : Interaction → Bool} (h : l.filter p = L) {i : Interaction}
    (hi : i ∈ l) (hp : p i = true) : i ∈ L := h ▸ List.mem_filter.2 ⟨hi, hp⟩

/-! ## Who sent a byte under a `BR` id -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- **A byte hashed under `ID_BR + 2·r0 + par`** was sent by `BR` row `r0`, from the `SHA_BYTES`
sends led by `idO` (`par = 0`) / `idN` (`par = 1`). -/
theorem br_byte (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r0 par : Nat} (hr0 : r0 < 2 ^ 20) (hpar : par ≤ 1) {id x y : Fp} (hid : id.toNat = ID_BR + 2 * r0 + par)
    (hm : [id, x, y] ∈ busList (fullAir D extra nb np) tr pub B_SHA_BYTES false) :
    ∃ i ∈ Br.interactions, i.bus = B_SHA_BYTES ∧ i.send = true ∧
      i.msg.head? = some (if par = 0 then Br.idO else Br.idN) ∧ r0 < tr.height 2 ∧
      0 < i.multNat tr 2 r0 pub ∧ [id, x, y] = i.msgVal tr 2 r0 pub := by
  have hlog := key_log hH
  have hc := key_hc hH
  have hH1 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  have hlt := Fp.toNat_lt id
  obtain ⟨t, hts, ht, r, hr, i, hi, hb, hs, hp, he⟩ := sender_set B_SHA_BYTES [1, 2, 3, 8] (sb_only D) hxB
    (recv_sent hH hm)
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
    simp [ID_KEY, ID_BR] at e0; omega
  · -- `BR`
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
      have hr0 : r0 = r := by omega
      have hp0 : par = 0 := by omega
      subst hr0 hp0
      exact ⟨i, hi, hb, hs, by rw [h]; rfl, hr, hp, he⟩
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      have hr0 : r0 = r := by omega
      have hp0 : par = 1 := by omega
      subst hr0 hp0
      exact ⟨i, hi, hb, hs, by rw [h]; rfl, hr, hp, he⟩
  · -- `SN`: ids from `ID_SN`
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
      simp [ID_SN, ID_BR] at this ⊢; omega
    · have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid") + 1) at this
      rw [ev_id2' _ _ (by omega) (by decide), hid, hrid] at this
      simp [ID_SN, ID_BR] at this ⊢; omega
  · -- `SNC`: an active row, `rid < 2^20`
    change i ∈ Snc.interactions at hi
    have := List.all_eq_true.1 snc_sb_ids i hi
    simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨mm, hmm, h | h⟩ := this
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h.2))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid")) at this
      rw [ev_id2 _ _ hrid (by decide), hid] at this
      simp [ID_SN, ID_BR] at this ⊢; omega
    · have ha := snc_ha_act (snc_hc hH r hr) mm hmm (multNat_one_bit h.1 hp)
      have hrid := snc_rid hH hxK _ r hr ha rfl
      have := congrArg (fun o => o.map Fp.toNat) (hhead.trans (head_eval h.2))
      simp only [Option.map_some, Option.some.injEq] at this
      change id.toNat = ev tr 8 r pub (K ID_SN + sm 2 (Snc.c "rid") + 1) at this
      rw [ev_id2' _ _ hrid (by decide), hid] at this
      simp [ID_SN, ID_BR] at this ⊢; omega

theorem ev_serLen {r : Nat} {hv : Expr} {fl : Nat → Expr} (hhv : ev tr 2 r pub hv ≤ 1)
    (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1) :
    ev tr 2 r pub (Br.serLen hv fl) = 11 + 36 * ev tr 2 r pub hv + 32 * cnt (flF tr pub r fl) 16 := by
  have hc := cnt_le (flF tr pub r fl) 16
  unfold Br.serLen
  rw [ev_hadd, ev_base (show ev tr 2 r pub (11 : Expr) = 11 from ev_const 11) (by omega) hhv, ev_sm,
    ev_rank hfl 16 (Nat.le_refl _), show 32 % P = 32 from rfl,
    Nat.mod_eq_of_lt (show 32 * cnt (flF tr pub r fl) 16 < P by omega)]
  omega

/-- **A hashing node's record is `Hashed` to its digest** (generic in the node's columns). -/
theorem node_hashed (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r par : Nat} (hr : r < tr.height 2) (hpar : par ≤ 1)
    {id g gv hv : Expr} {vl vh fl isn mb hb : Nat → Expr} {cb : Nat → Nat → Expr}
    (hid : ev tr 2 r pub id = ID_BR + 2 * r + par)
    (hidE : (if par = 0 then Br.idO else Br.idN) = id)
    (hsd : rcv B_SHA_DIGEST g ([id, Br.serLen hv fl] ++ (List.range 32).map hb) ∈ Br.interactions)
    (hsb : ∀ i ∈ Br.interactions, i.bus = B_SHA_BYTES → i.send = true → i.msg.head? = some id →
      i ∈ Br.serBytes id g gv hv vl vh fl (fun i => sumE ((List.range i).map fl)) cb mb)
    (hg : ev tr 2 r pub g = 1) (hgv : ev tr 2 r pub gv = 1 → ev tr 2 r pub hv = 1)
    (hhv : ev tr 2 r pub hv ≤ 1) (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1)
    (hisn : ∀ i, i < 16 → ev tr 2 r pub (fl i) = 1 → ev tr 2 r pub (isn i) = 0) :
    SerBytes tr pub r hv vl vh fl cb mb ∧
      Hashed (gRec tr pub r hv vl vh fl isn cb mb) (bytesOf ((pack2 hb).map (bE tr pub r))) := by
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  -- the digest receive and the SHA-256 contract
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact hsd) hr rfl (ev_one_eval hg)
  obtain ⟨d, hd, i, hi, hbd, hs, hp, he⟩ := sender_m5a B_SHA_DIGEST 0 (by simp [m5aAir]) (sd_only D) hxD
    (recv_sent hH hm)
  change i ∈ shaTable.interactions at hi
  obtain rfl := filter_one_mem sha_sd_s hi hbd hs
  have hdm : tr.cell 0 d ZkFormal.Sha.Layout.colDmult = 1 :=
    multNat_one_bit (g := Expr.col ZkFormal.Sha.Layout.colDmult false) (by decide) hp
  have hL : ZkFormal.Sha.ShaLocal tr 0 pub :=
    ZkFormal.Sha.shaLocal_of_holds hH (t := 0) (busBytes := B_SHA_BYTES) (busDigest := B_SHA_DIGEST)
      (by rw [fullAir_len]; omega) rfl
  obtain ⟨mm, dg, -, hdg, hmsg, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hL B_SHA_BYTES B_SHA_DIGEST hd hdm
  rw [hmsg] at he
  simp only [rcv, Interaction.msgVal, List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at he
  obtain ⟨eid, elen, edg⟩ := he
  have hcid : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = ID_BR + 2 * r + par := by
    rw [← eid]; exact hid
  -- every message byte sits at its `serF` position
  have hbyte : ∀ k, k < mm.length → k % P < (serF tr pub r hv vl vh fl cb mb).length ∧
      (serF tr pub r hv vl vh fl cb mb)[k % P]? = some (Fp.ofNat (mm[k]!).toNat) := by
    intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    obtain ⟨j, hj, hjb, hjs, hjh, -, hjp, hjm⟩ := br_byte hH hxB hxK (by omega) hpar hcid hmb
    rw [hidE] at hjh
    obtain ⟨pe, ve, hpe, hlt, hget⟩ := ser_ok hg hgv hhv hfl (hsb j hj hjb hjs hjh) hjp
    rw [Interaction.msgVal, hpe] at hjm
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hjm
    obtain ⟨-, e1, e2⟩ := hjm
    have ek : k % P = ev tr 2 r pub pe := by
      have := congrArg Fp.toNat e1; rw [ofNat_toNat'] at this; exact this
    rw [ek, hget, e2.1]
    exact ⟨hlt, rfl⟩
  -- the message is `serF`
  have hSl := serF_length (vl := vl) (vh := vh) (cb := cb) (mb := mb) (fl := fl) hhv
  have hc16 := cnt_le (flF tr pub r fl) 16
  have hlen : mm.length = (serF tr pub r hv vl vh fl cb mb).length := by
    have e := congrArg Fp.toNat elen
    rw [ofNat_toNat'] at e
    change ev tr 2 r pub (Br.serLen hv fl) = _ at e
    rw [ev_serLen hhv hfl, ← hSl] at e
    rcases Nat.lt_or_ge (serF tr pub r hv vl vh fl cb mb).length mm.length with h | h
    · have := (hbyte _ h).1
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at e; omega
  have hget : ∀ k, k < mm.length → (serF tr pub r hv vl vh fl cb mb)[k]? = some (Fp.ofNat (mm[k]!).toNat) :=
    fun k hk => by have := (hbyte k hk).2; rwa [Nat.mod_eq_of_lt (by omega)] at this
  have hS : ∀ x ∈ serF tr pub r hv vl vh fl cb mb, x.toNat < 256 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := hget k (by omega)
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [this, ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega)]
    exact UInt8.toNat_lt _
  have hmm : (serF tr pub r hv vl vh fl cb mb).map (fun x => UInt8.ofNat x.toNat) = mm := by
    apply List.ext_getElem?
    intro k
    rcases Nat.lt_or_ge k mm.length with h | h
    · rw [List.getElem?_map, hget k h, Option.map_some, ofNat_toNat',
        Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega), UInt8.ofNat_toNat,
        getElem!_def, List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
  have hR := grec_hashed hhv hfl hisn (serBytes_of hS)
  rw [hmm, show sha256 mm = dg from hdg.symm] at hR
  -- the digest bytes
  have hdl : dg.length = 32 := by
    have := congrArg List.length edg
    simp at this; omega
  have hdb : ∀ b, b < 32 → ev tr 2 r pub (hb b) = (dg[b]!).toNat := by
    intro b hb'
    have := congrArg (fun l => (l[b]?).map Fp.toNat) edg
    simp only [List.getElem?_map, List.getElem?_range hb', Option.map_some, List.getElem?_eq_getElem
      (show b < dg.length by omega)] at this
    have e := Option.some.inj this
    change ev tr 2 r pub (hb b) = _ at e
    have hlt := UInt8.toNat_lt (dg[b]'(by omega))
    rw [e, ofNat_toNat', Nat.mod_eq_of_lt (by omega), getElem!_def,
      List.getElem?_eq_getElem (show b < dg.length by omega)]
  have hdig : bytesOf ((pack2 hb).map (bE tr pub r)) = dg := by
    rw [bytesOf_pack2 hb (fun b h => by rw [hdb b h]; exact UInt8.toNat_lt _)]
    apply List.ext_getElem?
    intro b
    rcases Nat.lt_or_ge b 32 with h | h
    · rw [List.getElem?_map, List.getElem?_range h, Option.map_some, hdb b h, UInt8.ofNat_toNat, getElem!_def,
        List.getElem?_eq_getElem (show b < dg.length by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  rw [hdig]
  exact ⟨serBytes_of hS, hR⟩

end

/-! ## Row facts -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
theorem br_bool_nhv (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) : ev tr 2 r pub (Br.c "nhv") ≤ 1 := by
  apply bool_le; apply FieldRows2.br_hold hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

set_option maxHeartbeats 4000000 in
theorem br_bool_nf' (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (i : Nat) (hi : i < 16) :
    ev tr 2 r pub (Br.c "nf" i) ≤ 1 := by
  apply bool_le; apply FieldRows2.br_hold hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

set_option maxHeartbeats 4000000 in
theorem br_gfin_nisn (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (i : Nat) (hi : i < 16)
    (hg : ev tr 2 r pub Br.gfin = 1) : ev tr 2 r pub (Br.nisn i) = 0 := by
  refine FieldVer.gate_zero (FieldRows2.br_hold hc ?_) hg
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

theorem ev_gfin (hg : ev tr 2 r pub (Br.c "gnew") = 1) (hn : ev tr 2 r pub (Br.c "nref") = 0) :
    ev tr 2 r pub Br.gfin = 1 := by
  unfold Br.gfin; rw [ev_sub, hg, hn]

end

/-! ## `BrHashed` -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem pred_true {i : Interaction} {id : Expr} (hb : i.bus = B_SHA_BYTES) (hs : i.send = true)
    (hh : i.msg.head? = some id) :
    decide (i.bus = B_SHA_BYTES ∧ i.send = true ∧ i.msg.head? = some id) = true := by
  simp [hb, hs, hh]

/-- **A row hashing its old node** (`gsha`): the old node's bytes and its record hashed to `ho`. -/
theorem br_old_node (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub (Br.c "gsha") = 1) :
    SerBytes tr pub r (Br.c "hasv") (fun t => Br.c "vl" t) (fun t => Br.c "vh" t) (fun i => Br.c "f" i) Br.ch
        (fun b => Br.c "mem" b) ∧
      Hashed (brOld tr pub r) (bytesOf ((pack2 fun b => Br.c "ho" b).map (E tr 2 r pub))) := by
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hrid := br_rid hH r hr
  rw [brOld_eq]
  exact node_hashed hH hxB hxD hxK hr (par := 0) (Nat.zero_le _)
    (by show ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid")) = _
        rw [ev_id2 _ _ (by omega) (by decide), hrid]; rfl)
    rfl br_sd_old (fun i hi hb hs hh => mem_of_filter br_sb_old hi (pred_true hb hs hh))
    hg (fun h => ev_gate_one hg h) (bool_le (FieldRows.hold rfl hc RowBrF.br_bool_hasv)) (FieldRows2.br_bool_f hc)
    (fun i hi _ => FieldVer.br_gsha_isn hc i hi hg)

/-- **A row hashing its new node** (`gfin = gnew − nref`). -/
theorem br_new_node (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    {r : Nat} (hr : r < tr.height 2) (hf : ev tr 2 r pub Br.gfin = 1) :
    SerBytes tr pub r (Br.c "nhv") (fun t => Br.c "nvl" t) (fun t => Br.c "nvh" t) (fun i => Br.c "nf" i)
        Br.newch (fun b => Br.c "nmem" b) ∧
      Hashed (brNew tr pub r) (bytesOf ((pack2 fun b => Br.c "hn" b).map (E tr 2 r pub))) := by
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by rw [fullAir_len]; omega)).2
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hrid := br_rid hH r hr
  rw [brNew_eq]
  exact node_hashed hH hxB hxD hxK hr (par := 1) (Nat.le_refl _)
    (by show ev tr 2 r pub (K ID_BR + sm 2 (Br.c "rid") + 1) = _
        rw [ev_id2' _ _ (by omega) (by decide), hrid])
    rfl br_sd_new (fun i hi hb hs hh => mem_of_filter br_sb_new hi (pred_true hb hs hh))
    hf (fun h => ev_gate_one hf h) (br_bool_nhv hc) (br_bool_nf' hc)
    (fun i hi _ => br_gfin_nisn hc i hi hf)

/-- **The hashing `BR` rows' records are hashed to their digests**, from `Holds`. -/
theorem brHashed (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false) : BrHashed tr pub :=
  ⟨fun _ hr hg => (br_old_node hH hxB hxD hxK hr hg).2,
   fun _ hr hg hn => (br_new_node hH hxB hxD hxK hr (ev_gfin hg hn)).2⟩

end

end StateM5a.BrDigest
