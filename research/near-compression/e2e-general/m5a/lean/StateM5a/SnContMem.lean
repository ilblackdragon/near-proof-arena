import StateM5a.SnContByte
import StateM5a.SnContSer
import StateM5a.SnRec

/-!
# StateM5a.SnContMem — a continued head's memory bytes are SHA-256 message bytes

For an `SN` head with `cont = 1` hashing a node (old: `gsha`, new: `gfin`; a continued key is
always hashed, `cont·(gold − gsha) = 0`, `cont·nref = 0`):

* `cont_rl` / `cont_hplen`: its `rl` is an `SNC` chain total, even and `≤ 64·2^20`, so
  `hplen = 32 + rl/2`;
* `cont_snc_lt`: every byte an `SNC` chunk of the head sends sits at an offset `< 5 + hplen`
  (`SnContChain.snc_head`: the chunk's index and length are accounted for in `rl`);
* `cont_msg`: the SHA-256 message `m` under the head's id has length exactly
  `serLen = 45 + hplen + 4·isL` (every received offset is below it), and its entries at
  `37 + hplen + 4·isL + b` are the head's memory bytes `mb b` — so each `mb b < 256`;
* `cont_old_mem` / `cont_new_mem`: the instances `mem` (`gold`) and `nmem` (`gnew`).

No cryptographic assumption.  Extra premise beyond `SnRange`'s: `hxRr` (the extra tables have
no `KCR` interaction), `hxR` (they do not send on `KCR`).
-/

namespace StateM5a.SnContMem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.SnContHead StateM5a.SnContChain StateM5a.SnContByte
open StateM5a.SnContSer

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)

include hH hxK hxR in
/-- A continued head's `rl` is an `SNC` chain total: even and small. -/
theorem cont_rl {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ev tr 3 r pub (Sn.c "rl") % 2 = 0 ∧ ev tr 3 r pub (Sn.c "rl") ≤ 64 * 2 ^ 20 := by
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_kcr_r_mem) hr rfl (ev_one_eval hcont)
  obtain ⟨t, ht, i, hi, hb, hs, hp, he⟩ := sender_m5a B_KCR 8 (by simp [m5aAir]) (kcr_only D) hxR
    (recv_sent hH hm)
  change i ∈ Snc.interactions at hi
  obtain rfl := filter_one_mem snc_kcr_s hi hb hs
  have hta := eval_one_ev (multNat_one_bit rfl hp)
  simp only [rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
  have e2 := toNat_eq he.2.2.1
  obtain ⟨-, hev, hle⟩ := snc_v hH hxK hxR _ t ht hta rfl
  rw [e2]
  exact ⟨hev, hle⟩

include hH hxK hxR in
theorem cont_hplen {r : Nat} (hr : r < tr.height 3) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ev tr 3 r pub (Sn.c "hplen") = 32 + ev tr 3 r pub (Sn.c "rl") / 2 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨h1, h2⟩ := cont_rl hH hxK hxR hr hcont
  exact ch_hplen hc hA hcont h1 (by omega)

include hH hxK hxR hxRr in
/-- **An `SNC` chunk of a continued head sends below offset `5 + hplen`.** -/
theorem cont_snc_lt {r : Nat} (hr : r < tr.height 3) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) {x y : Fp} (hS : SncSent tr pub r x y) :
    x.toNat < 5 + ev tr 3 r pub (Sn.c "hplen") := by
  obtain ⟨s, hs, m, hm, ha, hrid, hha, c1, c2, hx, -⟩ := hS
  obtain ⟨c, hcc⟩ : ∃ c, ev tr 8 s pub (Snc.c "c") = c + 1 := ⟨ev tr 8 s pub (Snc.c "c") - 1, by omega⟩
  obtain ⟨r0, hr0, hrid', hco, hrl⟩ := snc_head hH hxK hxR hxRr c s hs ha hcc
  have e : r0 = r := by omega
  subst e
  have hn := snc_ha_n (snc_hc hH s hs) m hm hha
  obtain ⟨hv, -, -⟩ := snc_v hH hxK hxR _ s hs ha rfl
  rw [cont_hplen hH hxK hxR hr hA hcont, hrl, hv, hx, hcc]
  omega

include hH hxK hxR in
theorem ev_serLenC {r : Nat} (hr : r < tr.height 3) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ev tr 3 r pub Sn.serLen = 45 + ev tr 3 r pub (Sn.c "hplen") + 4 * ev tr 3 r pub (Sn.c "isL") ∧
      ev tr 3 r pub (Sn.c "hplen") < 2 ^ 26 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hpl := cont_hplen hH hxK hxR hr hA hcont
  obtain ⟨-, h2⟩ := cont_rl hH hxK hxR hr hcont
  have hb : ev tr 3 r pub (Sn.c "hplen") < 2 ^ 26 := by omega
  refine ⟨?_, hb⟩
  unfold Sn.serLen
  rw [ev_hadd, ev_hadd, show ev tr 3 r pub (45 : Expr) = 45 from ev_const 45, ev3_sm,
    show 4 % P = 4 from rfl, Nat.mod_eq_of_lt (show 4 * ev tr 3 r pub (Sn.c "isL") < P by omega),
    Nat.mod_eq_of_lt (show 45 + ev tr 3 r pub (Sn.c "hplen") < P by omega), Nat.mod_eq_of_lt (by omega)]

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 4000000 in
/-- **A hashing continued head's memory bytes are bytes** (generic in the node's columns). -/
theorem cont_msg (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
    {r par : Nat} (hr : r < tr.height 3) (hpar : par ≤ 1)
    {id g : Expr} {x mb hb : Nat → Expr}
    (hid : ev tr 3 r pub id = ID_SN + 2 * r + par)
    (hidE : (if par = 0 then Sn.idO else Sn.idN) = id)
    (hsd : rcv B_SHA_DIGEST g ([id, Sn.serLen] ++ (List.range 32).map hb) ∈ Sn.interactions)
    (hsb : ∀ i ∈ Sn.interactions, i.bus = B_SHA_BYTES → i.send = true → i.msg.head? = some id →
      i ∈ Sn.serBytes id g x mb)
    (hg : ev tr 3 r pub g = 1) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  obtain ⟨hSL, hHb⟩ := ev_serLenC hH hxK hxR hr hA hcont
  generalize hHd : ev tr 3 r pub (Sn.c "hplen") = H at hSL hHb
  generalize hId : ev tr 3 r pub (Sn.c "isL") = I at hSL hL
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
  obtain ⟨mm, dg, -, -, hmsg, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hLc B_SHA_BYTES B_SHA_DIGEST hd hdm
  rw [hmsg] at he
  simp only [rcv, Interaction.msgVal, List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at he
  obtain ⟨eid, elen, -⟩ := he
  have hcid : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = ID_SN + 2 * r + par := by
    rw [← eid]; exact hid
  -- every received offset is below `serLen`; offsets from `37 + hplen + 4·isL` on carry `mb`
  have hpos : ∀ k, k < mm.length → k % P < 45 + H + 4 * I ∧
      (37 + H + 4 * I ≤ k % P → ∃ b, b < 8 ∧
        Fp.ofNat (mm[k]!).toNat = (mb b).eval tr 3 r pub ∧ k % P = 37 + H + 4 * I + b) := by
    intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    rcases cont_byte hH hxB hxK hr hpar hcid hmb with ⟨j, hj, hjb, hjs, hjh, hjp, hjm⟩ | hS
    · rw [hidE] at hjh
      obtain ⟨pe, ve, hpe, hlt, himp⟩ :=
        cont_ser_pos hc hA hcont hHd (by omega) hg (hsb j hj hjb hjs hjh) hjp
      rw [Interaction.msgVal, hpe] at hjm
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hjm
      obtain ⟨-, e1, e2⟩ := hjm
      have ek : k % P = ev tr 3 r pub pe := by
        have := congrArg Fp.toNat e1; rw [ofNat_toNat'] at this; exact this
      rw [hId] at hlt himp
      refine ⟨by rw [ek]; exact hlt, fun h => ?_⟩
      rw [ek] at h ⊢
      obtain ⟨b, hb8, rfl, hpb⟩ := himp h
      exact ⟨b, hb8, e2.1, hpb⟩
    · have := cont_snc_lt hH hxK hxR hxRr hr hA hcont hS
      rw [ofNat_toNat', hHd] at this
      exact ⟨by omega, fun h => by omega⟩
  -- the message length is `serLen`
  have hlen : mm.length = 45 + H + 4 * I := by
    have e := congrArg Fp.toNat elen
    rw [ofNat_toNat'] at e
    change ev tr 3 r pub Sn.serLen = mm.length % P at e
    rw [hSL] at e
    rcases Nat.lt_or_ge (45 + H + 4 * I) mm.length with h | h
    · have := (hpos _ h).1
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at e; omega
  intro b hb8
  have hk : 37 + H + 4 * I + b < mm.length := by omega
  obtain ⟨b', -, ev', hpb⟩ := (hpos _ hk).2 (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
  rw [Nat.mod_eq_of_lt (by omega)] at hpb
  have e : b' = b := by omega
  subst e
  have := congrArg Fp.toNat ev'
  rw [ofNat_toNat'] at this
  change _ = ev tr 3 r pub (mb b') at this
  rw [← this, Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[37 + H + 4 * I + b']!); omega)]
  exact UInt8.toNat_lt _

/-- **Old memory bytes of a continued head** (`gold`). -/
theorem cont_old_mem (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
    {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) : ∀ b, b < 8 → ev tr 3 r pub (Sn.c "mem" b) < 256 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hs := ch_gsha hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inl hs)
  exact cont_msg hH hxB hxD hxK hxR hxRr hr (par := 0) (Nat.zero_le _) (SnRec.ev_idS hH hr).1 rfl sn_sd_old
    (fun i hi hb hs hh => mem_of_filter sn_sb_old hi (pred_true hb hs hh)) hs hA hcont

/-- **New memory bytes of a continued head** (`gnew`). -/
theorem cont_new_mem (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
    {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gnew") = 1) : ∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hf := ch_gfin hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inr hg)
  exact cont_msg hH hxB hxD hxK hxR hxRr hr (par := 1) (Nat.le_refl _) (SnRec.ev_idS hH hr).2 rfl sn_sd_new
    (fun i hi hb hs hh => mem_of_filter sn_sb_new hi (pred_true hb hs hh)) hf hA hcont

end

end StateM5a.SnContMem
