import StateM5a.SnContKey1

/-!
# StateM5a.SnContKey2 — the `SNC` part of a continued head's hashed `hexPrefix` comes from its chunks

`SnContRec2.cont_node` gives the message of a hashing continued head as `serC … M …` with `M` the
bytes at offsets `37 .. 4 + hplen` (an existential list).  **`cont_msg_snc`**: with `Sha256CR`
(the SHA-256 table's message `mm` hashes to the same digest, so `mm` is that `serC`), every byte
`M[i]` was sent by an active `SNC` chunk of the head (`rid = r`) at offset `37 + i = 5 + 32·c + m`
(`ha_m = 1`), and is its `hp_m`.

The one fact about the head's own byte sends used here is **`head_send_pos`**: a firing
`serBytes` send of a continued head is at an offset outside `[37, 5 + hplen)` (the header, the
32 head `hp` bytes, the payload and the memory) — a statement independent of how the hex-prefix
length is serialized.
-/

namespace StateM5a.SnContKey2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.SnContHead StateM5a.SnContChain StateM5a.SnContByte
open StateM5a.SnContSer StateM5a.SnContSer2 StateM5a.SnContMem StateM5a.SnContRec2

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat} {x mb : Nat → Expr}

/-- **A continued head's byte sends avoid the `SNC` offsets** `[37, 5 + hplen)`. -/
theorem head_send_pos (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hH32 : 32 ≤ ev tr 3 r pub (Sn.c "hplen")) (hHb : ev tr 3 r pub (Sn.c "hplen") < 2 ^ 26)
    {id g : Expr} (hg : ev tr 3 r pub g = 1)
    {i : Interaction} (hi : i ∈ Sn.serBytes id g x mb) (hp : 0 < i.multNat tr 3 r pub) :
    ∃ pe ve, i.msg = [id, pe, ve] ∧
      (ev tr 3 r pub pe < 37 ∨ 5 + ev tr 3 r pub (Sn.c "hplen") ≤ ev tr 3 r pub pe) := by
  obtain ⟨pe, ve, h1, -, h3, -⟩ := cont_ser_val hc hA hcont rfl hH32 (by omega) hg hi hp
  exact ⟨pe, ve, h1, h3⟩

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 4000000 in
/-- **The `SNC` bytes of a continued head's hashed message are its chunks' `hp` bytes.** -/
theorem cont_msg_snc (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hCR : Walk.Sha256CR)
    {r par : Nat} (hr : r < tr.height 3) (hpar : par ≤ 1)
    {id g : Expr} {x mb hb : Nat → Expr}
    (hid : ev tr 3 r pub id = ID_SN + 2 * r + par)
    (hidE : (if par = 0 then Sn.idO else Sn.idN) = id)
    (hsd : rcv B_SHA_DIGEST g ([id, Sn.serLen] ++ (List.range 32).map hb) ∈ Sn.interactions)
    (hsb : ∀ i ∈ Sn.interactions, i.bus = B_SHA_BYTES → i.send = true → i.msg.head? = some id →
      i ∈ Sn.serBytes id g x mb)
    (hg : ev tr 3 r pub g = 1) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    {M : List Nat} (hML : M.length = ev tr 3 r pub (Sn.c "hplen") - 32) (hMb : ∀ v ∈ M, v < 256)
    (hdig : bytesOf ((pack2 hb).map (nE tr pub r)) =
        sha256 ((serC (ev tr 3 r pub (sm 3 (Sn.c "isE"))) (ev tr 3 r pub (Sn.c "hplen"))
          (fun m => ev tr 3 r pub (Sn.c "hp" m)) M (payLen tr pub r) (fun t => ev tr 3 r pub (x t))
          (fun b => ev tr 3 r pub (mb b))).map UInt8.ofNat)) :
    ∀ i, i < M.length → ∃ s, s < tr.height 8 ∧ ∃ m, m < 32 ∧ ev tr 8 s pub (Snc.c "act") = 1 ∧
      ev tr 8 s pub (Snc.c "rid") = r ∧ ev tr 8 s pub (Snc.c "ha" m) = 1 ∧
      1 ≤ ev tr 8 s pub (Snc.c "c") ∧ ev tr 8 s pub (Snc.c "c") ≤ 2 ^ 20 ∧
      37 + i = 5 + 32 * ev tr 8 s pub (Snc.c "c") + m ∧ M[i]! = ev tr 8 s pub (Snc.c "hp" m) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨-, hHb⟩ := ev_serLenC hH hxK hxR hr hA hcont
  have hH32 : 32 ≤ ev tr 3 r pub (Sn.c "hplen") := by
    rw [cont_hplen hH hxK hxR hr hA hcont]; omega
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
  obtain ⟨eid, -, edg⟩ := he
  have hcid : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = ID_SN + 2 * r + par := by
    rw [← eid]; exact hid
  -- the digest bytes are `dg`
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
  have hbd : bytesOf ((pack2 hb).map (nE tr pub r)) = dg := by
    rw [bytesOf_pack3 hb (fun b h => by rw [hdb b h]; exact UInt8.toNat_lt _)]
    apply List.ext_getElem?
    intro b
    rcases Nat.lt_or_ge b 32 with h | h
    · rw [List.getElem?_map, List.getElem?_range h, Option.map_some, hdb b h, UInt8.ofNat_toNat, getElem!_def,
        List.getElem?_eq_getElem (show b < dg.length by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  -- collision resistance: `mm` is the `serC` message
  have hmm := hCR _ _ (hdg.symm.trans (hbd.symm.trans hdig))
  intro i hi
  generalize hHd : ev tr 3 r pub (Sn.c "hplen") = H at hML hH32 hHb hmm
  have hk : 37 + i < mm.length := by
    rw [hmm]; simp [serC, hML]; omega
  -- the byte at `37 + i` is `M[i]`
  have hval : (mm[37 + i]!).toNat = M[i]! := by
    rw [hmm]
    have e : (serC (ev tr 3 r pub (sm 3 (Sn.c "isE"))) H (fun m => ev tr 3 r pub (Sn.c "hp" m)) M (payLen tr pub r)
        (fun t => ev tr 3 r pub (x t)) (fun b => ev tr 3 r pub (mb b)))[37 + i]? = M[i]? := by
      unfold serC
      rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp),
        List.getElem?_append_left (by simp; omega)]
      simp
    rw [getElem!_def, List.getElem?_map, e, List.getElem?_eq_getElem hi]
    simp only [Option.map_some, getElem!_def, List.getElem?_eq_getElem hi]
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (hMb _ (List.getElem_mem hi))
  -- its sender
  obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes (37 + i) hk
  obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
  have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
  rw [hmq, hbq, hsq] at hmb
  rcases cont_byte hH hxB hxK hr hpar hcid hmb with ⟨j, hj, hjb, hjs, hjh, hjp, hjm⟩ | hS
  · exfalso
    rw [hidE] at hjh
    obtain ⟨pe, ve, hpe, hout⟩ := head_send_pos hc hA hcont (by rw [hHd]; exact hH32) (by rw [hHd]; exact hHb) hg
      (hsb j hj hjb hjs hjh) hjp
    rw [Interaction.msgVal, hpe] at hjm
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hjm
    have ek : (37 + i) % P = ev tr 3 r pub pe := by
      have := congrArg Fp.toNat hjm.2.1; rw [ofNat_toNat'] at this; exact this
    rw [Nat.mod_eq_of_lt (by omega)] at ek
    rw [hHd] at hout
    omega
  · obtain ⟨s, hs, m, hm, ha, hrid, hha, c1, c2, hx, hy⟩ := hS
    rw [ofNat_toNat', Nat.mod_eq_of_lt (by omega)] at hx
    refine ⟨s, hs, m, hm, ha, hrid, hha, c1, c2, hx, ?_⟩
    have := congrArg Fp.toNat hy
    rw [ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[37 + i]!); omega), hval] at this
    exact this

end

end StateM5a.SnContKey2
