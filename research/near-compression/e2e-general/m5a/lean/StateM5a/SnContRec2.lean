import StateM5a.SnContMem
import StateM5a.SnContSer2

/-!
# StateM5a.SnContRec2 — the SHA-256 message of a hashing continued head

`cont_node`: a continued head (`cont = 1`) hashing a node (`g = 1`, id `ID_SN + 2·r + par`)
receives the digest `sha256 (serC …)` where

`serC = [3·isE, H % 256, H / 256, 0, 0] ++ hp_0..hp_31 ++ M ++ payload ++ memory bytes`,

`H = hplen < 2^16` (its `u32` bytes `(H % 256, H / 256, 0, 0)`, M5a-8), and `M` (`H − 32` bytes) is what the `SNC` chunks put at offsets `37 .. 4 + H`;
every entry is a byte.  (`SnContMem.cont_msg` used the same argument for the memory bytes.)
-/

namespace StateM5a.SnContRec2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.SnContHead StateM5a.SnContChain StateM5a.SnContByte
open StateM5a.SnContSer StateM5a.SnContSer2 StateM5a.SnContMem

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The serialization of a continued head's node (as naturals). -/
def serC (tag H : Nat) (hp : Nat → Nat) (M : List Nat) (pl : Nat) (pay mb : Nat → Nat) : List Nat :=
  [tag, H % 256, H / 256, 0, 0] ++ (List.range 32).map hp ++ M ++ (List.range pl).map pay ++ (List.range 8).map mb

/-- M5a-8: the head's two length bytes `lo = H − 256·hi` (field), `hi`, both bytes, spell `H`
(plain naturals; `Q` the field size). -/
theorem u32_split (Q H lo hi : Nat) (hQ : 1073741824 < Q) (hH : H < 134217728) (hlo : lo < 256)
    (hhi : hi < 256) (h : lo = (H + (Q - 256 % Q * hi % Q) % Q) % Q) : H = lo + 256 * hi := by
  rw [Nat.mod_eq_of_lt (show 256 < Q by omega), Nat.mod_eq_of_lt (show 256 * hi < Q by omega)] at h
  rcases Nat.eq_zero_or_pos hi with rfl | hp
  · rw [Nat.mul_zero, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (show Q - 256 * hi < Q by omega)] at h
    by_cases hc : H + (Q - 256 * hi) < Q
    · rw [Nat.mod_eq_of_lt hc] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega

theorem range_add_map (g : Nat → Nat) (a b : Nat) :
    (List.range (a + b)).map g = (List.range a).map g ++ (List.range b).map fun j => g (a + j) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- **A list indexed by offset is `serC`** (pure). -/
theorem serC_eq (g : Nat → Nat) (tag H pl : Nat) (hp pay mb : Nat → Nat) (hH : 32 ≤ H)
    (g0 : g 0 = tag) (g1 : g 1 = H % 256) (g2 : g 2 = H / 256) (gz : ∀ k, 3 ≤ k → k < 5 → g k = 0)
    (ghp : ∀ m, m < 32 → g (5 + m) = hp m) (gpay : ∀ t, t < pl → g (5 + H + t) = pay t)
    (gmb : ∀ b, b < 8 → g (5 + H + pl + b) = mb b) :
    (List.range (5 + H + pl + 8)).map g =
      serC tag H hp ((List.range (H - 32)).map fun i => g (37 + i)) pl pay mb := by
  have e : 5 + H + pl + 8 = (((5 + 32) + (H - 32)) + pl) + 8 := by omega
  rw [e, range_add_map, range_add_map, range_add_map, range_add_map]
  unfold serC
  have h5 : (List.range 5).map g = [tag, H % 256, H / 256, 0, 0] := by
    rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.map_cons, List.map_nil, g0, g1, g2, gz 3 (by omega) (by omega),
      gz 4 (by omega) (by omega)]
  rw [h5]
  have a1 : ((List.range 32).map fun j => g (5 + j)) = (List.range 32).map hp := by
    apply List.map_congr_left; intro m hm; exact ghp m (List.mem_range.1 hm)
  have a2 : ((List.range (H - 32)).map fun j => g (5 + 32 + j)) = (List.range (H - 32)).map fun i => g (37 + i) := by
    apply List.map_congr_left; intro i _; rfl
  have a3 : ((List.range pl).map fun j => g (5 + 32 + (H - 32) + j)) = (List.range pl).map pay := by
    apply List.map_congr_left; intro t ht
    rw [show 5 + 32 + (H - 32) + t = 5 + H + t by omega]; exact gpay t (List.mem_range.1 ht)
  have a4 : ((List.range 8).map fun j => g (5 + 32 + (H - 32) + pl + j)) = (List.range 8).map mb := by
    apply List.map_congr_left; intro b hb
    rw [show 5 + 32 + (H - 32) + pl + b = 5 + H + pl + b by omega]; exact gmb b (List.mem_range.1 hb)
  rw [a1, a2, a3, a4]

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 4000000 in
/-- **The message of a hashing continued head.** -/
theorem cont_node (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
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
    ∃ M : List Nat, M.length = ev tr 3 r pub (Sn.c "hplen") - 32 ∧ (∀ v ∈ M, v < 256) ∧
      32 ≤ ev tr 3 r pub (Sn.c "hplen") ∧ ev tr 3 r pub (Sn.c "hplen") < 65536 ∧
      (∀ k, k < 5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + 8 →
        (k < 37 ∨ 5 + ev tr 3 r pub (Sn.c "hplen") ≤ k) →
        headF tr pub r (ev tr 3 r pub (Sn.c "hplen")) x mb k < 256) ∧
      bytesOf ((pack2 hb).map (nE tr pub r)) =
        sha256 ((serC (ev tr 3 r pub (sm 3 (Sn.c "isE"))) (ev tr 3 r pub (Sn.c "hplen"))
          (fun m => ev tr 3 r pub (Sn.c "hp" m)) M (payLen tr pub r) (fun t => ev tr 3 r pub (x t))
          (fun b => ev tr 3 r pub (mb b))).map UInt8.ofNat) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  obtain ⟨hSL, hHb⟩ := ev_serLenC hH hxK hxR hr hA hcont
  have hH32 : 32 ≤ ev tr 3 r pub (Sn.c "hplen") := by
    rw [cont_hplen hH hxK hxR hr hA hcont]; omega
  have hpL := payLen_eq (tr := tr) (pub := pub) (r := r)
  generalize hHd : ev tr 3 r pub (Sn.c "hplen") = H at hSL hHb hH32 ⊢
  generalize hId : ev tr 3 r pub (Sn.c "isL") = I at hSL hL hpL
  generalize hPL : payLen tr pub r = PL at hpL ⊢
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
  -- every received offset is below `serLen`; outside `[37, 5 + H)` it carries `headF`
  have hpos : ∀ k, k < mm.length → k % P < 45 + H + 4 * I ∧
      ((k % P < 37 ∨ 5 + H ≤ k % P) → (mm[k]!).toNat = headF tr pub r H x mb (k % P)) := by
    intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    obtain ⟨hmem, hbq, hsq, hmult⟩ := sha_rcv q hq
    have hmb := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 0) (by rw [fullAir_len]; omega)
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact hmem) hr' hmult (by exact hf)
    rw [hmq, hbq, hsq] at hmb
    rcases cont_byte hH hxB hxK hr hpar hcid hmb with ⟨j, hj, hjb, hjs, hjh, hjp, hjm⟩ | hS
    · rw [hidE] at hjh
      obtain ⟨pe, ve, hpe, hlt, hout, hval⟩ :=
        cont_ser_val hc hA hcont hHd hH32 (by omega) hg (hsb j hj hjb hjs hjh) hjp
      rw [Interaction.msgVal, hpe] at hjm
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hjm
      obtain ⟨-, e1, e2⟩ := hjm
      have ek : k % P = ev tr 3 r pub pe := by
        have := congrArg Fp.toNat e1; rw [ofNat_toNat'] at this; exact this
      have ev2 : (mm[k]!).toNat = ev tr 3 r pub ve := by
        have := congrArg Fp.toNat e2.1
        rw [ofNat_toNat', Nat.mod_eq_of_lt (by have := UInt8.toNat_lt (mm[k]!); omega)] at this
        exact this
      rw [hId] at hlt
      refine ⟨by rw [ek]; exact hlt, fun _ => ?_⟩
      rw [ek, ev2, hval]
    · have h1 := cont_snc_lt hH hxK hxR hxRr hr hA hcont hS
      obtain ⟨s, hs, m, hm, -, -, -, c1, -, hx, -⟩ := hS
      rw [ofNat_toNat', hHd] at h1
      rw [ofNat_toNat'] at hx
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
  have hval : ∀ k, k < 45 + H + 4 * I → (k < 37 ∨ 5 + H ≤ k) →
      (mm[k]!).toNat = headF tr pub r H x mb k := by
    intro k hk ho
    have := (hpos k (by omega)).2 (by rw [Nat.mod_eq_of_lt (by omega)]; exact ho)
    rwa [Nat.mod_eq_of_lt (show k < P by omega)] at this
  -- the `u32` length bytes (M5a-8): `lo = H − 256·hi`, `hi`, both bytes, so `H = lo + 256·hi`
  have hlo := hval 1 (by omega) (by omega)
  have hhi := hval 2 (by omega) (by omega)
  rw [headF_1, FieldRows.ev_sub, ev3_sm, hHd] at hlo
  rw [headF_2] at hhi
  rw [← hhi] at hlo
  have hsplit := u32_split P H _ _ (by decide) (by omega) (UInt8.toNat_lt (mm[1]!)) (UInt8.toNat_lt (mm[2]!)) hlo
  have hg1 : (mm[1]!).toNat = H % 256 := by have := UInt8.toNat_lt (mm[1]!); omega
  have hg2 : (mm[2]!).toNat = H / 256 := by have := UInt8.toNat_lt (mm[1]!); omega
  have hH16 : H < 65536 := by have := UInt8.toNat_lt (mm[1]!); have := UInt8.toNat_lt (mm[2]!); omega
  -- the message as `serC`
  have hL5 : 5 + H + PL + 8 = 45 + H + 4 * I := by omega
  have hmm : mm.map UInt8.toNat = (List.range (5 + H + PL + 8)).map fun k => (mm[k]!).toNat := by
    apply List.ext_getElem?
    intro k
    rcases Nat.lt_or_ge k mm.length with h | h
    · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega), List.getElem?_eq_getElem h]
      simp [getElem!_def, List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  rw [serC_eq (fun k => (mm[k]!).toNat) _ H PL _ _ _ hH32 (hval 0 (by omega) (by omega))
    hg1 hg2 (fun k h1 h2 => by rw [hval k (by omega) (by omega), headF_z h1 h2])
    (fun m hm => by rw [hval _ (by omega) (by omega), headF_hp hm])
    (fun t ht => by rw [hval _ (by omega) (by omega), headF_x hH32 (by omega)])
    (fun b hb => by rw [hval _ (by omega) (by omega), ← hPL, headF_mb hH32])] at hmm
  refine ⟨(List.range (H - 32)).map fun i => (mm[37 + i]!).toNat, by simp, ?_, hH32, ?_, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨i, -, rfl⟩ := hv
    exact UInt8.toNat_lt _
  · exact hH16
  · intro k hk ho
    rw [← hPL] at hk
    rw [← hval k (by omega) ho]; exact UInt8.toNat_lt _
  · have hid8 : ∀ l : List UInt8, (l.map UInt8.toNat).map UInt8.ofNat = l := fun l => by
      induction l with
      | nil => rfl
      | cons u l ih => simp only [List.map_cons, UInt8.ofNat_toNat, ih]
    have hm' := congrArg (List.map UInt8.ofNat) hmm
    rw [hid8] at hm'
    rw [← headF_0 (H := H) (x := x) (mb := mb), ← hm', show sha256 mm = dg from hdg.symm]
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

end StateM5a.SnContRec2
