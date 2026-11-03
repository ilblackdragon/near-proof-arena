import StateM5a.SnContKey3

/-!
# StateM5a.SnContKey4 — **the full key of a continued head is the walk key** (`ContKey`)

For an `SN` row with `cont = 1` hashing a node (old: `gsha`; new: `gfin`), **`cont_key`**: there is a
key `K` (the nibbles its hashed `hexPrefix` decodes to) such that

* the record over `K` is `Hashed` to the digest the row receives (so `OldOK` / `NewOK`);
* `K` has `klen = 62 + odd + rl` nibbles, all `< 16`, its first `62 + odd` are the head's cells `k_j`;
* with `gA = 0`, `K` is the walk key `K_kid[d .. d + klen)`; with `g2 = 1`, `K_kid2[d .. d + klen)`.

The head part is `SnContKey1.hpDec_head` (the AIR's `hp_m` pairing); the rest is the message's
`SNC` part `M` (`SnContKey2.cont_msg_snc`: `Sha256CR`) read nibble by nibble against the key the
chunks look up (`SnContKey3.snc_bytes_key`, `snc_look_A` / `snc_look_B`).
-/

namespace StateM5a.SnContKey4

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.KeyDecode StateM5a.SnContHead
open StateM5a.SnContChain StateM5a.SnContKey1 StateM5a.SnContKey2 StateM5a.SnContKey3 StateM5a.KeyLookups
open StateM5a.SnContRec1 StateM5a.SnContRec2 StateM5a.SnContRec3 StateM5a.SnContMem StateM5a.SnSer

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Pure: a key read off two parts -/

theorem two_parts {kk : List Nat} {base L : Nat} {k : Nat → Nat} {M : List Nat}
    (hhead : ∀ j, j < L → kk[base + j]? = some (k j))
    (hsnc : ∀ i, i < M.length → kk[base + L + 2 * i]? = some (M[i]! / 16) ∧
      kk[base + L + 2 * i + 1]? = some (M[i]! % 16)) :
    ∀ j, j < L + 2 * M.length → kk[base + j]? = ((List.range L).map k ++ M.flatMap nib)[j]? := by
  intro j hj
  by_cases h : j < L
  · rw [hhead j h, List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range h]; rfl
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    obtain ⟨i, e, he, hie⟩ : ∃ i e, e < 2 ∧ j - L = 2 * i + e := ⟨(j - L) / 2, (j - L) % 2, Nat.mod_lt _ (by decide), by omega⟩
    rw [hie, flat_get M i e he]
    have hi : i < M.length := by omega
    rw [List.getElem?_eq_getElem hi]
    obtain ⟨h0, h1⟩ := hsnc i hi
    have hM : M[i]! = M[i] := by rw [getElem!_def, List.getElem?_eq_getElem hi]
    rw [hM] at h0 h1
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · rw [show base + j = base + L + 2 * i by omega, h0]; rfl
    · rw [show base + j = base + L + 2 * i + 1 by omega, h1]; rfl

/-- **The full-key facts of a continued head's node key `K`.** -/
structure ContKey (tr : Trace Fp) (pub : List Fp) (r : Nat) (K : List Nat) : Prop where
  len : K.length = ev tr 3 r pub (Sn.c "klen")
  nib : nibblesOk K = true
  head : ∀ j, j < 62 + ev tr 3 r pub (Sn.c "odd") → K[j]? = some (ev tr 3 r pub (Sn.c "k" j))
  walk : ev tr 3 r pub (Sn.c "gA") = 0 → ∀ j, j < ev tr 3 r pub (Sn.c "klen") →
    (keyOf tr (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d") + j]? = K[j]?
  walk2 : ev tr 3 r pub (Sn.c "g2") = 1 → ∀ j, j < ev tr 3 r pub (Sn.c "klen") →
    (keyOf tr (ev tr 3 r pub (Sn.c "kid2")))[ev tr 3 r pub (Sn.c "d") + j]? = K[j]?

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem ev_dj {r : Nat} (j : Nat) (hj : j < 64) (hd : ev tr 3 r pub (Sn.c "d") < 2 ^ 21) :
    ev tr 3 r pub (Sn.c "d" + K j) = ev tr 3 r pub (Sn.c "d") + j := by
  rw [ev_hadd, show ev tr 3 r pub (K j) = j % P from ev_const j]
  generalize ev tr 3 r pub (Sn.c "d") = d at hd ⊢
  omega

set_option maxHeartbeats 8000000 in
/-- **The full key of a hashing continued head.** -/
theorem cont_key (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hCR : Walk.Sha256CR)
    {r par : Nat} (hr : r < tr.height 3) (hpar : par ≤ 1)
    {id g : Expr} {x mb hb : Nat → Expr} {xf : Expr}
    (hid : ev tr 3 r pub id = ID_SN + 2 * r + par)
    (hidE : (if par = 0 then Sn.idO else Sn.idN) = id)
    (hsd : rcv B_SHA_DIGEST g ([id, Sn.serLen] ++ (List.range 32).map hb) ∈ Sn.interactions)
    (hsb : ∀ i ∈ Sn.interactions, i.bus = B_SHA_BYTES → i.send = true → i.msg.head? = some id →
      i ∈ Sn.serBytes id g x mb)
    (hg : ev tr 3 r pub g = 1) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hx3 : ev tr 3 r pub (Sn.c "isL") = 1 → ev tr 3 r pub (x 3) = 0)
    (hxf : ev tr 3 r pub (Sn.c "isL") ≠ 1 → ev tr 3 r pub xf = 0) :
    ∃ K, ContKey tr pub r K ∧ Hashed (gRecK tr pub r K x xf mb) (bytesOf ((pack2 hb).map (nE tr pub r))) ∧
      (∀ t, t < payLen tr pub r → ev tr 3 r pub (x t) < 256) ∧ (∀ b, b < 8 → ev tr 3 r pub (mb b) < 256) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hk := SnHashed.sn_k16 hH hN hxr hr
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  obtain ⟨M, hML, hMb, hH32, hH256, hby, hdg⟩ := cont_node hH hxB hxD hxK hxR hxRr hr hpar hid hidE hsd hsb hg hA hcont
  obtain ⟨hl, hn, hR⟩ := grecK_hashed hc hA (hk 0 (by decide)) hML hMb hH32 hH256 hby hx3 hxf (xf := xf)
  have hSB : SncBytes tr pub r M := cont_msg_snc hH hxB hxD hxK hxR hCR hr hpar hid hidE hsd hsb hg hA hcont hML hMb hdg
  -- the decoded key, in two parts
  have hKeq : contKeyB tr pub r M =
      (List.range (62 + ev tr 3 r pub (Sn.c "odd"))).map (fun j => ev tr 3 r pub (Sn.c "k" j)) ++ M.flatMap nib := by
    unfold contKeyB
    rw [hpDec_split _ _ _ (by simp), hpDec_head (fun m => ev tr 3 r pub (Sn.c "hp" m)) (fun j => ev tr 3 r pub (Sn.c "k" j))
      _ (ev tr 3 r pub (Sn.c "isL")) ho hk (ev_hp0 hc (hk 0 (by decide))) (fun m h1 hm => ch_hp hc hk m h1 hm)]
  -- lengths
  obtain ⟨hrl2, hrlb⟩ := cont_rl hH hxK hxR hr hcont
  have hpl := cont_hplen hH hxK hxR hr hA hcont
  have hkl := ch_klen hc hcont (by omega)
  have hKL : ev tr 3 r pub (Sn.c "klen") = 62 + ev tr 3 r pub (Sn.c "odd") + 2 * M.length := by
    rw [hkl, hML, hpl]; omega
  have hpay : ∀ t, t < payLen tr pub r → ev tr 3 r pub (x t) < 256 := fun t ht => by
    have := hby (5 + ev tr 3 r pub (Sn.c "hplen") + t) (by omega) (by omega)
    rwa [SnContSer2.headF_x hH32 ht] at this
  have hmb : ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256 := fun b hb => by
    have := hby (5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + b) (by omega) (by omega)
    rwa [SnContSer2.headF_mb hH32] at this
  refine ⟨contKeyB tr pub r M, ⟨by rw [hl, hKL, hpl, hML]; omega, hn, ?_, ?_, ?_⟩, by rw [hdg]; exact hR, hpay, hmb⟩
  · intro j hj
    rw [hKeq, List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hj]; rfl
  · intro hA0 j hj
    -- the depth: the first nibble is looked up
    have hb0 : ev tr 3 r pub (Sn.b 0) = 1 := by
      rw [RowSnF.sn_b_eq_a hc hA0 0 (by decide), ch_a hc hcont 0]; rfl
    have hd := (sn_nib hH hN 0 (by decide) hr (ev_one_eval hb0)).2
    rw [ev_dj 0 (by decide) (by
      have := hd; rw [ev_hadd, show ev tr 3 r pub (K 0) = 0 % P from ev_const 0] at this
      have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "d"); omega)] at hd
    rw [Nat.add_zero] at hd
    rw [hKeq]
    refine two_parts (base := ev tr 3 r pub (Sn.c "d")) (fun j hj => ?_) (fun i hi => ?_) j (by omega)
    · have hj64 : j < 64 := by omega
      have hbj : ev tr 3 r pub (Sn.b j) = 1 := by
        rw [RowSnF.sn_b_eq_a hc hA0 j hj64, ch_a hc hcont j]; unfold af; (repeat' split) <;> omega
      have := (sn_nib hH hN j hj64 hr (ev_one_eval hbj)).1
      rw [ev_dj j hj64 hd, FieldRows2.sn_k_lt j hj64] at this
      exact this
    · have := snc_bytes_key hH hSB (snc_look_A hH hxK hN hr hA0 hd) i hi
      simpa [Nat.add_assoc] using this
  · intro hg2 j hj
    have ha0 : ev tr 3 r pub (Sn.a 0) = 1 := by rw [ch_a hc hcont 0]; rfl
    have hd := (sn_nib2 hH hN 0 (by decide) hr (ev_one_eval (by rw [ev_hmul, hg2, ha0]))).2
    rw [ev_dj 0 (by decide) (by
      have := hd; rw [ev_hadd, show ev tr 3 r pub (K 0) = 0 % P from ev_const 0] at this
      have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "d"); omega)] at hd
    rw [Nat.add_zero] at hd
    rw [hKeq]
    refine two_parts (base := ev tr 3 r pub (Sn.c "d")) (fun j hj => ?_) (fun i hi => ?_) j (by omega)
    · have hj64 : j < 64 := by omega
      have haj : ev tr 3 r pub (Sn.a j) = 1 := by rw [ch_a hc hcont j]; unfold af; (repeat' split) <;> omega
      have := (sn_nib2 hH hN j hj64 hr (ev_one_eval (by rw [ev_hmul, hg2, haj]))).1
      rw [ev_dj j hj64 hd, FieldRows2.sn_k_lt j hj64] at this
      exact this
    · have := snc_bytes_key hH hSB (snc_look_B hH hxK hN hr hg2 hd) i hi
      simpa [Nat.add_assoc] using this

end

end StateM5a.SnContKey4
