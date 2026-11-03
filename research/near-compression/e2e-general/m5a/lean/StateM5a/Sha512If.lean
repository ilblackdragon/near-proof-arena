import StateM5a.Ws

/-!
# StateM5a.Sha512If — the native SHA-512 compression chip's interface `IF384`, as a contract

The prover (`../prover/src/main.rs`, `s384/air.rs`: SHA-512 compression AIR v4, the recursion
chip) attaches the native chip to the Lean bus `IF384` (`Dsl.B_IF384`; native bus 103).  For its
compression number `k` the chip's segment of 128 rows sends, once each, the 16 messages

  `(cid, m, limbs(w_{2m}), limbs(w_{2m+1}))`,  `m < 16`,  `cid = 128·k`,

over the 32 words `w = h ‖ block ‖ compress(h, block)` (`h` 8 words: pairs 0–3 from the A/E rows;
`block` 16 words: pairs 4–11 from the W rows; output 8 words: pairs 12–15 from the O rows), each
word as limbs `[0,21) [21,42) [42,64)` (`Ws.wlimbs`).  Its words come from 32 base-4 digits, so
they are `< 2^64`.  That the chip's AIR enforces exactly this traffic is its faithfulness
argument (`results/pq384-sha-air3`, `FAITHFUL-v4.md`); here it is the **named premise**
`Sha512IfContract compress chip`, with the compression function a parameter (`compress` of
`NearSpecV3.SHA512` has this shape; `CompressOK` is its output shape: 8 words `< 2^64`).

A consumer row (`Ws.comp`) receives the 16 messages of one `cid` over its 32 limb triples.  Then:

* `comp_sound`: under the contract and `IF384` balance (every received message is a chip message),
  a consumer's 32 triples are the limbs of `h ‖ block ‖ compress(h, block)` for some 64-bit words
  (the 16 messages of one `cid` come from one compression: the chip's `cid`s are distinct);
* `comp_iv`: with the SHA-384 IV in the first 8 words (`WSB`/`WSL` leaves), the 6 digest triples
  are `digest6 (compress IV384 block)` of the decoded block;
* `comp_node`: with the node block `l ‖ r ‖ pad` (`WSN`/`WSP`), the digest is
  `nodeH compress l r` of the decoded children — the Merkle node hash `H` of `Merkle.lean` /
  `WsBus.WspOK` on `Dig` (6 words `< 2^64`, i.e. a SHA-384 digest), whose no-collision property is
  the named hypothesis `NodeCR compress` (SHA-384 collision resistance on 96-byte inputs);
* `wsp_hashes`: a `WSP` row's two compressions give `oo = nodeH lo ro`, `on = nodeH ln rn` on the
  decoded digests (`WsBus.WspOK.hO` / `hN`); `enc_inj`: the decoding is unique.
-/

namespace StateM5a.Sha512If

/-- A decoded `IF384` message `(cid, pair, limbs(w_{2·pair}), limbs(w_{2·pair+1}))`. -/
structure IfMsg where
  cid : Nat
  pair : Nat
  a : List Nat
  b : List Nat
deriving DecidableEq

/-- One compression of the chip: its id and its inputs. -/
structure Comp where
  cid : Nat
  h : List Nat
  blk : List Nat

/-- All words are 64-bit. -/
def W64 (ws : List Nat) : Prop := ∀ w ∈ ws, w < 2 ^ 64

section
variable (compress : List Nat → List Nat → List Nat)

/-- The 32 interface words `h ‖ block ‖ compress(h, block)`. -/
def Comp.words (c : Comp) : List Nat := c.h ++ c.blk ++ compress c.h c.blk

/-- The chip's 16 interface sends of one compression. -/
def chipMsgs (c : Comp) : List IfMsg :=
  (List.range 16).map fun m =>
    ⟨c.cid, m, wlimbs ((c.words compress).getD (2 * m) 0), wlimbs ((c.words compress).getD (2 * m + 1) 0)⟩

/-- **The chip contract**: the chip's `IF384` sends are the 16 messages of each of its
compressions, with distinct ids and 64-bit input words. -/
def Sha512IfContract (chip : List IfMsg) : Prop :=
  ∃ comps : List Comp, chip = comps.flatMap (chipMsgs compress) ∧ (comps.map Comp.cid).Nodup ∧
    ∀ c ∈ comps, c.h.length = 8 ∧ c.blk.length = 16 ∧ W64 c.h ∧ W64 c.blk

/-- The compression's output shape (8 words `< 2^64`). -/
def CompressOK : Prop := ∀ h b, (compress h b).length = 8 ∧ W64 (compress h b)
end

/-- `Ws.zeroW` as a limb list. -/
def zeroL : List Nat := [0, 0, 0]

/-- A consumer's 16 receives over its 32 limb triples (`Ws.comp` at record level). -/
def compRecv (cid : Nat) (ws : List (List Nat)) : List IfMsg :=
  (List.range 16).map fun m => ⟨cid, m, ws.getD (2 * m) zeroL, ws.getD (2 * m + 1) zeroL⟩

/-! ## Limbs -/

theorem wlimbs_inj {x y : Nat} (h : wlimbs x = wlimbs y) : x = y := by
  simp only [wlimbs, List.cons.injEq, and_true] at h
  omega

theorem map_wlimbs_inj : ∀ {xs ys : List Nat}, xs.map wlimbs = ys.map wlimbs → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [wlimbs_inj h.1, map_wlimbs_inj h.2]

theorem wlimbs_zero : wlimbs 0 = zeroL := rfl

theorem nodup_key {β κ : Type} {f : β → κ} :
    ∀ {L : List β}, (L.map f).Nodup → ∀ {a b}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hn, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map.2 ⟨b, hb', rfl⟩) hn.1
    · exact absurd (e.symm ▸ List.mem_map.2 ⟨a, ha', rfl⟩) hn.1
    · exact nodup_key hn.2 ha' hb' e

/-! ## The interface -/

section
variable {compress : List Nat → List Nat → List Nat}

/-- **A consumer's compression is a chip compression.**  Under the contract and `IF384` balance,
the 32 limb triples a consumer receives under one `cid` are the limbs of
`h ‖ block ‖ compress(h, block)` for 64-bit `h` (8 words) and `block` (16 words). -/
theorem comp_sound (hc : CompressOK compress) {chip : List IfMsg}
    (hC : Sha512IfContract compress chip) {cid : Nat} {ws : List (List Nat)} (hlen : ws.length = 32)
    (hin : ∀ x ∈ compRecv cid ws, x ∈ chip) :
    ∃ h blk : List Nat, h.length = 8 ∧ blk.length = 16 ∧ W64 h ∧ W64 blk ∧
      ws = (h ++ blk ++ compress h blk).map wlimbs := by
  obtain ⟨comps, rfl, hnd, hshape⟩ := hC
  -- every received message comes from a compression with id `cid`
  have hfrom : ∀ m, m < 16 → ∃ c ∈ comps, c.cid = cid ∧
      ws.getD (2 * m) zeroL = wlimbs ((c.words compress).getD (2 * m) 0) ∧
      ws.getD (2 * m + 1) zeroL = wlimbs ((c.words compress).getD (2 * m + 1) 0) := by
    intro m hm
    have := hin _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)
    obtain ⟨c, hc, hx⟩ := List.mem_flatMap.1 this
    obtain ⟨m', -, e⟩ := List.mem_map.1 hx
    simp only [IfMsg.mk.injEq] at e
    obtain ⟨e1, rfl, e3, e4⟩ := e
    exact ⟨c, hc, e1, e3.symm, e4.symm⟩
  obtain ⟨c, hcm, hcid, -⟩ := hfrom 0 (by decide)
  have hall : ∀ k, k < 32 → ws.getD k zeroL = wlimbs ((c.words compress).getD k 0) := by
    intro k hk
    obtain ⟨c', hc', hcid', e0, e1⟩ := hfrom (k / 2) (by omega)
    have := nodup_key hnd hc' hcm (hcid'.trans hcid.symm)
    subst this
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have : k = 2 * (k / 2) := by omega
      rw [this]; exact e0
    · have : k = 2 * (k / 2) + 1 := by omega
      rw [this]; exact e1
  obtain ⟨h8, h16, wh, wb⟩ := hshape c hcm
  have hw : (c.words compress).length = 32 := by
    simp [Comp.words, h8, h16, (hc c.h c.blk).1]
  refine ⟨c.h, c.blk, h8, h16, wh, wb, List.ext_getElem? fun k => ?_⟩
  by_cases hk : k < 32
  · have := hall k hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    rw [List.getElem?_map]
    rw [List.getElem?_eq_getElem (by omega)] at this ⊢
    rw [List.getElem?_eq_getElem (by rw [hw]; omega)] at this
    rw [List.getElem?_eq_getElem (by simp only [Comp.words] at hw; rw [hw]; omega)]
    simp only [Option.getD_some, Option.map_some] at this ⊢
    rw [this]; rfl
  · have hw' : (c.h ++ c.blk ++ compress c.h c.blk).length = 32 := hw
    have a1 : ws[k]? = none := List.getElem?_eq_none (by omega)
    have a2 : ((c.h ++ c.blk ++ compress c.h c.blk).map wlimbs)[k]? = none :=
      List.getElem?_eq_none (by rw [List.length_map, hw']; omega)
    rw [a1, a2]

/-! ## SHA-384 digests and the node hash -/

/-- A SHA-384 digest: 6 words `< 2^64`. -/
abbrev Dig := {x : List Nat // x.length = 6 ∧ W64 x}

/-- The digest's 18 limbs (6 triples), as the tables store it (`Ws.digW`). -/
def enc (d : Dig) : List (List Nat) := d.1.map wlimbs

theorem enc_inj {a b : Dig} (h : enc a = enc b) : a = b :=
  Subtype.ext (map_wlimbs_inj h)

/-- The first 6 words of a compression output, as a digest. -/
def digest6 (x : List Nat) : Dig :=
  ⟨(List.range 6).map fun k => x.getD k 0 % 2 ^ 64, by simp, by
    intro w hw
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
    exact Nat.mod_lt _ (by decide)⟩

/-- SHA-384 padding words of a 96-byte message (`0x80`, zeros, length 768 bits). -/
def padW : List Nat := [2 ^ 63, 0, 0, 768]

variable (compress) in
/-- **The working-set node hash**: SHA-384 of `left48 ‖ right48`, one compression from IV384. -/
def nodeH (a b : Dig) : Dig := digest6 (compress IV384 (a.1 ++ b.1 ++ padW))

variable (compress) in
/-- **Named hypothesis**: the node hash has no collision on digests (SHA-384 collision resistance
on 96-byte inputs; `Merkle.batch_update_sound`'s `hinj` for `α = Dig`, `H = nodeH compress`). -/
def NodeCR : Prop := ∀ a b c d : Dig, nodeH compress a b = nodeH compress c d → a = c ∧ b = d

theorem digest6_eq {out o ox : List Nat} (h : out = o ++ ox) (ho : o.length = 6) (hw : W64 o) :
    (digest6 out).1 = o := by
  apply List.ext_getElem? ; intro k
  show ((List.range 6).map fun k => out.getD k 0 % 2 ^ 64)[k]? = o[k]?
  by_cases hk : k < 6
  · rw [List.getElem?_map, List.getElem?_range hk, Option.map_some]
    subst h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    rw [Nat.mod_eq_of_lt (hw _ (List.getElem_mem _))]
  · have a1 : ((List.range 6).map fun k => out.getD k 0 % 2 ^ 64)[k]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [a1]
    exact (List.getElem?_eq_none (by omega)).symm

theorem w64_append {a b : List Nat} : W64 (a ++ b) ↔ W64 a ∧ W64 b := by
  simp only [W64, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

/-- Split `(h ++ blk ++ out).map wlimbs` along a consumer's layout `iv ‖ B ‖ (o ‖ ox)`. -/
theorem split3 (hc : CompressOK compress) {h blk : List Nat} {B o ox : List (List Nat)}
    (h8 : h.length = 8) (h16 : blk.length = 16) (hB : B.length = 16)
    (e : (h ++ blk ++ compress h blk).map wlimbs = IV384.map wlimbs ++ B ++ (o ++ ox))
    (ho : o.length = 6) :
    h = IV384 ∧ blk.map wlimbs = B ∧ ∃ o' ox', compress h blk = o' ++ ox' ∧ o'.map wlimbs = o ∧
      o'.length = 6 ∧ W64 o' := by
  rw [List.map_append, List.map_append, List.append_assoc, List.append_assoc] at e
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [h8, IV384])
  obtain ⟨e3, e4⟩ := List.append_inj e2 (by simp [h16, hB])
  obtain ⟨o', ox', hsplit, ho', -⟩ := List.map_eq_append_iff.1 e4
  have hl : o'.length = 6 := by rw [← ho, ← ho', List.length_map]
  have hw : W64 o' := by
    have := (hc h blk).2; rw [hsplit] at this; exact (w64_append.1 this).1
  exact ⟨map_wlimbs_inj e1, e3, o', ox', hsplit, ho', hl, hw⟩

/-- **A leaf (IV) compression**: a consumer whose first 8 words are the SHA-384 IV receives, as
its 6 digest triples, the limbs of `digest6 (compress IV384 block)` of its (decoded) block. -/
theorem comp_iv (hc : CompressOK compress) {chip : List IfMsg}
    (hC : Sha512IfContract compress chip) {cid : Nat} {B o ox : List (List Nat)}
    (hB : B.length = 16) (ho : o.length = 6) (hox : ox.length = 2)
    (hin : ∀ x ∈ compRecv cid (IV384.map wlimbs ++ B ++ (o ++ ox)), x ∈ chip) :
    ∃ bw : List Nat, bw.length = 16 ∧ W64 bw ∧ B = bw.map wlimbs ∧
      o = enc (digest6 (compress IV384 bw)) := by
  obtain ⟨h, blk, h8, h16, -, wb, e⟩ := comp_sound hc hC (by simp [IV384, hB, ho, hox]) hin
  obtain ⟨rfl, eB, o', ox', hs, ho', hl, hw⟩ := split3 hc h8 h16 hB e.symm ho
  refine ⟨blk, h16, wb, eB.symm, ?_⟩
  rw [enc, digest6_eq hs hl hw, ho']

/-- **A node compression** (`WSN`, `WSP`): a consumer whose words are `IV384 ‖ l ‖ r ‖ pad ‖ o ‖ ox`
receives `o = enc (nodeH compress dl dr)` for the digests `dl`, `dr` that `l`, `r` encode. -/
theorem comp_node (hc : CompressOK compress) {chip : List IfMsg}
    (hC : Sha512IfContract compress chip) {cid : Nat} {l r o ox : List (List Nat)}
    (hl : l.length = 6) (hr : r.length = 6) (ho : o.length = 6) (hox : ox.length = 2)
    (hin : ∀ x ∈ compRecv cid (IV384.map wlimbs ++ (l ++ r ++ padW.map wlimbs) ++ (o ++ ox)), x ∈ chip) :
    ∃ dl dr : Dig, l = enc dl ∧ r = enc dr ∧ o = enc (nodeH compress dl dr) := by
  obtain ⟨bw, h16, wb, eB, eo⟩ := comp_iv hc hC (by simp [hl, hr, padW]) ho hox hin
  have eB' : bw.map wlimbs = l ++ (r ++ padW.map wlimbs) := by rw [← eB, List.append_assoc]
  obtain ⟨bl, brest, hsp, hbl, hbrest⟩ := List.map_eq_append_iff.1 eB'
  obtain ⟨br, bp, hsp2, hbr, hbp⟩ := List.map_eq_append_iff.1 hbrest
  rw [hsp2] at hsp
  subst hsp
  have hbp' : bp = padW := map_wlimbs_inj hbp
  subst hbp'
  have lbl : bl.length = 6 := by rw [← hl, ← hbl, List.length_map]
  have lbr : br.length = 6 := by rw [← hr, ← hbr, List.length_map]
  have wl : W64 bl := (w64_append.1 wb).1
  have wr : W64 br := (w64_append.1 (w64_append.1 wb).2).1
  refine ⟨⟨bl, lbl, wl⟩, ⟨br, lbr, wr⟩, hbl.symm, hbr.symm, ?_⟩
  rw [eo, nodeH, List.append_assoc]

/-- **A `WSP` row's two compressions** (`WsBus.WspOK.hO` / `hN` on `Dig` with `H = nodeH`): its
old and new children and digests decode to digests with `oo = nodeH lo ro`, `on = nodeH ln rn`
(the decoding is unique: `enc_inj`). -/
theorem wsp_hashes (hc : CompressOK compress) {chip : List IfMsg}
    (hC : Sha512IfContract compress chip) {cidO cidN : Nat} {lo ro oo oox ln rn on onx : List (List Nat)}
    (h1 : lo.length = 6) (h2 : ro.length = 6) (h3 : oo.length = 6) (h4 : oox.length = 2)
    (h5 : ln.length = 6) (h6 : rn.length = 6) (h7 : on.length = 6) (h8 : onx.length = 2)
    (hO : ∀ x ∈ compRecv cidO (IV384.map wlimbs ++ (lo ++ ro ++ padW.map wlimbs) ++ (oo ++ oox)), x ∈ chip)
    (hN : ∀ x ∈ compRecv cidN (IV384.map wlimbs ++ (ln ++ rn ++ padW.map wlimbs) ++ (on ++ onx)), x ∈ chip) :
    ∃ dlo dro dln drn : Dig, lo = enc dlo ∧ ro = enc dro ∧ ln = enc dln ∧ rn = enc drn ∧
      oo = enc (nodeH compress dlo dro) ∧ on = enc (nodeH compress dln drn) := by
  obtain ⟨a, b, ea, eb, eo⟩ := comp_node hc hC h1 h2 h3 h4 hO
  obtain ⟨c, d, ec, ed, en⟩ := comp_node hc hC h5 h6 h7 h8 hN
  exact ⟨a, b, c, d, ea, eb, ec, ed, eo, en⟩

/-- `IF384` balance gives the membership premise: the chip is the only sender. -/
theorem mem_of_balance {chip recvs : List IfMsg} (h : chip.Perm recvs) {x : IfMsg}
    (hx : x ∈ recvs) : x ∈ chip := h.mem_iff.2 hx

end

end StateM5a.Sha512If
