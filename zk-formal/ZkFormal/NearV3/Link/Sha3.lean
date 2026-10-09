import ZkFormal.NearV3.Link.Compose3
import ZkFormal.Near.Link.ShaCore

/-!
# ZkFormal.NearV3.Link.Sha3 — `DIGEST` lookups of the trie tables are `sha256` of record bytes

`ShaHyp`: the SHA contract (`ShaFacts`), the `BYTES` balance (node records, value records and
other tables, whose ids are of other kinds) and "every `DIGEST` the trie tables receive is
provided by SHA".  Then, by `sha_core` (v1):
* `rec_bytes` — every record's bytes are bytes (`< 256`);
* `kid_sha` — a revealed kid window is `sha256` of the kid record's bytes;
* `head_sha` — a head's pre-root window is `sha256` of its root record's bytes;
* `val_sha` — a revealed value window is `sha256` of the value record's bytes, whose length is
  the slot's `vlen`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

/-- Hypotheses of the SHA glue. -/
structure ShaHyp (vs : List NodeS3) (hs : List HeadE) (es : List ValE) (others : List Msg)
    (shaS shaR : Nat → List Fp → Nat) : Prop where
  sha : ShaFacts shaS shaR
  bytes : ∀ m, shaR B_BYTES m = cnt (nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others) m
  othersId : ∀ m ∈ others, ∀ a, m.head? = some a →
    a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_NPRE ∧ a % 16 ≠ K_NPOST ∧ a % 16 ≠ K_VPRE
  digest : ∀ m, 0 < cnt (nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST) m → 0 < shaS B_DIGEST m

theorem mem_emitAt3 {id off : Nat} {bs : List Nat} {m : Msg} :
    m ∈ emitAt id off bs ↔ ∃ i, i < bs.length ∧ m = [id, off + i, bs.getD i 0] := by
  simp only [emitAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem slot_bytes_raw {sl : NSlot3} {x : Nat} (h : x ∈ sl.bytes false) : x ∈ sl.raw := by
  cases sl with
  | ref lb hh => simpa [NSlot3.bytes, NSlot3.raw] using h
  | val lb i l pre po w =>
    simp only [NSlot3.bytes, NSlot3.raw, List.mem_append, if_false] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)

theorem kid_bytes_raw {kd : NKid} {x : Nat} (h : x ∈ kd.bytes false) : x ∈ kd.raw := by
  cases kd with
  | none => simp [NKid.bytes] at h
  | hash hh => simpa [NKid.bytes, NKid.raw] using h
  | node c l r pre po => simp_all [NKid.bytes, NKid.raw]

/-- Values of a serialization: raw values, short constants, or below the length. -/
theorem ser_vals3 (v : NodeV3) (hw : v.wf) :
    ∀ x ∈ v.ser false, x ∈ v.raw ∨ x < 65536 ∨ x ≤ (v.ser false).length := by
  intro x hx
  cases v with
  | leaf k s m =>
    have hl : (hpN k true).length ≤ ((NodeV3.leaf k s m).ser false).length := by simp [NodeV3.ser]; omega
    simp only [NodeV3.ser, List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h)
    · simp at h; omega
    · right; left
      have := u32Bytes_lt _ _ h
      omega
    · right; left; unfold hpN at h; obtain ⟨y, -, rfl⟩ := List.mem_map.mp h; have := UInt8.toNat_lt y; omega
    · left; simp [NodeV3.raw, slot_bytes_raw h]
    · left; simp [NodeV3.raw, h]
  | ext k kid m =>
    have hl : (hpN k false).length ≤ ((NodeV3.ext k kid m).ser false).length := by simp [NodeV3.ser]; omega
    simp only [NodeV3.ser, List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h)
    · simp at h; omega
    · right; left
      have := u32Bytes_lt _ _ h
      omega
    · right; left; unfold hpN at h; obtain ⟨y, -, rfl⟩ := List.mem_map.mp h; have := UInt8.toNat_lt y; omega
    · left; simp [NodeV3.raw, kid_bytes_raw h]
    · left; simp [NodeV3.raw, h]
  | branch sv kids m =>
    obtain ⟨hl, -, -, -⟩ := hw
    have hb := kidBitmap_lt3 hl
    simp only [NodeV3.ser, List.mem_append] at hx
    rcases hx with (((h | h) | h) | h)
    · cases sv with
      | none => simp at h; omega
      | some s =>
        simp only [List.mem_append] at h
        rcases h with h | h
        · simp at h; omega
        · left; simp [NodeV3.raw, slot_bytes_raw h]
    · simp at h; rcases h with rfl | rfl <;> omega
    · obtain ⟨kd, hkd, h⟩ := List.mem_flatMap.mp h
      left; simp only [NodeV3.raw, List.mem_append, List.mem_flatMap]; left; right
      exact ⟨kd, hkd, kid_bytes_raw h⟩
    · left; simp [NodeV3.raw, h]

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

theorem ser_len_lt (hw : NodeWf3 vs) {n : Nat} (hn : n < vs.length) :
    (vs[n].v.ser false).length < 2 ^ 22 := by
  have := le_sum_mem (l := vs.map fun s => (s.v.ser false).length) (List.mem_map.mpr ⟨_, List.getElem_mem hn, rfl⟩)
  have := hw.rows; omega

theorem ser_lt_P (hw : NodeWf3 vs) {n : Nat} (hn : n < vs.length) :
    ∀ x ∈ vs[n].v.ser false, x < ZkFormal.Algebra.P := by
  intro x hx
  have hl := ser_len_lt hw hn
  rcases ser_vals3 _ (hw.wf _ (List.getElem_mem hn)) x hx with h | h | h
  · exact hw.canon _ (List.getElem_mem hn) x h
  · unfold ZkFormal.Algebra.P; omega
  · unfold ZkFormal.Algebra.P; omega

theorem nid_lt {n : Nat} (hw : NodeWf3 vs) (hn : n < vs.length) (k : Nat) (hk : k < 16) :
    msgId k n < ZkFormal.Algebra.P := by
  have := hw.count; unfold msgId ZkFormal.Algebra.P; omega

theorem vid_small (hvw : ValWf es) {t : Nat} (ht : t < es.length) : es[t].vid = t := by
  have hlen := vlen_le hvw
  rw [vid_at hvw hlen t ht]
  have h0 : vid0 es = 0 := by
    unfold vid0; cases es with
    | nil => simp at ht
    | cons e r => have := hvw.first (by simp); simpa using this
  rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)]

theorem nodeBytesS (vs : List NodeS3) : nodeSends3 vs B_BYTES = (vs.zip (List.range vs.length)).flatMap
    fun (s, n) => emitAt (msgId K_NPRE n) 0 (s.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (s.v.ser true) := by
  simp [nodeSends3]

theorem valBytesS (es : List ValE) : valSends es B_BYTES =
    es.flatMap fun e => if e.vz then [] else emitAt (eidV e) 0 e.bytes := by
  simp [valSends]

/-- Sends whose id is `msgId K_NPRE n` are record `n`'s pre bytes. -/
theorem npre_sends (hw : NodeWf3 vs) (hvw : ValWf es) {others : List Msg}
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_NPRE ∧ a % 16 ≠ K_NPOST ∧ a % 16 ≠ K_VPRE)
    {n : Nat} (hn : n < vs.length) :
    ∀ m ∈ nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_NPRE n) →
      ∃ j, j < (vs[n].v.ser false).length ∧ m = [msgId K_NPRE n, j, (vs[n].v.ser false).getD j 0] := by
  intro m hm a ha he
  have hid := nid_lt hw hn K_NPRE (by decide)
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · rw [nodeBytesS, List.mem_flatMap] at hm
    obtain ⟨⟨s, n'⟩, hsn, hm⟩ := hm
    obtain ⟨hn', rfl⟩ := mem_zip_range hsn
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have := ofNat_eq (nid_lt hw hn' K_NPRE (by decide)) hid he
      unfold msgId at this; have : n' = n := by omega
      subst this; exact ⟨i, hi, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have := ofNat_eq (nid_lt hw hn' K_NPOST (by decide)) hid he
      unfold msgId K_NPOST K_NPRE at this; omega
  · rw [valBytesS, List.mem_flatMap] at hm
    obtain ⟨e, he', hm⟩ := hm
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
    split at hm
    · simp at hm
    · obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have hv := vid_small hvw ht
      have hvl := vlen_le hvw
      have hlt : eidV es[t] < ZkFormal.Algebra.P := by
        unfold eidV msgId K_VPRE ZkFormal.Algebra.P; rw [hv]; omega
      have := ofNat_eq hlt hid he
      unfold eidV msgId K_VPRE K_NPRE at this; omega
  · obtain ⟨h1, h2, -, -⟩ := hoth m hm a ha
    have := ofNat_eq h1 hid he
    unfold msgId K_NPRE at this; unfold K_NPRE at h2; omega

/-- **Record bytes and windows via `sha_core`.** -/
theorem npre_sha (hw : NodeWf3 vs) (hvw : ValWf es) {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (H : ShaHyp vs hs es others shaS shaR) {n : Nat} (hn : n < vs.length) {d : List Nat}
    (hd : ∀ x ∈ d, x < ZkFormal.Algebra.P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_NPRE n) (vs[n].v.ser false).length d).toFp) :
    Bytes8 (vs[n].v.ser false) ∧ d = (sha256 (toB (vs[n].v.ser false))).map UInt8.toNat :=
  Link.sha_core H.sha _ H.bytes (nid_lt hw hn K_NPRE (by decide)) (ser_lt_P hw hn)
    (by have := ser_len_lt hw hn; unfold ZkFormal.Algebra.P; omega) hd
    (npre_sends hw hvw H.othersId hn) hrecv

theorem cnt_pos3 {l : List Msg} {x : Msg} (h : x ∈ l) : 0 < cnt l x.toFp := Link.cnt_pos_of_mem h

theorem kid_dig_mem {p : Nat} (hp : p < vs.length) {c l r : Nat} {pre po : List Nat}
    (hk : (c, l, r, pre, po) ∈ vs[p].v.revealed) :
    digMsg (msgId K_NPRE c) l pre ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
  apply List.mem_append_left
  unfold nodeRecvs3; rw [if_pos rfl, List.mem_flatMap]
  refine ⟨(vs[p], p), zip_range_mem vs hp, List.mem_append_left _ ?_⟩
  rw [List.mem_flatMap]
  exact ⟨(c, l, r, pre, po), hk, by simp⟩

theorem head_dig_mem {h : HeadE} (hh : h ∈ hs) :
    digMsg (msgId K_NPRE h.rid) h.rlen h.pre ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
  apply List.mem_append_right
  unfold headRecvs; rw [if_pos rfl, List.mem_flatMap]
  exact ⟨h, hh, by simp⟩

variable {others : List Msg} {shaS shaR : Nat → List Fp → Nat}

/-- **Revealed kid windows.** -/
theorem kid_sha (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) {p : Nat} (hp : p < vs.length) {c l r : Nat} {pre po : List Nat}
    (hk : (c, l, r, pre, po) ∈ vs[p].v.revealed) :
    ∃ hc : c < vs.length, Bytes8 (vs[c].v.ser false) ∧ pre = (sha256 (toB (vs[c].v.ser false))).map UInt8.toNat := by
  obtain ⟨hc, -, -, hl, -⟩ := kid_link hw hb hp hk
  have hlen := ser_len_lt hw hc
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)] at hl
  subst hl
  have hd : ∀ x ∈ pre, x < ZkFormal.Algebra.P := by
    intro x hx; apply hw.canon _ (List.getElem_mem hp)
    cases hv : vs[p].v with
    | leaf => rw [hv] at hk; simp [NodeV3.revealed] at hk
    | ext k kid m =>
      rw [hv] at hk; cases kid <;> simp [NodeV3.revealed] at hk
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk; simp [NodeV3.raw, NKid.raw, hx]
    | branch sv kids m =>
      rw [hv] at hk
      simp only [NodeV3.revealed, List.mem_filterMap] at hk
      obtain ⟨kd, hkd, he⟩ := hk
      cases kd with
      | none => simp at he
      | hash _ => simp at he
      | node c' l' r' pre' po' =>
        simp at he; obtain ⟨-, -, -, h4, -⟩ := he; subst h4
        simp only [NodeV3.raw, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨_, hkd, by simp [NKid.raw, hx]⟩)
  exact ⟨hc, npre_sha hw hvw H hc hd (H.digest _ (cnt_pos3 (kid_dig_mem hp hk)))⟩

/-- **Head windows.** -/
theorem head_sha (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) {h : HeadE} (hh : h ∈ hs) :
    ∃ hr : h.rid < vs.length, Bytes8 (vs[h.rid].v.ser false) ∧
      h.pre = (sha256 (toB (vs[h.rid].v.ser false))).map UInt8.toNat := by
  obtain ⟨hr, -, -, hl, -⟩ := head_link hw hhw hb hh
  have hlen := ser_len_lt hw hr
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)] at hl
  have hm := head_dig_mem (vs := vs) hh
  rw [← hl] at hm
  exact ⟨hr, npre_sha hw hvw H hr (fun x hx => (hhw.canon h hh).2.2.2.2.2.1 x hx) (H.digest _ (cnt_pos3 hm))⟩

/-- **Every record's bytes are bytes.** -/
theorem rec_bytes (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256 := by
  intro s hs' x hx
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hs'
  rcases sender_of hw hhw hb hn with ⟨h, hh, hr, -, -⟩ | ⟨p, hp, l, r, pre, po, hk, -, -⟩
  · obtain ⟨hr', hB, -⟩ := head_sha hw hhw hvw hb H hh
    subst hr; exact hB x hx
  · obtain ⟨hc, hB, -⟩ := kid_sha hw hhw hvw hb H hp hk
    exact hB x hx

/-- Sends whose id is `VPRE(vid)` of value record `t` are its bytes. -/
theorem vpre_sends (hw : NodeWf3 vs) (hvw : ValWf es) {others : List Msg}
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_NPRE ∧ a % 16 ≠ K_NPOST ∧ a % 16 ≠ K_VPRE)
    {t : Nat} (ht : t < es.length) :
    ∀ m ∈ nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_VPRE t) →
      ∃ j, j < es[t].bytes.length ∧ m = [msgId K_VPRE t, j, es[t].bytes.getD j 0] := by
  intro m hm a ha he
  have hvl := vlen_le hvw
  have hid : msgId K_VPRE t < ZkFormal.Algebra.P := by unfold msgId K_VPRE ZkFormal.Algebra.P; omega
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · rw [nodeBytesS, List.mem_flatMap] at hm
    obtain ⟨⟨s, n'⟩, hsn, hm⟩ := hm
    obtain ⟨hn', rfl⟩ := mem_zip_range hsn
    rw [List.mem_append] at hm
    rcases hm with hm | hm <;> obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm <;> simp at ha <;> subst ha
    · have := ofNat_eq (nid_lt hw hn' K_NPRE (by decide)) hid he
      unfold msgId K_VPRE K_NPRE at this; omega
    · have := ofNat_eq (nid_lt hw hn' K_NPOST (by decide)) hid he
      unfold msgId K_VPRE K_NPOST at this; omega
  · rw [valBytesS, List.mem_flatMap] at hm
    obtain ⟨e, he', hm⟩ := hm
    obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem he'
    split at hm
    · simp at hm
    · obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have hv := vid_small hvw ht'
      have hlt : eidV es[t'] < ZkFormal.Algebra.P := by
        unfold eidV msgId K_VPRE ZkFormal.Algebra.P; rw [hv]; omega
      have := ofNat_eq hlt hid he
      unfold eidV msgId at this; rw [hv] at this
      have : t' = t := by omega
      subst this
      exact ⟨i, hi, by simp [eidV, hv]⟩
  · obtain ⟨h1, -, -, h4⟩ := hoth m hm a ha
    have := ofNat_eq h1 hid he
    unfold msgId K_VPRE at this; unfold K_VPRE at h4; omega

theorem val_dig_mem {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    digMsg (msgId K_VPRE i) l pre ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
  apply List.mem_append_left
  unfold nodeRecvs3; rw [if_pos rfl, List.mem_flatMap]
  refine ⟨(vs[p], p), zip_range_mem vs hp, List.mem_append_right _ ?_⟩
  simp [hv]

/-- **Revealed value windows.** -/
theorem val_sha (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hvb : VParentBal vs es)
    (H : ShaHyp vs hs es others shaS shaR) {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    (valOf (valsOf3 vs es) (vpos (vid0 es) i)).length = l ∧
      pre = (sha256 (valOf (valsOf3 vs es) (vpos (vid0 es) i))).map UInt8.toNat := by
  have hlen := vlen_le hvw
  obtain ⟨t, ht, hpos, hi, hl, hV⟩ := val_pos hw hvw hvb hlen hp hv
  have hvt := vid_small hvw ht
  rw [hpos]
  have hval : valOf (valsOf3 vs es) t = toB es[t].bytes := by simp [valOf, hV]
  have hbl : es[t].bytes.length = l := by
    have := hvw.shape _ (List.getElem_mem ht)
    cases hz : es[t].vz
    · rw [(this.2 hz).1, hl]
    · rw [(this.1 hz).2, ← hl, (this.1 hz).1]; rfl
  rw [hval, toB_len, hbl]
  refine ⟨rfl, ?_⟩
  have hm := val_dig_mem (hs := hs) hp hv
  rw [← hi, hvt, ← hbl] at hm
  have hd : ∀ x ∈ pre, x < ZkFormal.Algebra.P := by
    intro x hx; apply hw.canon _ (List.getElem_mem hp)
    cases hvv : vs[p].v with
    | leaf k sl m =>
      rw [hvv] at hv
      cases sl with
      | ref => simp [NodeV3.value] at hv
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at hv; obtain ⟨-, -, rfl, -⟩ := hv
        simp [NodeV3.raw, NSlot3.raw, hx]
    | ext => rw [hvv] at hv; simp [NodeV3.value] at hv
    | branch sv kids m =>
      rw [hvv] at hv
      cases sv with
      | none => simp [NodeV3.value] at hv
      | some sl =>
        cases sl with
        | ref => simp [NodeV3.value] at hv
        | val lb i' l' pr p' w' =>
          simp [NodeV3.value] at hv; obtain ⟨-, -, rfl, -⟩ := hv
          simp [NodeV3.raw, NSlot3.raw, hx]
  have hcore := Link.sha_core H.sha _ H.bytes (enc := es[t].bytes)
    (by unfold msgId K_VPRE ZkFormal.Algebra.P; omega)
    (fun x hx => (hvw.canon _ (List.getElem_mem ht)).2.2.2 x hx)
    (by
      have hsh := hvw.shape _ (List.getElem_mem ht)
      have hr := hvw.rows
      have hm := le_sum_mem (l := es.map fun e => if e.vz then 1 else e.len)
        (List.mem_map.mpr ⟨es[t], List.getElem_mem ht, rfl⟩)
      cases hz : es[t].vz
      · rw [(hsh.2 hz).1]; simp only [hz] at hm; simp at hm; unfold ZkFormal.Algebra.P; omega
      · rw [(hsh.1 hz).2]; simp; unfold ZkFormal.Algebra.P; omega)
    hd (vpre_sends hw hvw H.othersId ht) (H.digest _ (cnt_pos3 hm))
  exact hcore.2

end ZkFormal.NearV3.Link3
