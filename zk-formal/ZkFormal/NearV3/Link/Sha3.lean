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
    · simp [u32r] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inr hl)
      · right; left; omega
    · right; left; unfold hpN at h; obtain ⟨y, -, rfl⟩ := List.mem_map.mp h; have := UInt8.toNat_lt y; omega
    · left; simp [NodeV3.raw, slot_bytes_raw h]
    · left; simp [NodeV3.raw, h]
  | ext k kid m =>
    have hl : (hpN k false).length ≤ ((NodeV3.ext k kid m).ser false).length := by simp [NodeV3.ser]; omega
    simp only [NodeV3.ser, List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h)
    · simp at h; omega
    · simp [u32r] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inr hl)
      · right; left; omega
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

end ZkFormal.NearV3.Link3
