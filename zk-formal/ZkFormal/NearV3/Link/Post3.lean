import ZkFormal.NearV3.Link.PerTau3
import ZkFormal.NearV3.Link.Post3Spec

/-!
# ZkFormal.NearV3.Link.Post3 — the post-root of each instance (M6c)

Node records carry their post bytes `ser true` in lockstep with `ser false`: revealed kid
post windows are `DIGEST (NPOST c, clen, post)`, written value slots
`DIGEST (VPOST vid, vlen, post)`, unwritten value slots have `post = pre` (`NSlot3.wf`), and
the head looks up `DIGEST (NPOST rid, rlen, h.post)`.  The post bytes of a record are hashed
through its `BYTES` `NPOST(n)` sends; the `VPOST(vid)` bytes come from another table
(`others`), parametrised by `pv : Nat → Bytes` (`VPostOk`).

* `postV` — the post view of a record (post windows in the pre position):
  `(postV v).ser false = v.ser true`, `(postV v).toRec3 f = v.toRec3 f`; `ser_length_post3`;
* `npost_sha`, `kid_post_sha`, `head_post_sha` — post windows are `sha256` of post bytes;
* `vpost_len` — a written slot's `vlen` is at most `|pv vid|` (from the `DIGEST` length:
  every hashed byte is a `VPOST` send); the converse `|pv vid| ≤ vlen` is a hypothesis
  (`hpl`), see below;
* `val_post_sha` — the post window of every revealed value slot is `sha256` of the post value
  (`valsPost`: written value records replaced by `pv vid`);
* **`post_tau`** — `digest R (valsPost vs es pv) h.rid = toB h.post` for every head.

`|pv vid| ≤ vlen` is not derivable from the `DIGEST` lookup: `ShaFacts.digest` only says the
hashed bytes were received on `BYTES`, so SHA may hash a proper prefix of the `VPOST` sends.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

/-! ## The post view of a record -/

def postSlot : NSlot3 → NSlot3
  | .ref lb h => .ref lb h
  | .val lb i l _ po w => .val lb i l po po w

def postKid : NKid → NKid
  | .node c l r _ po => .node c l r po po
  | k => k

def postV : NodeV3 → NodeV3
  | .leaf k s m => .leaf k (postSlot s) m
  | .ext k kid m => .ext k (postKid kid) m
  | .branch sv kids m => .branch (sv.map postSlot) (kids.map postKid) m

theorem postSlot_bytes (s : NSlot3) : (postSlot s).bytes false = s.bytes true := by
  cases s <;> rfl

theorem postKid_bytes (k : NKid) : (postKid k).bytes false = k.bytes true := by
  cases k <;> rfl

theorem postKid_toKid3 (k : NKid) : (postKid k).toKid3 = k.toKid3 := by
  cases k <;> rfl

theorem postSlot_toV3 (f : Nat → Nat) (s : NSlot3) : (postSlot s).toV3 f = s.toV3 f := by
  cases s <;> rfl

theorem kids_map_toKid3 (kids : List NKid) : (kids.map postKid).map NKid.toKid3 = kids.map NKid.toKid3 := by
  induction kids with
  | nil => rfl
  | cons k r ih => simp only [List.map_cons, postKid_toKid3, ih]

theorem kidBitmap_post (kids : List NKid) : kidBitmap (kids.map postKid) = kidBitmap kids := by
  rw [kidBitmap_eq3 (fun _ => .hash []), kidBitmap_eq3 (fun _ => .hash []) kids, kids_map_toKid3]

theorem flatMap_post : ∀ (kids : List NKid),
    (kids.map postKid).flatMap (NKid.bytes false) = kids.flatMap (NKid.bytes true)
  | [] => rfl
  | k :: r => by simp only [List.map_cons, List.flatMap_cons, postKid_bytes, flatMap_post r]

theorem ser_post (v : NodeV3) : (postV v).ser false = v.ser true := by
  cases v with
  | leaf k s m => simp only [postV, NodeV3.ser, postSlot_bytes]
  | ext k kid m => simp only [postV, NodeV3.ser, postKid_bytes]
  | branch sv kids m =>
    cases sv with
    | none => simp only [postV, NodeV3.ser, Option.map_none, kidBitmap_post, flatMap_post]
    | some s => simp only [postV, NodeV3.ser, Option.map_some, postSlot_bytes, kidBitmap_post, flatMap_post]

theorem toRec3_post (f : Nat → Nat) (v : NodeV3) : (postV v).toRec3 f = v.toRec3 f := by
  cases v with
  | leaf k s m => simp only [postV, NodeV3.toRec3, postSlot_toV3]
  | ext k kid m => simp only [postV, NodeV3.toRec3, postKid_toKid3]
  | branch sv kids m =>
    cases sv with
    | none => simp only [postV, NodeV3.toRec3, Option.map_none, kids_map_toKid3]
    | some s => simp only [postV, NodeV3.toRec3, Option.map_some, postSlot_toV3, kids_map_toKid3]

theorem postSlot_wf {s : NSlot3} (h : s.wf) : (postSlot s).wf := by
  cases s with
  | ref => exact h
  | val lb i l pre po w =>
    obtain ⟨h4, -, hpo, -, h3, hle⟩ := h
    exact ⟨h4, hpo, hpo, fun _ => rfl, h3, hle⟩

theorem postKid_wf {k : NKid} (h : k.wf) : (postKid k).wf := by
  cases k with
  | none => exact h
  | hash => exact h
  | node c l r pre po => exact ⟨h.2, h.2⟩

theorem postV_wf {v : NodeV3} (h : v.wf) : (postV v).wf := by
  cases v with
  | leaf k s m => obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, postSlot_wf h2, h3⟩
  | ext k kid m =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, ?_, postKid_wf h3, h4⟩
    cases kid <;> simp_all [postKid]
  | branch sv kids m =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨by simp [h1], ?_, ?_, h4⟩
    · intro s hs
      cases sv with
      | none => simp at hs
      | some s' => simp at hs; subst hs; exact postSlot_wf (h2 s' rfl)
    · intro kd hkd
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hkd
      exact postKid_wf (h3 k hk)

theorem postSlot_raw {s : NSlot3} {x : Nat} (h : x ∈ (postSlot s).raw) : x ∈ s.raw := by
  cases s with
  | ref => exact h
  | val lb i l pre po w =>
    simp only [postSlot, NSlot3.raw, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inr h

theorem postKid_raw {k : NKid} {x : Nat} (h : x ∈ (postKid k).raw) : x ∈ k.raw := by
  cases k with
  | none => exact h
  | hash => exact h
  | node c l r pre po =>
    simp only [postKid, NKid.raw, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inr h

theorem postV_raw {v : NodeV3} {x : Nat} (h : x ∈ (postV v).raw) : x ∈ v.raw := by
  cases v with
  | leaf k s m =>
    simp only [postV, NodeV3.raw, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (postSlot_raw h))
    · exact Or.inr h
  | ext k kid m =>
    simp only [postV, NodeV3.raw, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (postKid_raw h))
    · exact Or.inr h
  | branch sv kids m =>
    simp only [postV, NodeV3.raw, List.mem_append, List.mem_flatMap, List.mem_map] at h ⊢
    rcases h with (h | ⟨kd, ⟨k, hk, rfl⟩, hx⟩) | h
    · left; left
      cases sv with
      | none => simp at h
      | some s => simp only [Option.map_some, Option.getD_some] at h ⊢; exact postSlot_raw h
    · left; right
      exact ⟨k, hk, postKid_raw hx⟩
    · right; exact h

theorem revealed_post {v : NodeV3} {c l r : Nat} {pre po : List Nat}
    (h : (c, l, r, pre, po) ∈ (postV v).revealed) : pre = po ∧ ∃ pre', (c, l, r, pre', po) ∈ v.revealed := by
  cases v with
  | leaf => simp [postV, NodeV3.revealed] at h
  | ext k kid m =>
    cases kid with
    | none => simp [postV, postKid, NodeV3.revealed] at h
    | hash => simp [postV, postKid, NodeV3.revealed] at h
    | node c' l' r' pre' po' =>
      simp [postV, postKid, NodeV3.revealed] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, pre', by simp [NodeV3.revealed]⟩
  | branch sv kids m =>
    simp only [postV, NodeV3.revealed, List.mem_filterMap, List.mem_map] at h
    obtain ⟨kd, ⟨k, hk, rfl⟩, he⟩ := h
    cases k with
    | none => simp [postKid] at he
    | hash => simp [postKid] at he
    | node c' l' r' pre' po' =>
      simp [postKid] at he; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      exact ⟨rfl, pre', by simp only [NodeV3.revealed, List.mem_filterMap]; exact ⟨_, hk, rfl⟩⟩

theorem value_post {v : NodeV3} {i l : Nat} {pre po : List Nat} {w : Bool}
    (h : (postV v).value = some (i, l, pre, po, w)) : pre = po ∧ ∃ pre', v.value = some (i, l, pre', po, w) := by
  cases v with
  | leaf k s m =>
    cases s with
    | ref => simp [postV, postSlot, NodeV3.value] at h
    | val lb i' l' pr p' w' =>
      simp [postV, postSlot, NodeV3.value] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, pr, rfl⟩
  | ext => simp [postV, NodeV3.value] at h
  | branch sv kids m =>
    cases sv with
    | none => simp [postV, NodeV3.value] at h
    | some s =>
      cases s with
      | ref => simp [postV, postSlot, NodeV3.value] at h
      | val lb i' l' pr p' w' =>
        simp [postV, postSlot, NodeV3.value] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, pr, rfl⟩

/-! ## Post serialisation length and values -/

theorem kids_len_post : ∀ (kids : List NKid), (∀ kd ∈ kids, kd.wf) →
    (kids.flatMap (NKid.bytes true)).length = (kids.flatMap (NKid.bytes false)).length
  | [], _ => rfl
  | k :: r, h => by
    have ih := kids_len_post r (fun kd hk => h kd (by simp [hk]))
    have hk := h k (by simp)
    simp only [List.flatMap_cons, List.length_append, ih]
    cases k with
    | none => rfl
    | hash => rfl
    | node c l r pre po => simp [NKid.bytes, hk.1, hk.2]

theorem slot_len_post {s : NSlot3} (h : s.wf) : (s.bytes true).length = (s.bytes false).length := by
  cases s with
  | ref => rfl
  | val lb i l pre po w => obtain ⟨-, h1, h2, -⟩ := h; simp [NSlot3.bytes, h1, h2]

/-- **Pre and post serialisations have the same length.** -/
theorem ser_length_post3 {v : NodeV3} (hw : v.wf) : (v.ser true).length = (v.ser false).length := by
  cases v with
  | leaf k s m => simp [NodeV3.ser, slot_len_post hw.2.1]
  | ext k kid m =>
    obtain ⟨-, -, hk, -⟩ := hw
    cases kid with
    | none => rfl
    | hash => rfl
    | node c l r pre po => simp [NodeV3.ser, NKid.bytes, hk.1, hk.2]
  | branch sv kids m =>
    obtain ⟨-, hs, hk, -⟩ := hw
    cases sv with
    | none => simp [NodeV3.ser, kids_len_post kids hk]
    | some s => simp [NodeV3.ser, kids_len_post kids hk, slot_len_post (hs s rfl)]

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

theorem post_len_lt (hw : NodeWf3 vs) {n : Nat} (hn : n < vs.length) :
    (vs[n].v.ser true).length < 2 ^ 22 := by
  rw [ser_length_post3 (hw.wf _ (List.getElem_mem hn))]; exact ser_len_lt hw hn

theorem post_lt_P (hw : NodeWf3 vs) {n : Nat} (hn : n < vs.length) :
    ∀ x ∈ vs[n].v.ser true, x < ZkFormal.Algebra.P := by
  intro x hx
  have hl := post_len_lt hw hn
  have hwf := hw.wf _ (List.getElem_mem hn)
  rw [← ser_post] at hx hl
  rcases ser_vals3 _ (postV_wf hwf) x hx with h | h | h
  · exact hw.canon _ (List.getElem_mem hn) x (postV_raw h)
  · unfold ZkFormal.Algebra.P; omega
  · unfold ZkFormal.Algebra.P; omega

/-! ## `NPOST` sends and windows -/

/-- Sends whose id is `msgId K_NPOST n` are record `n`'s post bytes. -/
theorem npost_sends (hw : NodeWf3 vs) (hvw : ValWf es) {others : List Msg}
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_NPRE ∧ a % 16 ≠ K_NPOST ∧ a % 16 ≠ K_VPRE)
    {n : Nat} (hn : n < vs.length) :
    ∀ m ∈ nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_NPOST n) →
      ∃ j, j < (vs[n].v.ser true).length ∧ m = [msgId K_NPOST n, j, (vs[n].v.ser true).getD j 0] := by
  intro m hm a ha he
  have hid := nid_lt hw hn K_NPOST (by decide)
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
      unfold msgId K_NPOST K_NPRE at this; omega
    · obtain ⟨i, hi, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have := ofNat_eq (nid_lt hw hn' K_NPOST (by decide)) hid he
      unfold msgId at this; have : n' = n := by omega
      subst this; exact ⟨i, hi, by simp⟩
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
      unfold eidV msgId K_VPRE K_NPOST at this; omega
  · obtain ⟨h1, -, h3, -⟩ := hoth m hm a ha
    have := ofNat_eq h1 hid he
    unfold msgId K_NPOST at this; unfold K_NPOST at h3; omega

variable {others : List Msg} {shaS shaR : Nat → List Fp → Nat}

theorem npost_sha (hw : NodeWf3 vs) (hvw : ValWf es)
    (H : ShaHyp vs hs es others shaS shaR) {n : Nat} (hn : n < vs.length) {d : List Nat}
    (hd : ∀ x ∈ d, x < ZkFormal.Algebra.P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_NPOST n) (vs[n].v.ser true).length d).toFp) :
    Bytes8 (vs[n].v.ser true) ∧ d = (sha256 (toB (vs[n].v.ser true))).map UInt8.toNat :=
  Link.sha_core H.sha _ H.bytes (nid_lt hw hn K_NPOST (by decide)) (post_lt_P hw hn)
    (by have := post_len_lt hw hn; unfold ZkFormal.Algebra.P; omega) hd
    (npost_sends hw hvw H.othersId hn) hrecv

theorem kid_po_raw {v : NodeV3} {c l r : Nat} {pre po : List Nat} (hk : (c, l, r, pre, po) ∈ v.revealed) :
    ∀ x ∈ po, x ∈ v.raw := by
  intro x hx
  cases v with
  | leaf => simp [NodeV3.revealed] at hk
  | ext k kid m =>
    cases kid <;> simp [NodeV3.revealed] at hk
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk; simp [NodeV3.raw, NKid.raw, hx]
  | branch sv kids m =>
    simp only [NodeV3.revealed, List.mem_filterMap] at hk
    obtain ⟨kd, hkd, he⟩ := hk
    cases kd with
    | none => simp at he
    | hash _ => simp at he
    | node c' l' r' pre' po' =>
      simp at he; obtain ⟨-, -, -, -, h5⟩ := he; subst h5
      simp only [NodeV3.raw, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨_, hkd, by simp [NKid.raw, hx]⟩)

/-- **Revealed kid post windows.** -/
theorem kid_post_sha (hw : NodeWf3 vs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) {p : Nat} (hp : p < vs.length) {c l r : Nat} {pre po : List Nat}
    (hk : (c, l, r, pre, po) ∈ vs[p].v.revealed) :
    ∃ hc : c < vs.length, Bytes8 (vs[c].v.ser true) ∧
      po = (sha256 (toB (vs[c].v.ser true))).map UInt8.toNat := by
  obtain ⟨hc, -, -, hl, -⟩ := kid_link hw hb hp hk
  have hlen := ser_len_lt hw hc
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega),
    ← ser_length_post3 (hw.wf _ (List.getElem_mem hc))] at hl
  subst hl
  have hm : digMsg (msgId K_NPOST c) (vs[c].v.ser true).length po ∈
      nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
    apply List.mem_append_left
    unfold nodeRecvs3; rw [if_pos rfl, List.mem_flatMap]
    refine ⟨(vs[p], p), zip_range_mem vs hp, List.mem_append_left _ ?_⟩
    rw [List.mem_flatMap]
    exact ⟨(c, _, r, pre, po), hk, by simp⟩
  exact ⟨hc, npost_sha hw hvw H hc (fun x hx => hw.canon _ (List.getElem_mem hp) x (kid_po_raw hk x hx))
    (H.digest _ (cnt_pos3 hm))⟩

/-- **Head post windows.** -/
theorem head_post_sha (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) {h : HeadE} (hh : h ∈ hs) :
    ∃ hr : h.rid < vs.length, Bytes8 (vs[h.rid].v.ser true) ∧
      h.post = (sha256 (toB (vs[h.rid].v.ser true))).map UInt8.toNat := by
  obtain ⟨hr, -, -, hl, -⟩ := head_link hw hhw hb hh
  have hlen := ser_len_lt hw hr
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega),
    ← ser_length_post3 (hw.wf _ (List.getElem_mem hr))] at hl
  have hm : digMsg (msgId K_NPOST h.rid) h.rlen h.post ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
    apply List.mem_append_right
    unfold headRecvs; rw [if_pos rfl, List.mem_flatMap]
    exact ⟨h, hh, by simp⟩
  rw [← hl] at hm
  exact ⟨hr, npost_sha hw hvw H hr (fun x hx => (hhw.canon h hh).2.2.2.2.2.2 x hx) (H.digest _ (cnt_pos3 hm))⟩

/-- **Every record's post bytes are bytes.** -/
theorem rec_bytes_post (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (H : ShaHyp vs hs es others shaS shaR) : ∀ s ∈ vs, ∀ x ∈ s.v.ser true, x < 256 := by
  intro s hs' x hx
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hs'
  rcases sender_of hw hhw hb hn with ⟨h, hh, hr, -, -⟩ | ⟨p, hp, l, r, pre, po, hk, -, -⟩
  · obtain ⟨hr', hB, -⟩ := head_post_sha hw hhw hvw hb H hh
    subst hr; exact hB x hx
  · obtain ⟨hc, hB, -⟩ := kid_post_sha hw hvw hb H hp hk
    exact hB x hx

/-! ## `VPOST` -/

/-- The `VPOST(i)` bytes the other tables send are exactly the post value `pv i`. -/
structure VPostOk (others : List Msg) (pv : Nat → Bytes) : Prop where
  sends : ∀ i, i < 2 ^ 22 → ∀ m ∈ others, ∀ a, m.head? = some a →
    Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
    ∃ j, j < (pv i).length ∧ m = [msgId K_VPOST i, j, ((pv i).map UInt8.toNat).getD j 0]

/-- A value record is written: some revealed slot of it is written. -/
def wrote (vs : List NodeS3) (i : Nat) : Bool :=
  vs.any fun s => match s.v.value with
    | some (j, _, _, _, w) => j == i && w
    | none => false

/-- **The post value records**: written value records carry `pv vid`. -/
def valsPost (vs : List NodeS3) (es : List ValE) (pv : Nat → Bytes) : List ValRec3 :=
  es.map fun e => ⟨valTau vs e.vid, if wrote vs e.vid then pv e.vid else toB e.bytes⟩

theorem vpost_sends (hw : NodeWf3 vs) (hvw : ValWf es)
    {pv : Nat → Bytes} (HP : VPostOk others pv) {i : Nat} (hi : i < 2 ^ 22) :
    ∀ m ∈ nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
      ∃ j, j < ((pv i).map UInt8.toNat).length ∧
        m = [msgId K_VPOST i, j, ((pv i).map UInt8.toNat).getD j 0] := by
  intro m hm a ha he
  have hid : msgId K_VPOST i < ZkFormal.Algebra.P := by unfold msgId K_VPOST ZkFormal.Algebra.P; omega
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · rw [nodeBytesS, List.mem_flatMap] at hm
    obtain ⟨⟨s, n'⟩, hsn, hm⟩ := hm
    obtain ⟨hn', rfl⟩ := mem_zip_range hsn
    rw [List.mem_append] at hm
    rcases hm with hm | hm <;> obtain ⟨j, hj, rfl⟩ := mem_emitAt3.mp hm <;> simp at ha <;> subst ha
    · have := ofNat_eq (nid_lt hw hn' K_NPRE (by decide)) hid he
      unfold msgId K_VPOST K_NPRE at this; omega
    · have := ofNat_eq (nid_lt hw hn' K_NPOST (by decide)) hid he
      unfold msgId K_VPOST K_NPOST at this; omega
  · rw [valBytesS, List.mem_flatMap] at hm
    obtain ⟨e, he', hm⟩ := hm
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
    split at hm
    · simp at hm
    · obtain ⟨j, hj, rfl⟩ := mem_emitAt3.mp hm
      simp at ha; subst ha
      have hv := vid_small hvw ht
      have hvl := vlen_le hvw
      have hlt : eidV es[t] < ZkFormal.Algebra.P := by
        unfold eidV msgId K_VPRE ZkFormal.Algebra.P; rw [hv]; omega
      have := ofNat_eq hlt hid he
      unfold eidV msgId K_VPRE K_VPOST at this; omega
  · obtain ⟨j, hj, rfl⟩ := HP.sends i hi m hm a ha he
    exact ⟨j, by simpa using hj, rfl⟩

/-- The `DIGEST` length is at most the number of bytes sent for the id. -/
theorem sha_len_le (hsha : ShaFacts shaS shaR) (S : List Msg) (hbytes : ∀ m, shaR B_BYTES m = cnt S m)
    {id l : Nat} {enc d : List Nat} (hl : l < ZkFormal.Algebra.P) (hlen : enc.length < ZkFormal.Algebra.P)
    (hS : ∀ m ∈ S, ∀ a, m.head? = some a → Fp.ofNat a = Fp.ofNat id →
      ∃ j, j < enc.length ∧ m = [id, j, enc.getD j 0])
    (hrecv : 0 < shaS B_DIGEST (digMsg id l d).toFp) : l ≤ enc.length := by
  obtain ⟨id', bs, hm, hall⟩ := hsha.digest _ hrecv
  simp only [digMsg, Msg.toFp, List.map_cons, List.cons_append,
    List.nil_append, List.cons.injEq] at hm
  obtain ⟨hid', hlen', -⟩ := hm
  have hle : bs.length ≤ enc.length := by
    apply Classical.byContradiction; intro hlt
    have h1 := hall enc.length (by omega)
    rw [hbytes] at h1
    obtain ⟨m, hmS, hmE⟩ := Link.cnt_pos.mp h1
    cases m with
    | nil => simp [Msg.toFp] at hmE
    | cons a rest =>
      simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hmE
      obtain ⟨j, hj, hmj⟩ := hS _ hmS a rfl (by rw [hmE.1, hid'])
      simp only [List.cons.injEq] at hmj
      obtain ⟨-, rfl⟩ := hmj
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmE
      have := Link.ofNat_inj (by omega) hlen hmE.2.1; omega
  have := Link.ofNat_eq_iff.mp hlen'
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem value_po_raw {v : NodeV3} {i l : Nat} {pre po : List Nat} {w : Bool}
    (h : v.value = some (i, l, pre, po, w)) : ∀ x ∈ po, x ∈ v.raw := by
  intro x hx
  cases v with
  | leaf k s m =>
    cases s with
    | ref => simp [NodeV3.value] at h
    | val lb i' l' pr p' w' =>
      simp [NodeV3.value] at h; obtain ⟨-, -, -, rfl, -⟩ := h
      simp [NodeV3.raw, NSlot3.raw, hx]
  | ext => simp [NodeV3.value] at h
  | branch sv kids m =>
    cases sv with
    | none => simp [NodeV3.value] at h
    | some s =>
      cases s with
      | ref => simp [NodeV3.value] at h
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at h; obtain ⟨-, -, -, rfl, -⟩ := h
        simp [NodeV3.raw, NSlot3.raw, hx]

theorem value_wf {v : NodeV3} (hw : v.wf) {i l : Nat} {pre po : List Nat}
    (h : v.value = some (i, l, pre, po, false)) : po = pre := by
  cases v with
  | leaf k s m =>
    cases s with
    | ref => simp [NodeV3.value] at h
    | val lb i' l' pr p' w' =>
      simp [NodeV3.value] at h; obtain ⟨-, -, rfl, rfl, rfl⟩ := h
      exact hw.2.1.2.2.2.1 rfl
  | ext => simp [NodeV3.value] at h
  | branch sv kids m =>
    cases sv with
    | none => simp [NodeV3.value] at h
    | some s =>
      cases s with
      | ref => simp [NodeV3.value] at h
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at h; obtain ⟨-, -, rfl, rfl, rfl⟩ := h
        exact (hw.2.1 _ rfl).2.2.2.1 rfl

/-- Written-ness of a value record is that of its (unique) slot. -/
theorem wrote_eq (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es) {p : Nat} (hp : p < vs.length)
    {i l : Nat} {pre po : List Nat} {w : Bool} (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    wrote vs i = w := by
  cases w with
  | true =>
    unfold wrote; rw [List.any_eq_true]
    exact ⟨vs[p], List.getElem_mem hp, by simp [hv]⟩
  | false =>
    unfold wrote
    apply Classical.byContradiction; intro hne
    simp only [Bool.not_eq_false, List.any_eq_true] at hne
    obtain ⟨s, hs', hpred⟩ := hne
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hs'
    cases hvn : vs[n].v.value with
    | none => simp [hvn] at hpred
    | some x =>
      obtain ⟨j, l', pre', po', w'⟩ := x
      simp only [hvn, Bool.and_eq_true, beq_iff_eq] at hpred
      obtain ⟨rfl, rfl⟩ := hpred
      have := val_unique hw hvw hvb (vlen_le hvw) hn hp hvn hv
      subst this; rw [hv] at hvn; simp at hvn

theorem valOf_post (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es) (pv : Nat → Bytes)
    {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    valOf (valsPost vs es pv) (vpos (vid0 es) i) =
      if w then pv i else valOf (valsOf3 vs es) (vpos (vid0 es) i) := by
  obtain ⟨t, ht, hpos, hi, -, hV⟩ := val_pos hw hvw hvb (vlen_le hvw) hp hv
  rw [hpos, ← wrote_eq hw hvw hvb hp hv]
  have h1 : valOf (valsOf3 vs es) t = toB es[t].bytes := by simp [valOf, hV]
  rw [h1]; subst hi
  simp [valOf, valsPost, ht]

/-- **The length of a written post value**: `vlen ≤ |pv vid|` from the `DIGEST` lookup, and
`|pv vid| ≤ vlen` by hypothesis. -/
theorem vpost_len (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es)
    (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes} (HP : VPostOk others pv)
    {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat}
    (hv : vs[p].v.value = some (i, l, pre, po, true)) (hpl : (pv i).length ≤ l) :
    (pv i).length = l ∧ i < 2 ^ 22 ∧ 0 < shaS B_DIGEST (digMsg (msgId K_VPOST i) l po).toFp := by
  obtain ⟨t, ht, -, hi, -, -⟩ := val_pos hw hvw hvb (vlen_le hvw) hp hv
  have hit : i < 2 ^ 22 := by rw [← hi, vid_small hvw ht]; have := vlen_le hvw; omega
  have hlP : l < ZkFormal.Algebra.P := hw.canon _ (List.getElem_mem hp) l (value_raw hv).2
  have hm : digMsg (msgId K_VPOST i) l po ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
    apply List.mem_append_left
    unfold nodeRecvs3; rw [if_pos rfl, List.mem_flatMap]
    refine ⟨(vs[p], p), zip_range_mem vs hp, List.mem_append_right _ ?_⟩
    simp [hv]
  have hrecv := H.digest _ (cnt_pos3 hm)
  have hle := sha_len_le H.sha _ H.bytes (enc := (pv i).map UInt8.toNat) hlP
    (by simp; omega) (vpost_sends (others := others) hw hvw HP hit) hrecv
  simp only [List.length_map] at hle
  exact ⟨by omega, hit, hrecv⟩

/-- **Post windows of revealed value slots.** -/
theorem val_post_sha (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hvb : VParentBal vs es)
    (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes} (HP : VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    (valOf (valsPost vs es pv) (vpos (vid0 es) i)).length = l ∧
      po = (sha256 (valOf (valsPost vs es pv) (vpos (vid0 es) i))).map UInt8.toNat := by
  rw [valOf_post hw hvw hvb pv hp hv]
  cases w with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [value_wf (hw.wf _ (List.getElem_mem hp)) hv]
    exact val_sha hw hhw hvw hvb H hp hv
  | true =>
    simp only [if_true]
    obtain ⟨hlen, hit, hrecv⟩ := vpost_len hw hvw hvb H HP hp hv (hpl p hp i l pre po hv)
    refine ⟨hlen, ?_⟩
    have hlP : l < ZkFormal.Algebra.P := hw.canon _ (List.getElem_mem hp) l (value_raw hv).2
    rw [← hlen, show (pv i).length = ((pv i).map UInt8.toNat).length by simp] at hrecv
    have hc := Link.sha_core H.sha _ H.bytes (enc := (pv i).map UInt8.toNat)
      (by unfold msgId K_VPOST ZkFormal.Algebra.P; omega)
      (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        have := UInt8.toNat_lt y; unfold ZkFormal.Algebra.P; omega)
      (by simp; omega)
      (fun x hx => hw.canon _ (List.getElem_mem hp) x (value_po_raw hv x hx))
      (vpost_sends (others := others) hw hvw HP hit) hrecv
    rw [hc.2]
    exact congrArg (fun b => (sha256 b).map UInt8.toNat) (toB_toNat (pv i))

/-! ## Unfolding with other value records -/

section Unfold
variable {ns : List NodeRec3} {V : List ValRec3} {τ root : Nat} {rk : Nat → Nat}

theorem treeOf3_fuel_any (hd : RootedDagR ns V τ root rk) (V' : List ValRec3) :
    ∀ f f' n, InInst ns τ n → mu ns τ rk n < f → mu ns τ rk n < f' →
      treeOf3 ns V' f n = treeOf3 ns V' f' n := by
  intro f
  induction f with
  | zero => intro f' n hn h0 _; omega
  | succ f ih =>
    intro f' n hn hf hf'
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    obtain ⟨nr, hnr, ht⟩ := hn
    simp only [treeOf3, hnr]
    apply nodeTree3_congrP
    intro c hc
    obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
    have := mu_child (ns := ns) hlt hcI
    exact ih f'' c hcI (by omega) (by omega)

/-- `fullTree_unfoldR` for any value records (the unfolding uses only the record DAG). -/
theorem fullTree_unfold_any (hd : RootedDagR ns V τ root rk) (V' : List ValRec3) {n : Nat} {nr : NodeRec3}
    (hnr : ns[n]? = some nr) (ht : nr.tau = τ) :
    fullTree ns V' n = nodeTree3 V' (fullTree ns V') nr.node := by
  have hn : InInst ns τ n := ⟨nr, hnr, ht⟩
  have hm := mu_lt_length (rk := rk) hn
  obtain ⟨f, hf⟩ : ∃ f, ns.length = f + 1 := ⟨ns.length - 1, by omega⟩
  have h1 : fullTree ns V' n = treeOf3 ns V' (f + 1) n := by unfold fullTree; rw [hf]
  rw [h1]
  simp only [treeOf3, hnr]
  apply nodeTree3_congrP
  intro c hc
  obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
  have := mu_child (ns := ns) hlt hcI
  exact treeOf3_fuel_any hd V' f ns.length c hcI (by omega) (mu_lt_length hcI)

end Unfold

/-- **Along the DAG of an instance**: post bytes are the preimages of the post subtries. -/
theorem enc_fullTree_post {V V' : List ValRec3} {f : Nat → Nat} {τ root : Nat} {rk : Nat → Nat}
    (hd : RootedDagR (recsOf f vs) V τ root rk) (hw : NodeWf3 vs)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser true, x < 256)
    (hk : ∀ p (hp : p < vs.length), ∀ c l r pre po, (c, l, r, pre, po) ∈ vs[p].v.revealed →
      ∃ hc : c < vs.length, po = (sha256 (toB (vs[c].v.ser true))).map UInt8.toNat)
    (hv : ∀ p (hp : p < vs.length), ∀ i l pre po w, vs[p].v.value = some (i, l, pre, po, w) →
      (valOf V' (f i)).length = l ∧ po = (sha256 (valOf V' (f i))).map UInt8.toNat) :
    ∀ n, InInst (recsOf f vs) τ n → ∃ hn : n < vs.length,
      nodeEnc (fullTree (recsOf f vs) V' n) = toB (vs[n].v.ser true) ∧
        isNode (fullTree (recsOf f vs) V' n) = true := by
  apply dag_inductionR hd
  intro n nr hnr ht ih
  have hn : n < vs.length := by have := lt_of_getElem? hnr; rwa [recsOf_length] at this
  have hnr' := hnr
  rw [recsOf_get _ _ hn] at hnr
  simp only [Option.some.injEq] at hnr; subst hnr
  refine ⟨hn, ?_⟩
  rw [fullTree_unfold_any hd V' hnr' ht]
  have hwf := hw.wf _ (List.getElem_mem hn)
  have e := enc_tree V' f (fullTree (recsOf f vs) V') (postV vs[n].v) (postV_wf hwf)
    (by rw [ser_post]; exact hbytes _ (List.getElem_mem hn))
    (fun c l r pre po hm => by
      obtain ⟨rfl, pre', hm'⟩ := revealed_post hm
      obtain ⟨hc, hpo⟩ := hk n hn c l r pre' pre hm'
      obtain ⟨_hc, he, hnode⟩ := ih c ((kids_toRec3 f _ c).mpr ⟨l, r, pre', pre, hm'⟩)
      rw [hashOf_eq_enc _ hnode, he, hpo, toB_toNat])
    (fun i l pre po w hval => by
      obtain ⟨rfl, pre', hval'⟩ := value_post hval
      obtain ⟨h1, h2⟩ := hv n hn i l pre' pre w hval'
      exact ⟨h1, by rw [h2, toB_toNat]⟩)
  rw [toRec3_post, ser_post] at e
  exact ⟨e, isNode_tree _ _ _⟩

/-- **Post-root of an instance.** With `R := recsOf (vpos (vid0 es)) vs` and the post value
records `valsPost vs es pv`, the head's post window is the digest of its root record. -/
theorem post_tau (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes}
    (HP : VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {h : HeadE} (hh : h ∈ hs) :
    digest (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid = toB h.post := by
  have hbytes := rec_bytes hw hhw hvw hb H
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  obtain ⟨hr, -, hpost⟩ := head_post_sha hw hhw hvw hb H hh
  obtain ⟨_, henc, hnode⟩ := enc_fullTree_post hd hw (rec_bytes_post hw hhw hvw hb H)
    (fun p hp c l r pre po hk => by
      obtain ⟨hc, -, he⟩ := kid_post_sha hw hvw hb H hp hk; exact ⟨hc, he⟩)
    (fun p hp i l pre po w hv => val_post_sha hw hhw hvw hvb H HP hpl hp hv)
    h.rid hd.root_inst
  unfold digest
  rw [hashOf_eq_enc _ hnode, henc, hpost, toB_toNat]

end ZkFormal.NearV3.Link3
