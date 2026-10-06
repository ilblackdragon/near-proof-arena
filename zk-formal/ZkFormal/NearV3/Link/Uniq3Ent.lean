import ZkFormal.NearV3.Link.Sha3
import ZkFormal.NearV3.Link.Uniq3Core

/-!
# ZkFormal.NearV3.Link.Uniq3Ent — `DUP` + `ENT`: a duplicate `uniq` entry carries its predecessor's bytes

The message bytes of an entry id (`bN`): record `n`'s pre serialization for `NPRE(n)`, value
record `t`'s bytes for `VPRE(t)` (value ids are positions, `vid_small`), else `[]`.

Balances (as permutations of the `Fp` images, like `Walk3.BusBal`), each over the tables on
that bus:
* `DupBal`: `uniqV3` sends `DUP (eid, peid)` on equal entries; `nodeV3` / `valV3` duplicates
  receive `DUP (eid, repE)`;
* `EntBal`: entries with `hd` send `ENT (eid, len, pos, byte)` for their bytes, duplicates
  receive `ENT (repE, len, pos, byte)` for theirs (an empty value: the marker `(eid, 0, 0, 0)`).

`dup_bytes`: for an entry `t + 1` of `uniqV3` with `eq = 1`, `bN eid_{t+1} = bN eid_t`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

/-- Message bytes of entry id `E`. -/
def bN (vs : List NodeS3) (es : List ValE) (E : Nat) : List Nat :=
  if E % 16 = K_NPRE then ((vs[E / 16]?).map fun s => s.v.ser false).getD []
  else if E % 16 = K_VPRE then ((es[E / 16]?).map ValE.bytes).getD []
  else []

/-- Message bytes of entry id `E` (as `Bytes`): the `B` of `storeOf_hashFunctional3`. -/
def bOf (vs : List NodeS3) (es : List ValE) (E : Nat) : Bytes := toB (bN vs es E)

theorem bN_node (vs : List NodeS3) (es : List ValE) {n : Nat} (hn : n < vs.length) :
    bN vs es (msgId K_NPRE n) = vs[n].v.ser false := by
  have h1 : msgId K_NPRE n % 16 = K_NPRE := by unfold msgId K_NPRE; omega
  have h2 : msgId K_NPRE n / 16 = n := by unfold msgId K_NPRE; omega
  simp [bN, h1, h2, hn]

theorem bN_val (vs : List NodeS3) (es : List ValE) {t : Nat} (ht : t < es.length) :
    bN vs es (msgId K_VPRE t) = es[t].bytes := by
  have h1 : msgId K_VPRE t % 16 = K_VPRE := by unfold msgId K_VPRE; omega
  have h2 : msgId K_VPRE t / 16 = t := by unfold msgId K_VPRE; omega
  unfold bN
  rw [h1, h2, if_neg (by unfold K_VPRE K_NPRE; omega), if_pos rfl]
  simp [ht]

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

theorem val_bytes_lt (hvw : ValWf es) {t : Nat} (ht : t < es.length) : es[t].bytes.length < 2 ^ 22 := by
  have hsh := hvw.shape _ (List.getElem_mem ht)
  have hr := hvw.rows
  have hm := le_sum_mem (l := es.map fun e => if e.vz then 1 else e.len)
    (List.mem_map.mpr ⟨es[t], List.getElem_mem ht, rfl⟩)
  cases hz : es[t].vz
  · rw [(hsh.2 hz).1]; simp only [hz] at hm; simp at hm; omega
  · rw [(hsh.1 hz).2]; simp

theorem bN_ok (hw : NodeWf3 vs) (hvw : ValWf es) (E : Nat) :
    (∀ x ∈ bN vs es E, x < P) ∧ (bN vs es E).length < P := by
  unfold bN
  split
  · cases h : vs[E / 16]? with
    | none => simp; unfold P; omega
    | some s =>
      obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
      simp only [Option.map_some, Option.getD_some]
      exact ⟨ser_lt_P hw hn, by have := ser_len_lt hw hn; unfold P; omega⟩
  · split
    · cases h : es[E / 16]? with
      | none => simp; unfold P; omega
      | some e =>
        obtain ⟨ht, rfl⟩ := List.getElem?_eq_some_iff.1 h
        simp only [Option.map_some, Option.getD_some]
        exact ⟨(hvw.canon _ (List.getElem_mem ht)).2.2.2, by have := val_bytes_lt hvw ht; unfold P; omega⟩
    · simp; unfold P; omega

/-! ## `ENT` rows -/

theorem getD_get {l : List Nat} {p : Nat} (h : p < l.length) : l.getD p 0 = l[p] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The `ENT` rows of bytes `X` under id `E` (an empty `X`: the marker `(E, 0, 0, 0)`). -/
def entR (E : Nat) (X : List Nat) : List Msg :=
  if X = [] then [[E, 0, 0, 0]] else (List.range X.length).map fun p => [E, X.length, p, X.getD p 0]

theorem toFp4 (a b c d : Nat) : Msg.toFp [a, b, c, d] = [Fp.ofNat a, Fp.ofNat b, Fp.ofNat c, Fp.ofNat d] := rfl

/-- Rows determine the bytes. -/
theorem entR_inj {E E' : Nat} {X Y : List Nat} (hX : ∀ x ∈ X, x < P) (hXl : X.length < P)
    (hY : ∀ x ∈ Y, x < P) (hYl : Y.length < P)
    (h : ∀ m ∈ entR E X, m.toFp ∈ (entR E' Y).map Msg.toFp) : X = Y := by
  have hP : (0 : Nat) < P := by unfold P; omega
  by_cases hX0 : X = []
  · have := h [E, 0, 0, 0] (by simp [entR, hX0])
    by_cases hY0 : Y = []
    · rw [hX0, hY0]
    · simp only [entR, hY0, if_false, List.map_map, List.mem_map, List.mem_range, Function.comp_def,
        toFp4, List.cons.injEq, and_true] at this
      obtain ⟨q, hq, -, h2, -, -⟩ := this
      have := ofNat_eq hYl hP h2; subst hX0; exact absurd (List.length_eq_zero_iff.1 this) hY0
  · have hpos : 0 < X.length := List.length_pos_iff.2 hX0
    have hm : ∀ p, p < X.length → ∃ q, q < Y.length ∧ Y ≠ [] ∧ X.length = Y.length ∧ p = q ∧
        X.getD p 0 = Y.getD q 0 := by
      intro p hp
      have := h [E, X.length, p, X.getD p 0] (by simp only [entR, hX0, if_false, List.mem_map, List.mem_range]; exact ⟨p, hp, rfl⟩)
      by_cases hY0 : Y = []
      · simp only [entR, hY0, if_true, List.map_cons, List.map_nil, List.mem_singleton, toFp4,
          List.cons.injEq] at this
        have := ofNat_eq hP hXl this.2.1.symm; omega
      · simp only [entR, hY0, if_false, List.map_map, List.mem_map, List.mem_range, Function.comp_def,
          toFp4, List.cons.injEq, and_true] at this
        obtain ⟨q, hq, -, h2, h3, h4⟩ := this
        have hl := ofNat_eq hYl hXl h2
        have hpq := ofNat_eq (by omega) (by omega) h3
        subst hpq
        have hxp : X.getD q 0 < P := by
          rw [getD_get hp]; exact hX _ (List.getElem_mem hp)
        have hyq : Y.getD q 0 < P := by
          rw [getD_get hq]; exact hY _ (List.getElem_mem hq)
        exact ⟨q, hq, hY0, hl.symm, rfl, (ofNat_eq hyq hxp h4).symm⟩
    obtain ⟨-, -, -, hlen, -, -⟩ := hm 0 hpos
    apply List.ext_getElem hlen
    intro p h1 h2
    obtain ⟨q, -, -, -, rfl, he⟩ := hm p h1
    rwa [getD_get h1, getD_get h2] at he

theorem ser_ne_nil (v : NodeV3) : v.ser false ≠ [] := by
  cases v with
  | leaf => simp [NodeV3.ser]
  | ext => simp [NodeV3.ser]
  | branch sv kids m => cases sv <;> simp [NodeV3.ser]

theorem entS (vs : List NodeS3) (es : List ValE) :
    nodeSends3 vs B_ENT ++ valSends es B_ENT =
      (vs.zip (List.range vs.length)).flatMap (fun (s, n) => if s.hd then
        (List.range (s.v.ser false).length).map fun p => [eidN n, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
        else []) ++
      es.flatMap (fun e => if e.hd then e.entRows.map (eidV e :: ·) else []) := by
  simp [nodeSends3, valSends, B_ENT, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS]

theorem entRv (vs : List NodeS3) (es : List ValE) :
    nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT =
      (vs.zip (List.range vs.length)).flatMap (fun (s, _) => if s.dup then
        (List.range (s.v.ser false).length).map fun p => [s.repE, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
        else []) ++
      es.flatMap (fun e => if e.dup then e.entRows.map (e.repE :: ·) else []) := by
  simp [nodeRecvs3, valRecvs, B_ENT, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_VBYTES, B_VPARENT]

theorem entRows_eq (hvw : ValWf es) {e : ValE} (he : e ∈ es) (E : Nat) :
    e.entRows.map (E :: ·) = entR E e.bytes := by
  have hsh := hvw.shape e he
  unfold ValE.entRows entR
  cases hz : e.vz
  · obtain ⟨hl, hp⟩ := hsh.2 hz
    have : e.bytes ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
    simp [this, hl]
  · simp [(hsh.1 hz).2]

/-- Every `ENT` send is a row of some id `E` with its message bytes. -/
theorem ent_send (hw : NodeWf3 vs) (hvw : ValWf es) {m : Msg}
    (hm : m ∈ nodeSends3 vs B_ENT ++ valSends es B_ENT) :
    ∃ E, E < P ∧ m ∈ entR E (bN vs es E) := by
  rw [entS, List.mem_append] at hm
  rcases hm with hm | hm
  · rw [List.mem_flatMap] at hm
    obtain ⟨⟨s, n⟩, hsn, hm⟩ := hm
    obtain ⟨hn, rfl⟩ := mem_zip_range hsn
    by_cases hd : vs[n].hd = true
    · refine ⟨eidN n, nid_lt hw hn K_NPRE (by decide), ?_⟩
      rw [eidN, bN_node vs es hn]
      simpa [entR, ser_ne_nil, hd, eidN] using hm
    · simp [hd] at hm
  · rw [List.mem_flatMap] at hm
    obtain ⟨e, he, hm⟩ := hm
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    split at hm
    · have hv := vid_small hvw ht
      have hvl := vlen_le hvw
      refine ⟨eidV es[t], by unfold eidV msgId K_VPRE P; rw [hv]; omega, ?_⟩
      rw [entRows_eq hvw he] at hm
      rw [eidV, hv] at hm ⊢; rwa [bN_val vs es ht]
    · simp at hm

theorem ent_recv_node {n : Nat} (hn : n < vs.length) (hd : vs[n].dup = true) :
    ∀ m ∈ entR vs[n].repE (vs[n].v.ser false), m ∈ nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT := by
  intro m hm
  rw [entRv, List.mem_append, List.mem_flatMap]
  left
  refine ⟨(vs[n], n), zip_range_mem vs hn, ?_⟩
  simp only [hd, if_true]
  simpa [entR, ser_ne_nil] using hm

theorem ent_recv_val (hvw : ValWf es) {e : ValE} (he : e ∈ es) (hd : e.dup = true) :
    ∀ m ∈ entR e.repE e.bytes, m ∈ nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT := by
  intro m hm
  rw [entRv, List.mem_append, List.mem_flatMap]
  right
  rw [List.mem_flatMap]
  refine ⟨e, he, ?_⟩
  rw [if_pos hd, entRows_eq hvw he]; exact hm

/-- The `ENT` balance. -/
def EntBal (vs : List NodeS3) (es : List ValE) : Prop :=
  ((nodeSends3 vs B_ENT ++ valSends es B_ENT).map Msg.toFp).Perm
    ((nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT).map Msg.toFp)

/-- The `DUP` balance. -/
def DupBal (us : List UniqE) (vs : List NodeS3) (es : List ValE) : Prop :=
  ((uniqSends us B_DUP).map Msg.toFp).Perm ((nodeRecvs3 vs B_DUP ++ valRecvs es B_DUP).map Msg.toFp)

/-- **A duplicate receives the bytes of its representative.** -/
theorem ent_match (hw : NodeWf3 vs) (hvw : ValWf es) (hENT : EntBal vs es) {E : Nat} (hE : E < P)
    {X : List Nat} (hX : ∀ x ∈ X, x < P) (hXl : X.length < P)
    (hr : ∀ m ∈ entR E X, m ∈ nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT) : X = bN vs es E := by
  obtain ⟨hY, hYl⟩ := bN_ok hw hvw E
  apply entR_inj hX hXl hY hYl
  intro m hm
  have h1 : m.toFp ∈ (nodeRecvs3 vs B_ENT ++ valRecvs es B_ENT).map Msg.toFp := List.mem_map_of_mem (hr m hm)
  rw [← hENT.mem_iff, List.mem_map] at h1
  obtain ⟨m', hm', he⟩ := h1
  obtain ⟨E', hE', hm''⟩ := ent_send hw hvw hm'
  -- the ids agree
  have hh : ∀ X' : List Nat, ∀ E0, ∀ m0 ∈ entR E0 X', m0.head? = some E0 := by
    intro X' E0 m0 h0
    unfold entR at h0
    split at h0
    · simp at h0; subst h0; rfl
    · simp only [List.mem_map] at h0; obtain ⟨p, -, rfl⟩ := h0; rfl
  have e1 := hh _ _ _ hm''
  have e2 := hh _ _ _ hm
  have : E' = E := by
    cases m' with
    | nil => simp at e1
    | cons a r =>
      cases m with
      | nil => simp at e2
      | cons b r' =>
        simp only [List.head?_cons, Option.some.injEq] at e1 e2
        subst e1 e2
        simp only [Msg.toFp, List.map_cons, List.cons.injEq] at he
        exact ofNat_eq hE' hE he.1
  subst this
  rw [← he]; exact List.mem_map_of_mem hm''

theorem dupS (us : List UniqE) : uniqSends us B_DUP = (us.filter fun e => e.eq == 1).map fun e => [e.eid, e.peid] := by
  simp [uniqSends]

theorem dupR (vs : List NodeS3) (es : List ValE) : nodeRecvs3 vs B_DUP ++ valRecvs es B_DUP =
    (vs.zip (List.range vs.length)).filterMap (fun (s, n) => if s.dup then some [eidN n, s.repE] else none) ++
    es.flatMap (fun e => if e.dup then [[eidV e, e.repE]] else []) := by
  simp [nodeRecvs3, valRecvs, B_DUP, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_VBYTES, B_VPARENT]

/-- **`hdup`**: an equal entry carries the message bytes of its predecessor. -/
theorem dup_bytes {us : List UniqE} (hw : NodeWf3 vs) (hvw : ValWf es) (huw : UniqWf us)
    (hDUP : DupBal us vs es) (hENT : EntBal vs es) :
    ∀ t (ht : t + 1 < us.length), us[t + 1].eq = 1 → bOf vs es us[t + 1].eid = bOf vs es us[t].eid := by
  intro t ht heq
  obtain ⟨hpe, -, -, -⟩ := huw.link t ht
  have c1 := huw.canon _ (List.getElem_mem ht)
  have c0 := huw.canon _ (List.getElem_mem (show t < us.length by omega))
  have hm : [us[t + 1].eid, us[t + 1].peid] ∈ uniqSends us B_DUP := by
    rw [dupS, List.mem_map]; exact ⟨us[t + 1], List.mem_filter.2 ⟨List.getElem_mem ht, by simp [heq]⟩, rfl⟩
  have h1 := List.mem_map_of_mem (f := Msg.toFp) hm
  rw [hDUP.mem_iff, List.mem_map, dupR] at h1
  obtain ⟨m, hm', he⟩ := h1
  rw [List.mem_append] at hm'
  unfold bOf
  congr 1
  rcases hm' with hm' | hm'
  · rw [List.mem_filterMap] at hm'
    obtain ⟨⟨s, n⟩, hsn, hm'⟩ := hm'
    obtain ⟨hn, rfl⟩ := mem_zip_range hsn
    by_cases hd : vs[n].dup = true
    · simp only [hd, if_true, Option.some.injEq] at hm'; subst hm'
      simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
      have sn := hw.small _ (List.getElem_mem hn)
      have e1 := ofNat_eq (nid_lt hw hn K_NPRE (by decide)) c1.1 he.1
      have e2 := ofNat_eq sn.2.2.2.2.1 c1.2.1 he.2
      rw [hpe] at e2
      rw [← e1]; (try rw [eidN]); rw [bN_node vs es hn, ← e2]
      exact ent_match hw hvw hENT sn.2.2.2.2.1 (ser_lt_P hw hn)
        (by have := ser_len_lt hw hn; unfold P; omega) (ent_recv_node hn hd)
    · simp [hd] at hm'
  · rw [List.mem_flatMap] at hm'
    obtain ⟨e, he', hm'⟩ := hm'
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem he'
    by_cases hd : es[u].dup = true
    · simp only [hd, if_true, List.mem_singleton] at hm'; subst hm'
      simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
      have cu := hvw.canon _ he'
      have hv := vid_small hvw hu
      have hvl := vlen_le hvw
      have e1 := ofNat_eq (by unfold eidV msgId K_VPRE P; rw [hv]; omega) c1.1 he.1
      have e2 := ofNat_eq cu.2.2.1 c1.2.1 he.2
      rw [hpe] at e2
      rw [← e1, eidV, hv, bN_val vs es hu, ← e2]
      exact ent_match hw hvw hENT cu.2.2.1 cu.2.2.2
        (by have := val_bytes_lt hvw hu; unfold P; omega) (ent_recv_val hvw he' hd)
    · simp [hd] at hm'

end ZkFormal.NearV3.Link3
