import ZkFormal.NearV3.Link.Records3

/-!
# ZkFormal.NearV3.Link.Parent3 — `PARENT` balance: kids, roots, depths

`PARENT` is sent by revealed kid windows of node records (`[c, τ, d+1, clen, cres]`) and by
instance heads (`[rid, τ, 0, rlen, rres]`); every node record `n` receives
`[n, τ, depth, len, res]` once.  From the balance on this bus alone:

* `kid_link` — a revealed kid `c` of record `p` is a record of the same instance, with
  `depth c ≡ depth p + 1`, `res c = cres`;
* `head_link` — a head's root `rid` is a record of its instance at depth `0`, `res = rres`;
* `sender_of` — every record has a sender (a head or a parent record);
* `depth_lt` — every record has depth `< 400` (the 9-bit check of `nodeV3` excludes the
  wrapped depths: following senders upwards they would decrease below `P − 112`);
* `kid_depth` — hence `depth c = depth p + 1` exactly.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

def cnt3 (l : List Msg) (m : List Fp) : Nat := (l.map Msg.toFp).count m

theorem ofNat_eq {a b : Nat} (ha : a < P) (hb : b < P) (h : Fp.ofNat a = Fp.ofNat b) : a = b :=
  ofNat_inj ha hb h

theorem ofNat_mod (a : Nat) : Fp.ofNat a = Fp.ofNat (a % P) := by
  rw [← natCast_eq, ← natCast_eq]; apply Fp.ext; simp [natCast_eq]

theorem ofNat_eq_mod {a b : Nat} (hb : b < P) (h : Fp.ofNat a = Fp.ofNat b) : a % P = b := by
  rw [ofNat_mod a] at h; exact ofNat_eq (Nat.mod_lt _ (by unfold P; omega)) hb h

/-- The `PARENT` balance. -/
def ParentBal (vs : List NodeS3) (hs : List HeadE) : Prop :=
  ∀ m, cnt3 (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) m = cnt3 (nodeRecvs3 vs B_PARENT) m

theorem parentR (vs : List NodeS3) :
    nodeRecvs3 vs B_PARENT = (vs.zip (List.range vs.length)).map fun (s, n) =>
      [n, s.tau, s.depth, (s.v.ser false).length, s.res] := by
  simp [nodeRecvs3, B_PARENT, B_DIGEST]

theorem parentS (vs : List NodeS3) :
    nodeSends3 vs B_PARENT = (vs.zip (List.range vs.length)).flatMap fun (s, _) =>
      s.v.revealed.map fun (c, l, r, _, _) => [c, s.tau, s.depth + 1, l, r] := by
  simp [nodeSends3, B_PARENT, B_BYTES]

theorem headS (hs : List HeadE) : headSends hs B_PARENT = hs.map fun h => [h.rid, h.tau, 0, h.rlen, h.rres] := by
  simp [headSends, B_PARENT, B_MIDROOT]

theorem mem_zip_range {α : Type} {l : List α} {x : α} {n : Nat} (h : (x, n) ∈ l.zip (List.range l.length)) :
    ∃ hn : n < l.length, l[n] = x := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, he⟩ := h
  simp only [List.length_zip, List.length_range, Nat.min_self] at hi
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at he
  obtain ⟨h1, rfl⟩ := he
  exact ⟨hi, h1⟩

theorem zip_range_mem {α : Type} (l : List α) {n : Nat} (hn : n < l.length) :
    (l[n], n) ∈ l.zip (List.range l.length) := by
  rw [List.mem_iff_getElem]
  exact ⟨n, by simp [hn], by simp⟩

/-- A sent message is received: some record `n` receives it. -/
theorem recv_of_send {vs : List NodeS3} {hs : List HeadE} (hb : ParentBal vs hs) {m : Msg}
    (hm : m ∈ nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) :
    ∃ n, ∃ hn : n < vs.length, Msg.toFp m =
      Msg.toFp [n, vs[n].tau, vs[n].depth, (vs[n].v.ser false).length, vs[n].res] := by
  have h1 : 0 < cnt3 (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) (Msg.toFp m) :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)
  rw [hb, cnt3, List.count_pos_iff, List.mem_map] at h1
  obtain ⟨m', hm', he⟩ := h1
  rw [parentR, List.mem_map] at hm'
  obtain ⟨⟨s, n⟩, hsn, rfl⟩ := hm'
  obtain ⟨hn, rfl⟩ := mem_zip_range hsn
  exact ⟨n, hn, he.symm⟩

/-- A received message is sent. -/
theorem send_of_recv {vs : List NodeS3} {hs : List HeadE} (hb : ParentBal vs hs) {n : Nat}
    (hn : n < vs.length) :
    Msg.toFp [n, vs[n].tau, vs[n].depth, (vs[n].v.ser false).length, vs[n].res] ∈
      (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT).map Msg.toFp := by
  have h1 : 0 < cnt3 (nodeRecvs3 vs B_PARENT)
      (Msg.toFp [n, vs[n].tau, vs[n].depth, (vs[n].v.ser false).length, vs[n].res]) := by
    rw [cnt3, List.count_pos_iff, List.mem_map]
    exact ⟨_, by rw [parentR, List.mem_map]; exact ⟨(vs[n], n), zip_range_mem vs hn, rfl⟩, rfl⟩
  rw [← hb, cnt3, List.count_pos_iff] at h1
  exact h1

theorem revealed_raw {v : NodeV3} {c l r : Nat} {pre po : List Nat} (h : (c, l, r, pre, po) ∈ v.revealed) :
    c ∈ v.raw ∧ l ∈ v.raw ∧ r ∈ v.raw := by
  cases v with
  | leaf k s m => simp [NodeV3.revealed] at h
  | ext k kid m =>
    cases kid <;> simp [NodeV3.revealed] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    simp [NodeV3.raw, NKid.raw]
  | branch sv kids m =>
    simp only [NodeV3.revealed, List.mem_filterMap] at h
    obtain ⟨kd, hk, he⟩ := h
    cases kd with
    | none => simp at he
    | hash _ => simp at he
    | node c' l' r' pre' po' =>
      simp at he; obtain ⟨h1, h2, h3, -, -⟩ := he
      rw [← h1, ← h2, ← h3]
      have : ∀ x ∈ [c', l', r'], x ∈ (NodeV3.branch sv kids m).raw := by
        intro x hx; simp only [NodeV3.raw, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨_, hk, by simp [NKid.raw]; simp at hx; omega⟩)
      exact ⟨this c' (by simp), this l' (by simp), this r' (by simp)⟩

variable {vs : List NodeS3} {hs : List HeadE}

/-- **Kids.** -/
theorem kid_link (hw : NodeWf3 vs) (hb : ParentBal vs hs) {p : Nat} (hp : p < vs.length)
    {c l r : Nat} {pre po : List Nat} (hk : (c, l, r, pre, po) ∈ vs[p].v.revealed) :
    ∃ hc : c < vs.length, vs[c].tau = vs[p].tau ∧ vs[c].depth = (vs[p].depth + 1) % P ∧
      (vs[c].v.ser false).length % P = l ∧ vs[c].res = r := by
  have hmem : [c, vs[p].tau, vs[p].depth + 1, l, r] ∈ nodeSends3 vs B_PARENT ++ headSends hs B_PARENT := by
    rw [List.mem_append, parentS]; left
    rw [List.mem_flatMap]
    exact ⟨(vs[p], p), zip_range_mem vs hp, List.mem_map.mpr ⟨(c, l, r, pre, po), hk, rfl⟩⟩
  obtain ⟨n, hn, he⟩ := recv_of_send hb hmem
  obtain ⟨rc, rl, rr⟩ := revealed_raw hk
  have cp := hw.canon _ (List.getElem_mem hp)
  have sp := hw.small _ (List.getElem_mem hp)
  have sn := hw.small _ (List.getElem_mem hn)
  have hnP : n < P := by have := hw.count; unfold P; omega
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  obtain ⟨e1, e2, e3, e4, e5⟩ := he
  have := ofNat_eq (cp c rc) hnP e1; subst this
  exact ⟨hn, (ofNat_eq sp.1 sn.1 e2).symm, (ofNat_eq_mod sn.2.1 e3).symm, (ofNat_eq_mod (cp l rl) e4.symm),
    (ofNat_eq (cp r rr) sn.2.2.1 e5).symm⟩

/-- **Roots.** -/
theorem head_link (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) {h : HeadE} (hh : h ∈ hs) :
    ∃ hr : h.rid < vs.length, vs[h.rid].tau = h.tau ∧ vs[h.rid].depth = 0 ∧
      (vs[h.rid].v.ser false).length % P = h.rlen ∧ vs[h.rid].res = h.rres := by
  have hmem : [h.rid, h.tau, 0, h.rlen, h.rres] ∈ nodeSends3 vs B_PARENT ++ headSends hs B_PARENT := by
    rw [List.mem_append, headS]; right; exact List.mem_map.mpr ⟨h, hh, rfl⟩
  obtain ⟨n, hn, he⟩ := recv_of_send hb hmem
  have ch := hhw.canon h hh
  have sn := hw.small _ (List.getElem_mem hn)
  have hnP : n < P := by have := hw.count; unfold P; omega
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  obtain ⟨e1, e2, e3, e4, e5⟩ := he
  have := ofNat_eq ch.2.1 hnP e1; subst this
  exact ⟨hn, (ofNat_eq ch.1 sn.1 e2).symm, (ofNat_eq (by unfold P; omega) sn.2.1 e3).symm,
    ofNat_eq_mod ch.2.2.1 e4.symm, (ofNat_eq ch.2.2.2.1 sn.2.2.1 e5).symm⟩

/-- **Senders.** Every record is the root of a head or a revealed kid of a record. -/
theorem sender_of (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) {n : Nat} (hn : n < vs.length) :
    (∃ h ∈ hs, h.rid = n ∧ h.tau = vs[n].tau ∧ vs[n].depth = 0) ∨
    (∃ p, ∃ hp : p < vs.length, ∃ l r pre po, (n, l, r, pre, po) ∈ vs[p].v.revealed ∧
      vs[p].tau = vs[n].tau ∧ vs[n].depth = (vs[p].depth + 1) % P) := by
  have hm := send_of_recv hb hn
  rw [List.map_append, List.mem_append] at hm
  rcases hm with hm | hm
  · right
    rw [List.mem_map, parentS] at hm
    obtain ⟨m, hm, he⟩ := hm
    rw [List.mem_flatMap] at hm
    obtain ⟨⟨s, p⟩, hsp, hm⟩ := hm
    obtain ⟨hp, rfl⟩ := mem_zip_range hsp
    rw [List.mem_map] at hm
    obtain ⟨⟨c, l, r, pre, po⟩, hk, rfl⟩ := hm
    obtain ⟨hc, ht, hd, -, -⟩ := kid_link (hs := hs) hw hb hp hk
    obtain ⟨rc, -, -⟩ := revealed_raw hk
    have cp := hw.canon _ (List.getElem_mem hp)
    have hnP : n < P := by have := hw.count; unfold P; omega
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := ofNat_eq (cp c rc) hnP he.1; subst this
    exact ⟨p, hp, l, r, pre, po, hk, ht.symm, hd⟩
  · left
    rw [List.mem_map, headS] at hm
    obtain ⟨m, hm, he⟩ := hm
    rw [List.mem_map] at hm
    obtain ⟨h, hh, rfl⟩ := hm
    obtain ⟨hr, ht, hd, -, -⟩ := head_link hw hhw hb hh
    have ch := hhw.canon h hh
    have hnP : n < P := by have := hw.count; unfold P; omega
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := ofNat_eq ch.2.1 hnP he.1; subst this
    exact ⟨h, hh, rfl, ht.symm, hd⟩

/-- **Depths are below 400.** -/
theorem depth_lt (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) {n : Nat} (hn : n < vs.length) :
    vs[n].depth < 400 := by
  have hP : 400 + 112 < P := by unfold P; omega
  -- wrapped depths `P − 112 + v`: induction on `v`
  have wrapped : ∀ v, ∀ n (hn : n < vs.length), vs[n].depth ≠ P - 112 + v := by
    intro v
    induction v with
    | zero =>
      intro n hn hd
      rcases sender_of hw hhw hb hn with ⟨h, -, -, -, h0⟩ | ⟨p, hp, l, r, pre, po, hk, -, hdp⟩
      · rw [h0] at hd; omega
      · have dp := hw.depth _ (List.getElem_mem hp)
        have dps := (hw.small _ (List.getElem_mem hp)).2.1
        rw [hd] at hdp
        rcases dp with dp | dp
        · rw [Nat.mod_eq_of_lt (by omega)] at hdp; omega
        · by_cases h1 : vs[p].depth + 1 < P
          · rw [Nat.mod_eq_of_lt h1] at hdp; omega
          · rw [show vs[p].depth + 1 = P by omega, Nat.mod_self] at hdp; omega
    | succ v ih =>
      intro n hn hd
      rcases sender_of hw hhw hb hn with ⟨h, -, -, -, h0⟩ | ⟨p, hp, l, r, pre, po, hk, -, hdp⟩
      · rw [h0] at hd; omega
      · have dp := hw.depth _ (List.getElem_mem hp)
        have dps := (hw.small _ (List.getElem_mem hp)).2.1
        have hn' := (hw.small _ (List.getElem_mem hn)).2.1
        rw [hd] at hdp
        rcases dp with dp | dp
        · rw [Nat.mod_eq_of_lt (by omega)] at hdp; omega
        · by_cases h1 : vs[p].depth + 1 < P
          · rw [Nat.mod_eq_of_lt h1] at hdp
            exact ih p hp (by omega)
          · rw [show vs[p].depth + 1 = P by omega, Nat.mod_self] at hdp; omega
  rcases hw.depth _ (List.getElem_mem hn) with h | h
  · exact h
  · exfalso
    have := (hw.small _ (List.getElem_mem hn)).2.1
    exact wrapped (vs[n].depth - (P - 112)) n hn (by omega)

/-- **Child depth.** -/
theorem kid_depth (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) {p : Nat} (hp : p < vs.length)
    {c l r : Nat} {pre po : List Nat} (hk : (c, l, r, pre, po) ∈ vs[p].v.revealed) :
    ∃ hc : c < vs.length, vs[c].tau = vs[p].tau ∧ vs[c].depth = vs[p].depth + 1 ∧ vs[c].res = r := by
  obtain ⟨hc, ht, hd, -, hr⟩ := kid_link hw hb hp hk
  have := depth_lt hw hhw hb hp
  exact ⟨hc, ht, by rw [hd, Nat.mod_eq_of_lt (by unfold P; omega)], hr⟩

end ZkFormal.NearV3.Link3
