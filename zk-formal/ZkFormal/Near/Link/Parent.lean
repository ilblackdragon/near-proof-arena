import ZkFormal.Near.Link.Nodup

/-!
# ZkFormal.Near.Link.Parent — the `PARENT` bus

* `parent_link` — a revealed child slot `(c, l, r)` of node `n` points at a
  non-root node `c` in range, with `l` its serialization length, `r` its walk
  target, and `depth c = depth n + 1` in the field;
* `refCount_eq` — every non-root node is referenced by exactly one child slot
  (and nothing else is referenced).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem revealed_raw3 {v : NodeV} {c l r : Nat} {pre po : List Nat}
    (hm : (c, l, r, pre, po) ∈ v.revealed) : c ∈ v.raw ∧ l ∈ v.raw ∧ r ∈ v.raw := by
  cases v with
  | leaf => simp [NodeV.revealed] at hm
  | ext k kid memB =>
    cases kid with
    | node c' l' r' pre' po' =>
      simp only [NodeV.revealed, List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, -, -⟩ := hm
      simp [NodeV.raw, NKid.raw]
    | _ => simp [NodeV.revealed] at hm
  | branch sv kids memB =>
    simp only [NodeV.revealed, List.mem_filterMap] at hm
    obtain ⟨kd, hkd, he⟩ := hm
    cases kd with
    | node c' l' r' pre' po' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -, -⟩ := he
      refine ⟨?_, ?_, ?_⟩ <;> simp only [NodeV.raw, List.mem_append, List.mem_flatMap] <;>
        left <;> right <;> exact ⟨_, hkd, by simp [NKid.raw]⟩
    | _ => simp at he

/-- Revealed children with id `c` = references to node `c` in the record. -/
theorem revealed_count (v : NodeV) (c : Nat) :
    (v.revealed.filter (fun x => x.1 == c)).length = v.toRec.kids.count (Kid.node c) := by
  cases v with
  | leaf => simp [NodeV.revealed, NodeV.toRec, NodeRec.kids]
  | ext k kid memB =>
    cases kid <;> simp [NodeV.revealed, NodeV.toRec, NodeRec.kids, NKid.toRec, List.count_cons,
      List.filter_cons] <;> split <;> simp_all
  | branch sv kids memB =>
    simp only [NodeV.revealed, NodeV.toRec, NodeRec.kids]
    induction kids with
    | nil => rfl
    | cons kd kids ih =>
      cases kd <;> simp [List.filterMap_cons, NKid.toRec, List.count_cons, List.filter_cons, ih] <;>
        split <;> simp_all

def headIs (c : Nat) (m : List Fp) : Bool := m.head? == some (Fp.ofNat c)

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

omit h in
theorem nodeSends_parent : nodeSends vs B_PARENT = (vs.zip (List.range vs.length)).flatMap
    fun p => p.1.v.revealed.map fun x => [x.1, p.1.depth + 1, x.2.1, x.2.2.1] := by
  simp [nodeSends, B_PARENT, B_BYTES]

omit h in
theorem nodeRecvs_parent (pub : List Fp) : nodeRecvs vs pub B_PARENT =
    ((vs.zip (List.range vs.length)).drop 1).map
      fun p => [p.2, p.1.depth, (p.1.v.ser false).length, p.1.res] := by
  simp [nodeRecvs, B_PARENT, B_DIGEST]

theorem ser_len_lt {n : Nat} (hn : n < vs.length) : (vs[n].v.ser false).length < P := by
  have := Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _)
    (le_sum_of_mem (fun s : NodeS => (s.v.ser false).length + if s.v.touched then 72 else 0)
      (List.getElem_mem hn))) h.node.size
  unfold P; omega

omit h in
theorem mem_parent_recvs {m : Msg} (hm : m ∈ nodeRecvs vs (publicOf c) B_PARENT) :
    ∃ n, ∃ hn : n < vs.length, 0 < n ∧
      m = [n, vs[n].depth, (vs[n].v.ser false).length, vs[n].res] := by
  rw [nodeRecvs_parent] at hm
  obtain ⟨⟨s, n⟩, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hp
  simp only [List.getElem_drop, List.length_drop, List.length_zip, List.length_range,
    Nat.min_self] at he hi
  rw [List.getElem_zip] at he
  simp only [List.getElem_range, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨1 + i, by omega, by omega, rfl⟩

/-- **A revealed child slot points at its child.** -/
theorem parent_link {n : Nat} (hn : n < vs.length) {c' l r : Nat} {pre po : List Nat}
    (hm : (c', l, r, pre, po) ∈ vs[n].v.revealed) :
    ∃ hc : c' < vs.length, 0 < c' ∧ l = (vs[c'].v.ser false).length ∧ r = vs[c'].res ∧
      Fp.ofNat (vs[n].depth + 1) = Fp.ofNat vs[c'].depth := by
  have hcan := h.node.canon _ (List.getElem_mem hn)
  obtain ⟨r1, r2, r3⟩ := revealed_raw3 hm
  have hs : [c', vs[n].depth + 1, l, r] ∈ nearSends (publicOf c) vs ws rs as mv ids B_PARENT := by
    rw [nearSends_parent, nodeSends_parent]
    exact List.mem_flatMap.mpr ⟨(vs[n], n), mem_zip_range.mpr ⟨hn, rfl⟩,
      List.mem_map.mpr ⟨(c', l, r, pre, po), hm, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := sent_recv h (by decide) (by decide) hs
  rw [nearRecvs_parent] at hy
  obtain ⟨n', hn', hpos, rfl⟩ := mem_parent_recvs hy
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨e1, e2, e3, e4, -⟩ := he
  have hlt := vs_length_lt h.node
  have hsm := h.node.small _ (List.getElem_mem hn')
  have := ofNat_inj (by omega) (hcan c' r1) e1; subst this
  refine ⟨hn', hpos, (ofNat_inj (ser_len_lt h hn') (hcan l r2) e3).symm,
    (ofNat_inj hsm.2.1 (hcan r r3) e4).symm, e2.symm⟩

theorem sends_filter_len (c' : Nat) (hc : c' < P) :
    (((nearSends (publicOf c) vs ws rs as mv ids B_PARENT).map Msg.toFp).filter (headIs c')).length =
      refCount (vs.map (·.v.toRec)) c' := by
  rw [nearSends_parent, nodeSends_parent, List.filter_map, List.length_map, List.filter_flatMap,
    List.length_flatMap]
  unfold refCount
  have hz : vs.map (fun s : NodeS => s.v.toRec.kids.count (Kid.node c')) =
      (vs.zip (List.range vs.length)).map (fun p => p.1.v.toRec.kids.count (Kid.node c')) := by
    conv => lhs; rw [← List.map_fst_zip (l₁ := vs) (l₂ := List.range vs.length) (by simp)]
    rw [List.map_map]; rfl
  rw [List.map_map]
  rw [show ((fun nr : NodeRec => List.count (Kid.node c') nr.kids) ∘ fun x : NodeS => x.v.toRec) =
    (fun s : NodeS => s.v.toRec.kids.count (Kid.node c')) from rfl, hz]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨hn, hpe⟩ := mem_zip_range.mp (show (p.1, p.2) ∈ _ from hp)
  have hcan := h.node.canon _ (hpe ▸ List.getElem_mem hn)
  rw [List.filter_map, List.length_map, ← revealed_count]
  congr 1
  apply List.filter_congr
  intro x hx
  have h1 := (revealed_raw3 (show (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) ∈ _ from hx)).1
  show (some (Fp.ofNat x.1) == some (Fp.ofNat c')) = (x.1 == c')
  by_cases hxc : x.1 = c'
  · simp [hxc]
  · have : Fp.ofNat x.1 ≠ Fp.ofNat c' := fun he => hxc (ofNat_inj (hcan _ h1) hc he)
    have h2 : some (Fp.ofNat x.1) ≠ some (Fp.ofNat c') := fun he => this (Option.some.inj he)
    rw [beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr hxc]

theorem recvs_filter_len (c' : Nat) (h0 : 0 < c') (hc : c' < vs.length) :
    (((nearRecvs (publicOf c) vs ws rs as mv ids B_PARENT).map Msg.toFp).filter (headIs c')).length
      = 1 := by
  have hlt := vs_length_lt h.node
  rw [nearRecvs_parent, nodeRecvs_parent, List.filter_map, List.length_map, List.filter_map,
    List.length_map]
  have e : ((vs.zip (List.range vs.length)).drop 1).filter
      ((headIs c' ∘ Msg.toFp) ∘ fun p : NodeS × Nat => [p.2, p.1.depth, (p.1.v.ser false).length, p.1.res]) =
      ((vs.zip (List.range vs.length)).drop 1).filter ((· == c') ∘ Prod.snd) := by
    apply List.filter_congr
    intro p hp
    have : p.2 < vs.length := by
      have := (mem_zip_range.mp (show (p.1, p.2) ∈ _ from List.mem_of_mem_drop hp)).1; exact this
    simp only [Function.comp, headIs, Msg.toFp, List.map_cons, List.head?_cons]
    show (some (Fp.ofNat p.2) == some (Fp.ofNat c')) = (p.2 == c')
    by_cases hpc : p.2 = c'
    · simp [hpc]
    · have : Fp.ofNat p.2 ≠ Fp.ofNat c' := fun he => hpc (ofNat_inj (by omega) (by omega) he)
      have h2 : some (Fp.ofNat p.2) ≠ some (Fp.ofNat c') := fun he => this (Option.some.inj he)
      rw [beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr hpc]
  rw [e, ← List.length_map (f := Prod.snd), ← List.filter_map, List.map_drop, map_snd_zip_range,
    ← List.count_eq_length_filter, List.Nodup.count (List.nodup_range.sublist (List.drop_sublist _ _))]
  rw [if_pos]
  rw [List.mem_iff_getElem]
  refine ⟨c' - 1, by simp; omega, by simp; omega⟩

/-- **Every non-root node has exactly one parent slot.** -/
theorem refCount_one (c' : Nat) (h0 : 0 < c') (hc : c' < vs.length) :
    refCount (vs.map (·.v.toRec)) c' = 1 := by
  have hlt := vs_length_lt h.node
  rw [← sends_filter_len h c' (by omega), ((perm h (by decide) (by decide)).filter _).length_eq,
    recvs_filter_len h c' h0 hc]

end Hyp

end Link

end ZkFormal.Near
