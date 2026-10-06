import ZkFormal.NearV3.Link.Post3Writes
import ZkFormal.NearV3.Link.Compose3

/-!
# ZkFormal.NearV3.Link.Post3Occ — every value record occurs at most once (M6d, `occ_le_one`)

Records are tree-shaped: by the `PARENT` balance every record `n` receives its message
`[n, τ, d, len, res]` exactly once, so at most one kid slot of all records sends it (one parent
revealing the same kid in two slots would send it twice).  Kid depths increase by one.  By
`VPARENT` balance at most one record holds a given value id (`val_unique`).

Spec side (generic records `ns`, rank `rk`):
* `pc3 ns m f n` — number of paths from record `n` to record `m` (fuel `f`);
* `pc_le_one` — `≤ 1` when every record has at most one incoming kid slot overall
  (`HK`, as a count bound per record pair) and kids have a larger rank;
* `occ_le_pc` / `fullOcc_le_one` — occurrences of value id `i` are bounded by the paths to its
  unique holder.

Link side: **`occ_le_one`** — for `R := recsOf (vpos (vid0 es)) vs`, every value id position
`i` and every record `n` (in particular every head root `h.rid`): `fullOcc R i n ≤ 1`.

Heads sharing a root record do not matter: `fullOcc` counts within the unfolding of one root.
(In fact two heads cannot share a root: both would send the same `PARENT` message.)
-/

namespace ZkFormal.NearV3

open NearSpec

/-! ## Paths -/

/-- Number of paths from record `n` down to record `m` (fuel `f`). -/
def pc3 (ns : List NodeRec3) (m : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n =>
    match ns[n]? with
    | none => 0
    | some nr => (if n = m then 1 else 0) + kOcc (pc3 ns m f) nr.node.kids

theorem kOcc_mono {g g' : Nat → Nat} (h : ∀ c, g c ≤ g' c) : ∀ kids, kOcc g kids ≤ kOcc g' kids
  | [] => Nat.le_refl _
  | .node c :: r => by have := kOcc_mono h r; have := h c; simp only [kOcc]; omega
  | .none :: r => by simp only [kOcc]; exact kOcc_mono h r
  | .hash _ :: r => by simp only [kOcc]; exact kOcc_mono h r

theorem kOcc_add (g g' : Nat → Nat) : ∀ kids, kOcc (fun c => g c + g' c) kids = kOcc g kids + kOcc g' kids
  | [] => rfl
  | .node c :: r => by have := kOcc_add g g' r; simp only [kOcc]; omega
  | .none :: r => by simp only [kOcc]; exact kOcc_add g g' r
  | .hash _ :: r => by simp only [kOcc]; exact kOcc_add g g' r

theorem kOcc_ind (n : Nat) : ∀ kids, kOcc (fun c => if c = n then 1 else 0) kids = kids.count (Kid3.node n)
  | [] => rfl
  | .node c :: r => by
    have := kOcc_ind n r
    simp only [kOcc, List.count_cons, this]
    by_cases h : c = n
    · subst h; simp <;> omega
    · simp [h] <;> omega
  | .none :: r => by simp only [kOcc, List.count_cons, kOcc_ind n r]; simp
  | .hash _ :: r => by simp only [kOcc, List.count_cons, kOcc_ind n r]; simp

theorem kOcc_pos {g : Nat → Nat} : ∀ kids, 0 < kOcc g kids → ∃ c, Kid3.node c ∈ kids ∧ 0 < g c
  | [], h => by simp [kOcc] at h
  | .node c :: r, h => by
    simp only [kOcc] at h
    by_cases hc : 0 < g c
    · exact ⟨c, by simp, hc⟩
    · obtain ⟨c', h1, h2⟩ := kOcc_pos (g := g) r (by omega); exact ⟨c', by simp [h1], h2⟩
  | .none :: r, h => by
    simp only [kOcc] at h; obtain ⟨c', h1, h2⟩ := kOcc_pos r h; exact ⟨c', by simp [h1], h2⟩
  | .hash _ :: r, h => by
    simp only [kOcc] at h; obtain ⟨c', h1, h2⟩ := kOcc_pos r h; exact ⟨c', by simp [h1], h2⟩

theorem vids_count_le (r : Rec3) (i : Nat) : r.vids.count i ≤ 1 := by
  have : r.vids.length ≤ 1 := by unfold Rec3.vids; split <;> simp
  have := List.count_le_length (a := i) (l := r.vids); omega

theorem kOcc_const0 : ∀ kids, kOcc (fun _ => 0) kids = 0
  | [] => rfl
  | .node _ :: r => by simp only [kOcc, Nat.zero_add]; exact kOcc_const0 r
  | .none :: r => by simp only [kOcc]; exact kOcc_const0 r
  | .hash _ :: r => by simp only [kOcc]; exact kOcc_const0 r

theorem pc3_succ (ns : List NodeRec3) (m f n : Nat) : pc3 ns m (f + 1) n =
    match ns[n]? with
    | none => 0
    | some nr => (if n = m then 1 else 0) + kOcc (pc3 ns m f) nr.node.kids := rfl

section Paths
variable {ns : List NodeRec3} {rk : Nat → Nat}

/-- Paths go to larger ranks. -/
theorem pc_rank (HR : ∀ (r : Nat) (nr : NodeRec3) c, ns[r]? = some nr → Kid3.node c ∈ nr.node.kids → rk r < rk c) {m : Nat} :
    ∀ f r, 0 < pc3 ns m f r → rk r ≤ rk m := by
  intro f
  induction f with
  | zero => intro r h; simp [pc3] at h
  | succ f ih =>
    intro r h
    simp only [pc3] at h
    cases hr : ns[r]? with
    | none => rw [hr] at h; simp at h
    | some nr =>
      rw [hr] at h; simp only at h
      by_cases hm : r = m
      · subst hm; exact Nat.le_refl _
      · rw [if_neg hm] at h
        obtain ⟨c, hc, hp⟩ := kOcc_pos (g := pc3 ns m f) nr.node.kids (by omega)
        have := HR r nr c hr hc
        have := ih c hp
        omega

/-- No incoming slot: only the trivial path. -/
theorem pc_noparent {n : Nat} (h0 : ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) = 0) :
    ∀ f r, pc3 ns n f r ≤ if r = n then 1 else 0 := by
  intro f
  induction f with
  | zero => intro r; simp [pc3]
  | succ f ih =>
    intro r
    simp only [pc3]
    cases hr : ns[r]? with
    | none => simp
    | some nr =>
      simp only
      have := kOcc_mono ih nr.node.kids
      rw [kOcc_ind, h0 r nr hr] at this
      omega

/-- One incoming slot (at record `p`): paths to `n` are paths to `p`, plus the trivial one. -/
theorem pc_step {n p : Nat}
    (h1 : ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) ≤ if r = p then 1 else 0) :
    ∀ f r, pc3 ns n (f + 1) r ≤ (if r = n then 1 else 0) + pc3 ns p f r := by
  intro f
  induction f with
  | zero =>
    intro r
    rw [pc3_succ]
    cases ns[r]? with
    | none => simp
    | some nr =>
      simp only
      have := kOcc_mono (g := pc3 ns n 0) (g' := fun _ => 0) (fun c => Nat.le_of_eq rfl) nr.node.kids
      rw [kOcc_const0] at this
      omega
  | succ f ih =>
    intro r
    rw [pc3_succ, pc3_succ]
    cases hr : ns[r]? with
    | none => simp
    | some nr =>
      simp only
      have hm := kOcc_mono ih nr.node.kids
      rw [kOcc_add, kOcc_ind] at hm
      have hc := h1 r nr hr
      split at hc <;> split <;> omega

/-- **At most one path** between two records. -/
theorem pc_le_one
    (HR : ∀ (r : Nat) (nr : NodeRec3) c, ns[r]? = some nr → Kid3.node c ∈ nr.node.kids → rk r < rk c)
    (HK : ∀ (n r r' : Nat) (nr nr' : NodeRec3), ns[r]? = some nr → ns[r']? = some nr' →
      0 < nr.node.kids.count (Kid3.node n) → 0 < nr'.node.kids.count (Kid3.node n) → r = r')
    (HK1 : ∀ (n r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) ≤ 1) :
    ∀ n f r, pc3 ns n f r ≤ 1 := by
  have key : ∀ d n, rk n = d → ∀ f r, pc3 ns n f r ≤ 1 := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro n hd f r
      by_cases hp : ∃ (p : Nat) (nr : NodeRec3), ns[p]? = some nr ∧ 0 < nr.node.kids.count (Kid3.node n)
      · obtain ⟨p, nrp, hpn, hpc⟩ := hp
        have h1 : ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) ≤ if r = p then 1 else 0 := by
          intro r nr hr
          by_cases hrp : r = p
          · rw [if_pos hrp]; exact HK1 n r nr hr
          · rw [if_neg hrp]
            by_cases hc : 0 < nr.node.kids.count (Kid3.node n)
            · exact absurd (HK n r p nr nrp hr hpn hc hpc) hrp
            · omega
        have hrk : rk p < rk n := HR p nrp n hpn (List.count_pos_iff.mp hpc)
        cases f with
        | zero => simp [pc3]
        | succ f =>
          have hs := pc_step h1 f r
          by_cases hrn : r = n
          · subst hrn
            have : pc3 ns p f r = 0 := by
              apply Classical.byContradiction; intro hne
              have := pc_rank HR (m := p) f r (by omega); omega
            rw [if_pos rfl] at hs; omega
          · rw [if_neg hrn] at hs
            have := ih (rk p) (by omega) p rfl f r
            omega
      · have h0 : ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) = 0 := by
          intro r nr hr
          apply Classical.byContradiction; intro hne
          exact hp ⟨r, nr, hr, by omega⟩
        have := pc_noparent h0 f r
        split at this <;> omega
  exact fun n f r => key _ n rfl f r

/-- Occurrences of a value id are bounded by the paths to its holder `m`. -/
theorem occ_le_pc {i m : Nat}
    (hv : ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.vids.count i ≤ if r = m then 1 else 0) :
    ∀ f r, occ3 ns i f r ≤ pc3 ns m f r := by
  intro f
  induction f with
  | zero => intro r; simp [occ3, pc3]
  | succ f ih =>
    intro r
    simp only [occ3, pc3]
    cases hr : ns[r]? with
    | none => simp
    | some nr =>
      simp only
      have := kOcc_mono ih nr.node.kids
      have := hv r nr hr
      omega

/-- **Tree-shaped records: one occurrence per value id.** -/
theorem fullOcc_le_one
    (HR : ∀ (r : Nat) (nr : NodeRec3) c, ns[r]? = some nr → Kid3.node c ∈ nr.node.kids → rk r < rk c)
    (HK : ∀ (n r r' : Nat) (nr nr' : NodeRec3), ns[r]? = some nr → ns[r']? = some nr' →
      0 < nr.node.kids.count (Kid3.node n) → 0 < nr'.node.kids.count (Kid3.node n) → r = r')
    (HK1 : ∀ (n r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.kids.count (Kid3.node n) ≤ 1)
    (HV : ∀ (i r r' : Nat) (nr nr' : NodeRec3), ns[r]? = some nr → ns[r']? = some nr' → i ∈ nr.node.vids → i ∈ nr'.node.vids → r = r')
    (i n : Nat) : fullOcc ns i n ≤ 1 := by
  have hm : ∃ m, ∀ (r : Nat) (nr : NodeRec3), ns[r]? = some nr → nr.node.vids.count i ≤ if r = m then 1 else 0 := by
    by_cases he : ∃ (m : Nat) (nr : NodeRec3), ns[m]? = some nr ∧ i ∈ nr.node.vids
    · obtain ⟨m, nrm, hmn, hmi⟩ := he
      refine ⟨m, fun r nr hr => ?_⟩
      by_cases hrm : r = m
      · rw [if_pos hrm]; exact vids_count_le _ _
      · rw [if_neg hrm]
        by_cases hi : i ∈ nr.node.vids
        · exact absurd (HV i r m nr nrm hr hmn hi hmi) hrm
        · exact Nat.le_of_eq (List.count_eq_zero.mpr hi)
    · refine ⟨0, fun r nr hr => ?_⟩
      have : i ∉ nr.node.vids := fun hi => he ⟨r, nr, hr, hi⟩
      rw [List.count_eq_zero.mpr this]; exact Nat.zero_le _
  obtain ⟨m, hv⟩ := hm
  have := occ_le_pc hv ns.length n
  have := pc_le_one HR HK HK1 m ns.length n
  unfold fullOcc; omega

end Paths

end ZkFormal.NearV3

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

/-! ## Link facts -/

/-- Kid slots holding record `n` are the revealed entries with id `n`. -/
theorem kids_count (f : Nat → Nat) (v : NodeV3) (n : Nat) :
    (v.toRec3 f).kids.count (Kid3.node n) = v.revealed.countP (fun e => e.1 == n) := by
  cases v with
  | leaf k s m => simp [NodeV3.toRec3, Rec3.kids, NodeV3.revealed]
  | ext k kid m =>
    cases kid <;> simp [NodeV3.toRec3, Rec3.kids, NodeV3.revealed, NKid.toKid3, List.count_singleton]
  | branch sv kids m =>
    simp only [NodeV3.toRec3, Rec3.kids, NodeV3.revealed]
    induction kids with
    | nil => simp
    | cons kd r ih =>
      cases kd with
      | none => simp [NKid.toKid3, ih]
      | hash h => simp [NKid.toKid3, ih]
      | node c l rr pre po =>
        simp only [List.map_cons, NKid.toKid3, List.count_cons, List.filterMap_cons, List.countP_cons, ih]
        by_cases hc : c = n <;> simp [hc] <;> omega

theorem countP_le_count {α β : Type} [BEq β] [LawfulBEq β] (p : α → Bool) (g : α → β) (M : β) :
    ∀ (l : List α), (∀ e ∈ l, p e = true → g e = M) → l.countP p ≤ (l.map g).count M
  | [], _ => by simp
  | a :: r, h => by
    have ih := countP_le_count p g M r (fun e he => h e (by simp [he]))
    simp only [List.countP_cons, List.map_cons, List.count_cons]
    by_cases hp : p a = true
    · have := h a (by simp) hp
      simp [hp, this]; omega
    · simp only [hp, Bool.false_eq_true, if_false]; split <;> omega

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

/-- The `PARENT` message record `n` receives. -/
def recvMsg (vs : List NodeS3) (n : Nat) : List Fp :=
  Msg.toFp [n, (vs.getD n default).tau, (vs.getD n default).depth,
    ((vs.getD n default).v.ser false).length, (vs.getD n default).res]

/-- Per-record sender counts of a message. -/
def sendCnt (M : List Fp) (x : NodeS3 × Nat) : Nat :=
  ((x.1.v.revealed.map fun (e : Nat × Nat × Nat × List Nat × List Nat) =>
    Msg.toFp [e.1, x.1.tau, x.1.depth + 1, e.2.1, e.2.2.1]).count M)

theorem sends_cnt (vs : List NodeS3) (M : List Fp) :
    cnt3 (nodeSends3 vs B_PARENT) M = ((vs.zip (List.range vs.length)).map (sendCnt M)).sum := by
  rw [cnt3, parentS, List.map_flatMap, List.count_flatMap]
  unfold sendCnt
  congr 1
  apply List.map_congr_left
  intro ⟨s, p⟩ _
  simp [List.map_map, Function.comp_def]

/-- Record `n` receives its message once. -/
theorem recv_cnt (hw : NodeWf3 vs) {n : Nat} : cnt3 (nodeRecvs3 vs B_PARENT) (recvMsg vs n) ≤ 1 := by
  rw [cnt3, parentR, List.map_map]
  apply (List.nodup_iff_count.mp ?_ _)
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab heq
  simp only [List.length_map, List.length_zip, List.length_range, Nat.min_self] at ha hb
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range, Function.comp, Msg.toFp,
    List.map_cons, List.map_nil, List.cons.injEq] at heq
  have hP : vs.length < P := by have := hw.count; unfold P; omega
  have := ofNat_eq (by omega) (by omega) heq.1
  omega

/-- A kid slot holding `n` in record `p` sends `n`'s message. -/
theorem kid_cnt (hw : NodeWf3 vs) (hb : ParentBal vs hs) (f : Nat → Nat) {p : Nat} (hp : p < vs.length)
    (n : Nat) : (vs[p].v.toRec3 f).kids.count (Kid3.node n) ≤ sendCnt (recvMsg vs n) (vs[p], p) := by
  rw [kids_count]
  unfold sendCnt
  apply countP_le_count
  intro ⟨c, l, r, pre, po⟩ he hc
  simp only [beq_iff_eq] at hc; subst hc
  obtain ⟨hc, ht, hd, hl, hr⟩ := kid_link hw hb hp he
  simp only [recvMsg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
    Msg.toFp, List.map_cons, List.map_nil, ht, hr]
  rw [ofNat_mod (vs[p].depth + 1), ← hd, ← hl, ← ofNat_mod]

/-- **One sender**: over all records, the kid slots holding `n` are at most one. -/
theorem kid_slots (hw : NodeWf3 vs) (hb : ParentBal vs hs) (f : Nat → Nat) {n : Nat} :
    (∀ p (hp : p < vs.length), (vs[p].v.toRec3 f).kids.count (Kid3.node n) ≤ 1) ∧
    (∀ p p' (hp : p < vs.length) (hp' : p' < vs.length), p ≠ p' →
      (vs[p].v.toRec3 f).kids.count (Kid3.node n) + (vs[p'].v.toRec3 f).kids.count (Kid3.node n) ≤ 1) := by
  have hS : cnt3 (nodeSends3 vs B_PARENT) (recvMsg vs n) ≤ 1 := by
    have h1 := hb (recvMsg vs n)
    have h2 : cnt3 (nodeSends3 vs B_PARENT) (recvMsg vs n) ≤
        cnt3 (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) (recvMsg vs n) := by
      simp [cnt3, List.count_append]
    have := recv_cnt (n := n) hw; omega
  rw [sends_cnt] at hS
  have hz : (vs.zip (List.range vs.length)).length = vs.length := by simp
  refine ⟨fun p hp => ?_, fun p p' hp hp' hne => ?_⟩
  · have hm := le_sum_mem (List.mem_map.mpr ⟨_, zip_range_mem vs hp, rfl⟩ :
      sendCnt (recvMsg vs n) (vs[p], p) ∈ (vs.zip (List.range vs.length)).map (sendCnt (recvMsg vs n)))
    have := kid_cnt hw hb f hp n; omega
  · have h2 := sum_ge_two (vs.zip (List.range vs.length)) (sendCnt (recvMsg vs n)) (a := p) (b := p')
      (by rw [hz]; exact hp) (by rw [hz]; exact hp') hne
    simp only [List.getElem_zip, List.getElem_range] at h2
    have := kid_cnt hw hb f hp n
    have := kid_cnt hw hb f hp' n
    omega

theorem recsOf_some {f : Nat → Nat} {n : Nat} {nr : NodeRec3} (h : (recsOf f vs)[n]? = some nr) :
    ∃ hn : n < vs.length, nr = ⟨vs[n].tau, vs[n].v.toRec3 f⟩ := by
  have hn : n < vs.length := by have := lt_of_getElem? h; rwa [recsOf_length] at this
  rw [recsOf_get _ _ hn] at h
  exact ⟨hn, (Option.some.inj h).symm⟩

/-- **`occ_le_one`**: in the record trie of every record (in particular every head root), each
value id position occurs at most once. -/
theorem occ_le_one (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (i n : Nat) :
    fullOcc (recsOf (vpos (vid0 es)) vs) i n ≤ 1 := by
  apply fullOcc_le_one (rk := rkOf vs)
  · intro r nr c hr hc
    obtain ⟨hr', rfl⟩ := recsOf_some hr
    obtain ⟨l, rr, pre, po, hk⟩ := (kids_toRec3 _ _ c).mp hc
    obtain ⟨hcl, -, hdc, -⟩ := kid_depth hw hhw hb hr' hk
    simp only [rkOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', List.getElem?_eq_getElem hcl,
      Option.getD_some, hdc]
    omega
  · intro m r r' nr nr' hr hr' hc hc'
    obtain ⟨h1, rfl⟩ := recsOf_some hr
    obtain ⟨h2, rfl⟩ := recsOf_some hr'
    apply Classical.byContradiction; intro hne
    have := (kid_slots hw hb (vpos (vid0 es)) (n := m)).2 r r' h1 h2 hne
    simp only at hc hc'; omega
  · intro m r nr hr
    obtain ⟨h1, rfl⟩ := recsOf_some hr
    exact (kid_slots hw hb (vpos (vid0 es)) (n := m)).1 r h1
  · intro j r r' nr nr' hr hr' hj hj'
    obtain ⟨h1, rfl⟩ := recsOf_some hr
    obtain ⟨h2, rfl⟩ := recsOf_some hr'
    obtain ⟨vid, l, pre, po, w, hv, rfl⟩ := vids_toRec3 _ _ hj
    obtain ⟨vid', l', pre', po', w', hv', he⟩ := vids_toRec3 _ _ hj'
    have hlen := vlen_le hvw
    obtain ⟨t, ht, hti, -⟩ := val_link hw hvw hvb h1 hv
    obtain ⟨t', ht', hti', -⟩ := val_link hw hvw hvb h2 hv'
    have e1 := vpos_at hvw hlen ht
    have e2 := vpos_at hvw hlen ht'
    rw [hti] at e1; rw [hti'] at e2
    have htt : t = t' := by rw [← e1, ← e2, he]
    subst htt
    rw [hti] at hti'; subst hti'
    exact val_unique hw hvw hvb hlen h1 h2 hv hv'

end ZkFormal.NearV3.Link3
