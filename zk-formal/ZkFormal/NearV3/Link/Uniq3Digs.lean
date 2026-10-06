import ZkFormal.NearV3.Link.Uniq3Ent

/-!
# ZkFormal.NearV3.Link.Uniq3Digs — `DIGS`: the `uniq` entries are the digest windows

`DigsBal`: the `DIGS` messages sent by node-record windows (revealed kids, revealed values)
and by heads (root windows) are, as a multiset of `Fp` images, those `uniqV3` receives.

* `digs_send` — every `DIGS` send is `(E, τ, j, digNat (bOf E) [j])` (`kid_sha`, `val_sha`,
  `head_sha`): a window's bytes are the SHA-256 of the message bytes of its id;
* `uniq_bytes` — hence every `uniq` entry's digest bytes are `digNat (bOf eid)`;
* `uniq_of_send` — every window has a `uniq` entry with its id and instance;
* `uniq_len` — `|uniq| ≤ P` (≤ 17 windows per record, `|heads| ≤ |records|` by `PARENT`).
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

/-- The `DIGS` balance. -/
def DigsBal (vs : List NodeS3) (hs : List HeadE) (us : List UniqE) : Prop :=
  ((nodeSends3 vs B_DIGS ++ headSends hs B_DIGS).map Msg.toFp).Perm ((uniqRecvs us B_DIGS).map Msg.toFp)

/-- Digest bytes of the message of entry id `E`. -/
def dN (vs : List NodeS3) (es : List ValE) (E : Nat) : List Nat := digNat (bOf vs es E)

theorem dN_len (vs : List NodeS3) (es : List ValE) (E : Nat) : (dN vs es E).length = 32 := by
  simp [dN, digNat]

theorem dN_lt (vs : List NodeS3) (es : List ValE) (E : Nat) : ∀ y ∈ dN vs es E, y < 256 := by
  intro y hy
  simp only [dN, digNat, List.mem_map] at hy
  obtain ⟨b, -, rfl⟩ := hy; exact UInt8.toNat_lt b

/-- `DIGS` windows of one record. -/
def digsOf (s : NodeS3) : List Msg :=
  (s.v.revealed.flatMap fun (c, _, _, pre, _) =>
    (List.range 32).map fun i => [msgId K_NPRE c, s.tau, i, pre.getD i 0]) ++
  (match s.v.value with
   | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, s.tau, j, pre.getD j 0]
   | none => [])

/-- `DIGS` window of one head. -/
def digsH (h : HeadE) : List Msg := (List.range 32).map fun i => [msgId K_NPRE h.rid, h.tau, i, h.pre.getD i 0]

theorem digsN (vs : List NodeS3) :
    nodeSends3 vs B_DIGS = (vs.zip (List.range vs.length)).flatMap (fun x => digsOf x.1) := by
  simp [nodeSends3, digsOf, B_DIGS, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP] <;> rfl

theorem digsHs (hs : List HeadE) : headSends hs B_DIGS = hs.flatMap digsH := by
  simp [headSends, B_DIGS, B_PARENT, B_EDGE, B_MIDROOT] <;> rfl

theorem digsS (vs : List NodeS3) (hs : List HeadE) :
    nodeSends3 vs B_DIGS ++ headSends hs B_DIGS =
      (vs.zip (List.range vs.length)).flatMap (fun x => digsOf x.1) ++ hs.flatMap digsH := by
  rw [digsN, digsHs]

theorem digsR (us : List UniqE) :
    uniqRecvs us B_DIGS = us.flatMap fun e => (List.range 32).map fun j => [e.eid, e.tau, j, e.bytes.getD j 0] := by
  simp [uniqRecvs]

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- **Windows.** Every `DIGS` send is a digest byte of the message bytes of its id. -/
theorem digs_send (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {m : Msg}
    (hm : m ∈ nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) :
    ∃ E τ' j, E < P ∧ τ' < P ∧ j < 32 ∧ m = [E, τ', j, (dN vs es E).getD j 0] := by
  have hvl := vlen_le hvw
  rw [digsS, List.mem_append] at hm
  rcases hm with hm | hm
  · rw [List.mem_flatMap] at hm
    obtain ⟨⟨s, p⟩, hsp, hm⟩ := hm
    obtain ⟨hp, rfl⟩ := mem_zip_range hsp
    have tp := (hw.small _ (List.getElem_mem hp)).1
    simp only [digsOf] at hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_flatMap] at hm
      obtain ⟨⟨c, l, r, pre, po⟩, hk, hm⟩ := hm
      rw [List.mem_map] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      obtain ⟨hc, -, hpre⟩ := kid_sha hw hhw hvw hb H hp hk
      refine ⟨msgId K_NPRE c, vs[p].tau, i, nid_lt hw hc K_NPRE (by decide), tp, List.mem_range.1 hi, ?_⟩
      rw [dN, bOf, bN_node vs es hc, digNat, ← hpre]
    · cases hv : vs[p].v.value with
      | none => rw [hv] at hm; simp at hm
      | some x =>
        obtain ⟨i, l, pre, po, w⟩ := x
        rw [hv] at hm
        simp only [List.mem_map] at hm
        obtain ⟨j, hj, rfl⟩ := hm
        obtain ⟨t, ht, hpos, hi, -, hV⟩ := val_pos hw hvw hvb hvl hp hv
        have hvt := vid_small hvw ht
        rw [hvt] at hi; subst hi
        obtain ⟨-, hpre⟩ := val_sha hw hhw hvw hvb H hp hv
        rw [hpos] at hpre
        have hval : valOf (valsOf3 vs es) t = toB es[t].bytes := by simp [valOf, hV]
        rw [hval] at hpre
        refine ⟨msgId K_VPRE t, vs[p].tau, j, by unfold msgId K_VPRE P; omega, tp, List.mem_range.1 hj, ?_⟩
        rw [dN, bOf, bN_val vs es ht, digNat, ← hpre]
  · rw [List.mem_flatMap] at hm
    obtain ⟨h, hh, hm⟩ := hm
    rw [digsH, List.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    obtain ⟨hr, -, hpre⟩ := head_sha hw hhw hvw hb H hh
    refine ⟨msgId K_NPRE h.rid, h.tau, i, nid_lt hw hr K_NPRE (by decide), (hhw.canon h hh).1,
      List.mem_range.1 hi, ?_⟩
    rw [dN, bOf, bN_node vs es hr, digNat, ← hpre]

/-- **Digest bytes of `uniq` entries.** -/
theorem uniq_bytes (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) {e : UniqE} (he : e ∈ us) : e.bytes = dN vs es e.eid := by
  have ce := huw.canon e he
  have hl := huw.len e he
  have hj : ∀ j, j < 32 → e.bytes.getD j 0 = (dN vs es e.eid).getD j 0 := by
    intro j hjl
    have hm : [e.eid, e.tau, j, e.bytes.getD j 0] ∈ uniqRecvs us B_DIGS := by
      rw [digsR, List.mem_flatMap]
      exact ⟨e, he, List.mem_map.2 ⟨j, List.mem_range.2 hjl, rfl⟩⟩
    have h1 := List.mem_map_of_mem (f := Msg.toFp) hm
    rw [← hD.mem_iff, List.mem_map] at h1
    obtain ⟨m, hm', hme⟩ := h1
    obtain ⟨E, τ', j', hE, -, hj', rfl⟩ := digs_send hw hhw hvw hb hvb H hm'
    simp only [toFp4, List.cons.injEq] at hme
    obtain ⟨e1, -, e3, e4, -⟩ := hme
    have e1' : E = e.eid := ofNat_eq hE ce.1 e1
    have e3' : j' = j := ofNat_eq (by unfold P; omega) (by unfold P; omega) e3
    subst e1' e3'
    have hd : (dN vs es e.eid).getD j' 0 < P := by
      rw [getD_get (by rw [dN_len]; exact hj')]
      have := dN_lt vs es e.eid _ (List.getElem_mem (by rw [dN_len]; exact hj')); unfold P; omega
    have hbP : e.bytes.getD j' 0 < P := by
      rw [getD_get (by rw [hl]; exact hj')]; exact ce.2.2.2.2.2 _ (List.getElem_mem _)
    exact (ofNat_eq hd hbP e4).symm
  apply List.ext_getElem (by rw [hl, dN_len])
  intro j h1 h2
  have := hj j (by rw [hl] at h1; exact h1)
  rwa [getD_get h1, getD_get h2] at this

theorem uniq_byte_lt (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) : ∀ e ∈ us, ∀ y ∈ e.bytes, y < 256 := by
  intro e he y hy
  rw [uniq_bytes hw hhw hvw huw hb hvb H hD he] at hy
  exact dN_lt vs es _ y hy

/-- **Every window has a `uniq` entry** with its id and instance. -/
theorem uniq_of_send (huw : UniqWf us) (hD : DigsBal vs hs us) {E τ' : Nat} {r : List Nat}
    (hE : E < P) (hτ : τ' < P) (hm : E :: τ' :: r ∈ nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) :
    ∃ e ∈ us, e.eid = E ∧ e.tau = τ' := by
  have h1 := List.mem_map_of_mem (f := Msg.toFp) hm
  rw [hD.mem_iff, List.mem_map, digsR, ] at h1
  obtain ⟨m, hm', hme⟩ := h1
  rw [List.mem_flatMap] at hm'
  obtain ⟨e, he, hm'⟩ := hm'
  rw [List.mem_map] at hm'
  obtain ⟨j, -, rfl⟩ := hm'
  have ce := huw.canon e he
  simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hme
  exact ⟨e, he, ofNat_eq ce.1 hE hme.1, ofNat_eq ce.2.2.1 hτ hme.2.1⟩

/-! ## The `uniq` table is short -/

theorem len_flatMap_le {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length ≤ k) → (l.flatMap f).length ≤ k * l.length
  | [], _ => by simp
  | a :: l, h => by
    have ih := len_flatMap_le f k l (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

theorem len_flatMap_eq {α β : Type} (f : α → List β) (k : Nat) (hf : ∀ x, (f x).length = k) :
    ∀ (l : List α), (l.flatMap f).length = k * l.length
  | [] => by simp
  | a :: l => by
    have ih := len_flatMap_eq f k hf l
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ, hf a]
    omega

theorem revealed_len {v : NodeV3} (hv : v.wf) : v.revealed.length ≤ 16 := by
  cases v with
  | leaf => simp [NodeV3.revealed]
  | ext k kid m => cases kid <;> simp [NodeV3.revealed]
  | branch sv kids m =>
    simp only [NodeV3.revealed]
    exact Nat.le_trans (List.length_filterMap_le _ _) (Nat.le_of_eq hv.1)

theorem heads_le (hb : ParentBal vs hs) : hs.length ≤ vs.length := by
  have hp : ((nodeSends3 vs B_PARENT ++ headSends hs B_PARENT).map Msg.toFp).Perm
      ((nodeRecvs3 vs B_PARENT).map Msg.toFp) := List.perm_iff_count.2 (fun m => hb m)
  have := hp.length_eq
  simp only [List.length_map, List.length_append, parentR, headS, List.length_zip,
    List.length_range, Nat.min_self] at this
  omega

theorem uniq_len (hw : NodeWf3 vs) (hb : ParentBal vs hs) (hD : DigsBal vs hs us) : us.length ≤ P := by
  have h1 := hD.length_eq
  have hu : (uniqRecvs us B_DIGS).length = 32 * us.length := by
    rw [digsR]; exact len_flatMap_eq _ 32 (by simp) us
  have hh : (headSends hs B_DIGS).length = 32 * hs.length := by
    rw [digsHs]; exact len_flatMap_eq _ 32 (by simp [digsH]) hs
  have hn : (nodeSends3 vs B_DIGS).length ≤ (32 * 16 + 32) * vs.length := by
    rw [digsN]
    have hz : (vs.zip (List.range vs.length)).length = vs.length := by simp
    refine Nat.le_trans (len_flatMap_le _ (32 * 16 + 32) _ ?_) (Nat.le_of_eq (by rw [hz]))
    intro x hx
    obtain ⟨hn, hx1⟩ := mem_zip_range (x := x.1) (n := x.2) hx
    have hr := revealed_len (hw.wf _ (List.getElem_mem hn))
    rw [hx1] at hr
    unfold digsOf
    rw [List.length_append, len_flatMap_eq _ 32 (by simp)]
    have : 32 * x.1.v.revealed.length ≤ 32 * 16 := Nat.mul_le_mul_left _ hr
    split <;> simp <;> omega
  rw [List.length_map, List.length_map, List.length_append, hu, hh] at h1
  have h3 := heads_le hb
  have h4 := hw.count
  unfold P; omega

end ZkFormal.NearV3.Link3
