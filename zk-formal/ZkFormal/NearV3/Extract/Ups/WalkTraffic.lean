import ZkFormal.NearV3.Extract.Ups.Walk

/-!
# ZkFormal.NearV3.Extract.Ups.WalkTraffic — the `EDGE` / `BMAP` traffic of a segment (layer 2)

The `EDGE` and `BMAP` messages of an `upsV3` segment are exactly `walkV3`'s traffic of its walk
`upsWalk s` (`walkSends3` / `walkRecvs3 [upsWalk s]`): the walk rows `W0 … W3` send and receive
them by mode (step / absent by key on `EDGE`, absent at a branch on `BMAP`), and value and node
rows send none.  So the chained-provider argument of the `walkV3` link (`Link/Walk3Prov`)
applies to `upsV3`'s walk unchanged.

Two forms:
* `ups_walkTrafficFp` (no hypothesis): equality after `Msg.toFp`, the form the `walkV3` link
  (`Link/Walk3Prov`, `.map Msg.toFp` permutations) consumes; there the row's sent use count
  `(u + 1) mod P` and `walkV3`'s unreduced `u + 1` agree.
* `ups_walkTraffic` (exact, over `ℕ`): needs `u + 1 < P` on the walk rows (`hu`).  `u` is
  canonical (`< P`), so this only excludes `u = P − 1`.  It comes from the chained-provider
  count in the link: the use counts on one `EDGE`/`BMAP` record's chain are `0, 1, …, n − 1`
  with `n` the record's number of consumers, which is at most the total number of consumer
  rows (`≤ 2^22 + 2^21 < P`).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem flatMap_ite_filter {α β : Type} (f : Nat → α) (p : α → Bool) (m : α → β) :
    ∀ l : List Nat, l.flatMap (fun i => if p (f i) then [m (f i)] else []) = ((l.map f).filter p).map m
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.map_cons, List.filter_cons, flatMap_ite_filter f p m l]
    split <;> simp

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a List.mem_cons_self, flatMap_congr' (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem ofNat_modP (n : Nat) : Fp.ofNat (n % P) = Fp.ofNat n := by
  rw [← Fp.toNat_inj, Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_mod]

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw hs hL

omit hw hs in
/-- Rows after the walk send nothing on `EDGE` / `BMAP`. -/
theorem quietWalkBus {i : Nat} (h4 : 4 ≤ i) (hi : i < s.rows.length) {bb : Nat} (hb : bb = B_EDGE ∨ bb = B_BMAP)
    (sd : Bool) : uMsgs (s.row i) (s.next i) bb sd = [] := by
  rcases Nat.lt_or_ge i (4 + L) with h | h
  · have := hL.msgsV (i - 4) (by omega) bb sd
    rw [show 4 + (i - 4) = i by omega] at this
    rw [this]
    rcases hb with rfl | rfl <;> simp [B_SPOST, B_BYTES, B_EDGE, B_BMAP]
  · rw [hL.msgsQ i h hi bb sd]
    rcases hb with rfl | rfl <;> simp [B_DIGEST, B_BYTES, B_UPB, B_MEMD, B_EDGE, B_BMAP]

/-- One walk row's `EDGE` / `BMAP` messages, as its `walkV3` step's (the sent use count reduced
mod `P`). -/
theorem walkRowBus {i : Nat} (hi : i < 4) :
    uMsgs (s.row i) (s.next i) B_EDGE true =
      (if decide ((stepOf (s.row i) i).mode ≤ 1) then
        [(stepOf (s.row i) i).edgeMsg (((stepOf (s.row i) i).u + 1) % P)] else []) ∧
    uMsgs (s.row i) (s.next i) B_EDGE false =
      (if decide ((stepOf (s.row i) i).mode ≤ 1) then [(stepOf (s.row i) i).edgeMsg (stepOf (s.row i) i).u] else []) ∧
    uMsgs (s.row i) (s.next i) B_BMAP true =
      (if decide ((stepOf (s.row i) i).mode = 2) then
        [(stepOf (s.row i) i).bmapMsg (((stepOf (s.row i) i).ub + 1) % P)] else []) ∧
    uMsgs (s.row i) (s.next i) B_BMAP false =
      (if decide ((stepOf (s.row i) i).mode = 2) then [(stepOf (s.row i) i).bmapMsg (stepOf (s.row i) i).ub] else []) := by
  have F := wRowF hw hs hL i hi
  have M := mode_cases F.modes i
  obtain ⟨b1, b2, b3, bs, -⟩ := F.modes
  have hm1 : (stepOf (s.row i) i).mode ≤ 1 ↔ s.row i mS + s.row i mK = 1 := by
    constructor
    · intro h
      rcases (show (stepOf (s.row i) i).mode = 0 ∨ (stepOf (s.row i) i).mode = 1 by omega) with h | h
      · have := M.1.1 h; omega
      · have := M.2.1.1 h; omega
    · intro h
      rcases (show s.row i mS = 1 ∨ s.row i mK = 1 by omega) with h | h
      · have := M.1.2 h; omega
      · have := M.2.1.2 h; omega
  have hm2 : (stepOf (s.row i) i).mode = 2 ↔ s.row i mB = 1 := M.2.2.1
  have W := fun bb sd => hL.msgsW i hi bb sd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [W]
  · by_cases h : s.row i mS + s.row i mK = 1
    · have h' := hm1.2 h
      rw [decide_eq_true h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, stepOf, WStep3.edgeMsg]
    · have h' : ¬ (stepOf (s.row i) i).mode ≤ 1 := fun h' => h (hm1.1 h')
      rw [decide_eq_false h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]
  · by_cases h : s.row i mS + s.row i mK = 1
    · have h' := hm1.2 h
      rw [decide_eq_true h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, stepOf, WStep3.edgeMsg]
    · have h' : ¬ (stepOf (s.row i) i).mode ≤ 1 := fun h' => h (hm1.1 h')
      rw [decide_eq_false h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]
  · by_cases h : s.row i mB = 1
    · have h' := hm2.2 h
      rw [decide_eq_true h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, stepOf, WStep3.bmapMsg]
    · have h' : ¬ (stepOf (s.row i) i).mode = 2 := fun h' => h (hm2.1 h')
      rw [decide_eq_false h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]
  · by_cases h : s.row i mB = 1
    · have h' := hm2.2 h
      rw [decide_eq_true h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, stepOf, WStep3.bmapMsg]
    · have h' : ¬ (stepOf (s.row i) i).mode = 2 := fun h' => h (hm2.1 h')
      rw [decide_eq_false h']
      simp [h, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]

/-- The bus traffic of a segment is that of its walk rows. -/
theorem msgs_walkBus {bb : Nat} (hb : bb = B_EDGE ∨ bb = B_BMAP) (sd : Bool) :
    s.msgs bb sd = (List.range 4).flatMap fun i => uMsgs (s.row i) (s.next i) bb sd := by
  have h4 := hL.walk.1
  unfold UpsSeg.msgs
  rw [show s.rows.length = 4 + (s.rows.length - 4) by omega, List.range_add, List.flatMap_append]
  rw [show (List.map (fun x => 4 + x) (List.range (s.rows.length - 4))).flatMap
      (fun i => uMsgs (s.row i) (s.next i) bb sd) = [] by
    rw [List.flatMap_eq_nil_iff]
    intro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨d, hd, rfl⟩ := hi
    exact quietWalkBus hL (by omega) (by omega) hb sd, List.append_nil]


/-- The walk rows' receives (no hypothesis). -/
theorem ups_walkTrafficE :
    (List.range 4).flatMap (fun i => uMsgs (s.row i) (s.next i) B_EDGE false) = walkRecvs3 [upsWalk s] B_EDGE ∧
    (List.range 4).flatMap (fun i => uMsgs (s.row i) (s.next i) B_BMAP false) = walkRecvs3 [upsWalk s] B_BMAP := by
  have R := fun i (hi : i < 4) => walkRowBus hw hs hL hi
  have hEB : (B_BMAP = B_EDGE) = False := by simp [B_BMAP, B_EDGE]
  refine ⟨?_, ?_⟩
  · simp only [walkRecvs3, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode ≤ 1)) (fun st => st.edgeMsg st.u)]
    apply flatMap_congr'; intro i hi; exact (R i (List.mem_range.mp hi)).2.1
  · simp only [walkRecvs3, hEB, if_false, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode = 2)) (fun st => st.bmapMsg st.ub)]
    apply flatMap_congr'; intro i hi; exact (R i (List.mem_range.mp hi)).2.2.2

/-- **The walk traffic of a segment** (`EDGE`, `BMAP`): `upsV3`'s messages on these buses are
`walkV3`'s view traffic `walkSends3` / `walkRecvs3` of the walk `upsWalk s`. -/
theorem ups_walkTraffic (hu : ∀ i, i < 4 → s.row i u + 1 < P) :
    s.msgs B_EDGE true = walkSends3 [upsWalk s] B_EDGE ∧ s.msgs B_EDGE false = walkRecvs3 [upsWalk s] B_EDGE ∧
    s.msgs B_BMAP true = walkSends3 [upsWalk s] B_BMAP ∧ s.msgs B_BMAP false = walkRecvs3 [upsWalk s] B_BMAP := by
  have R := fun i (hi : i < 4) => walkRowBus hw hs hL hi
  have hP := fun i (hi : i < 4) => Nat.mod_eq_of_lt (hu i hi)
  have hEB : (B_BMAP = B_EDGE) = False := by simp [B_BMAP, B_EDGE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [msgs_walkBus hw hs hL (Or.inl rfl)]
    simp only [walkSends3, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode ≤ 1)) (fun st => st.edgeMsg (st.u + 1))]
    apply flatMap_congr'; intro i hi; rw [(R i (List.mem_range.mp hi)).1, show ((stepOf (s.row i) i).u + 1) % P = (stepOf (s.row i) i).u + 1 from
      hP i (List.mem_range.mp hi)]
  · rw [msgs_walkBus hw hs hL (Or.inl rfl)]
    simp only [walkRecvs3, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode ≤ 1)) (fun st => st.edgeMsg st.u)]
    apply flatMap_congr'; intro i hi; exact (R i (List.mem_range.mp hi)).2.1
  · rw [msgs_walkBus hw hs hL (Or.inr rfl)]
    simp only [walkSends3, hEB, if_false, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode = 2)) (fun st => st.bmapMsg (st.ub + 1))]
    apply flatMap_congr'; intro i hi; rw [(R i (List.mem_range.mp hi)).2.2.1, show ((stepOf (s.row i) i).ub + 1) % P = (stepOf (s.row i) i).ub + 1 from
      hP i (List.mem_range.mp hi)]
  · rw [msgs_walkBus hw hs hL (Or.inr rfl)]
    simp only [walkRecvs3, hEB, if_false, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode = 2)) (fun st => st.bmapMsg st.ub)]
    apply flatMap_congr'; intro i hi; exact (R i (List.mem_range.mp hi)).2.2.2

/-- **The walk traffic of a segment, over `Fp`** (no hypothesis): the link compares messages
after `Msg.toFp`, where the sent use count `u + 1` and its reduction mod `P` agree. -/
theorem ups_walkTrafficFp :
    (s.msgs B_EDGE true).map Msg.toFp = (walkSends3 [upsWalk s] B_EDGE).map Msg.toFp ∧
    (s.msgs B_EDGE false).map Msg.toFp = (walkRecvs3 [upsWalk s] B_EDGE).map Msg.toFp ∧
    (s.msgs B_BMAP true).map Msg.toFp = (walkSends3 [upsWalk s] B_BMAP).map Msg.toFp ∧
    (s.msgs B_BMAP false).map Msg.toFp = (walkRecvs3 [upsWalk s] B_BMAP).map Msg.toFp := by
  have R := fun i (hi : i < 4) => walkRowBus hw hs hL hi
  have hEB : (B_BMAP = B_EDGE) = False := by simp [B_BMAP, B_EDGE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [msgs_walkBus hw hs hL (Or.inl rfl)]
    simp only [walkSends3, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode ≤ 1)) (fun st => st.edgeMsg (st.u + 1)),
      List.map_flatMap, List.map_flatMap]
    apply flatMap_congr'; intro i hi
    rw [(R i (List.mem_range.mp hi)).1]
    split <;> simp [Msg.toFp, WStep3.edgeMsg] <;> exact ofNat_modP _
  · rw [msgs_walkBus hw hs hL (Or.inl rfl), (ups_walkTrafficE hw hs hL).1]
  · rw [msgs_walkBus hw hs hL (Or.inr rfl)]
    simp only [walkSends3, hEB, if_false, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, upsWalk]
    rw [← flatMap_ite_filter (fun i => stepOf (s.row i) i) (fun st => decide (st.mode = 2)) (fun st => st.bmapMsg (st.ub + 1)),
      List.map_flatMap, List.map_flatMap]
    apply flatMap_congr'; intro i hi
    rw [(R i (List.mem_range.mp hi)).2.2.1]
    split <;> simp [Msg.toFp, WStep3.bmapMsg] <;> exact ofNat_modP _
  · rw [msgs_walkBus hw hs hL (Or.inr rfl), (ups_walkTrafficE hw hs hL).2]

end

end ZkFormal.NearV3.UpsRows
