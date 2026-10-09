import ZkFormal.NearV3.Link.Walk3Chain

/-!
# ZkFormal.NearV3.Link.Walk3Prov — every `EDGE` / `BMAP` message a walk uses is provided

From `EDGE` (resp. `BMAP`) balance between `nodeV3`, `headV3` and `walkV3`:

* `edge_provided3` — an edge of a step / absent-by-key row is an edge `edgesOf3 n vs[n]`
  of a node record, or the `START` edge of a head;
* `bmap_provided3` — the `BMAP` message of an absent-at-branch row is that of a branch
  record `n = e[0]`.

Besides the views' local facts this needs two size facts: the total number of walk rows
is below `p` (`hT`, v1's `WalkLen`), and leaf / extension keys are shorter than `p`
(`hkl`, so that key-edge positions `i + 1` are canonical).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Walk3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3

/-- Key length of a record (`0` for a branch). -/
def klen3 : NodeV3 → Nat
  | .leaf k _ _ => k.length
  | .ext k _ _ => k.length
  | .branch .. => 0

theorem P_big : 2 ^ 22 < P := by unfold P; omega

theorem mem_keyEdges3 {n : Nat} {k : List Nat} {e : Msg} :
    e ∈ keyEdges3 n k ↔ ∃ i, i < k.length ∧ e = [n, i, k.getD i 0, n, i + 1, EK_KEY] := by
  simp only [keyEdges3, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem getD_mem_or {l : List Nat} (i : Nat) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => right; rfl
  | some y => left; exact List.mem_of_getElem? h

/-- Node edges: length 6, canonical, start at `n`, symbol `≤ END`. -/
theorem edges3_canon (n : Nat) (s : NodeS3) (hn : n < P) (hraw : ∀ x ∈ s.v.raw, x < P)
    (hk : klen3 s.v < P) (hwf : s.v.wf) :
    ∀ e ∈ edgesOf3 n s, e.length = 6 ∧ Canon e ∧ e.getD 0 0 = n ∧ e.getD 2 0 ≤ SYM_END := by
  have hP : (19 : Nat) < P := by unfold P; omega
  have hE : SYM_END = 16 := rfl
  have hkey : ∀ {k : List Nat} {i : Nat}, (∀ x ∈ k, x < 16) → i < k.length → k.length < P →
      ∀ e, e = [n, i, k.getD i 0, n, i + 1, EK_KEY] →
        e.length = 6 ∧ Canon e ∧ e.getD 0 0 = n ∧ e.getD 2 0 ≤ SYM_END := by
    intro k i hkr hi hkl e he; subst he
    have hg : k.getD i 0 < 16 := by
      rcases getD_mem_or (l := k) i with h | h
      · exact hkr _ h
      · rw [h]; omega
    refine ⟨rfl, fun x hx => ?_, rfl, by show k.getD i 0 ≤ 16; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold EK_KEY; omega)
  intro e he
  unfold edgesOf3 at he
  generalize hv : s.v = v at hraw hk he hwf
  cases v with
  | leaf k sl m =>
    simp only [klen3] at hk
    have hkr : ∀ x ∈ k, x < 16 := hwf.1
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_keyEdges3.mp he; exact hkey hkr hi hk _ rfl
      · cases sl with
        | val lenB i l pre po w =>
          simp only [List.mem_singleton] at he; subst he
          have hi : i < P := hraw i (by simp [NodeV3.raw, NSlot3.raw])
          refine ⟨rfl, fun x hx => ?_, rfl, Nat.le_refl SYM_END⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | omega | (unfold EK_VAL; omega) | (unfold SYM_END; omega)
        | ref => simp at he
    · simp only [List.mem_singleton] at he; subst he
      refine ⟨rfl, fun x hx => ?_, rfl, Nat.le_refl SYM_END⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | omega | (unfold EK_LEND; omega) | (unfold SYM_END; omega)
  | ext k kid m =>
    simp only [klen3] at hk
    have hkr : ∀ x ∈ k, x < 16 := hwf.1
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, rfl⟩ := mem_keyEdges3.mp he
      have hgd : k.dropLast.getD i 0 = k.getD i 0 := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_dropLast]; simp only [List.length_dropLast] at hi; simp [hi]
      rw [hgd]
      simp only [List.length_dropLast] at hi
      have := hkey hkr (show i < k.length by omega) hk [n, i, k.getD i 0, n, i + 1, EK_KEY] rfl
      exact this
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        have hx : x ∈ k := List.mem_of_getLast? hl
        have hx16 := hkr x hx
        have hkpos : 0 < k.length := List.length_pos_of_mem hx
        cases kid with
        | node c1 c2 cr p1 p2 =>
          simp only [hl, List.mem_singleton] at he; subst he
          have hcr : cr < P := hraw cr (by simp [NodeV3.raw, NKid.raw])
          refine ⟨rfl, fun y hy => ?_, rfl, by show x ≤ 16; omega⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold EK_KEY; omega)
        | none =>
          simp only [hl, List.mem_singleton] at he; subst he
          refine ⟨rfl, fun y hy => ?_, rfl, by show x ≤ 16; omega⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold EK_KEY; omega)
        | hash h =>
          simp only [hl, List.mem_singleton] at he; subst he
          refine ⟨rfl, fun y hy => ?_, rfl, by show x ≤ 16; omega⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold EK_KEY; omega)
  | branch sv kids m =>
    rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨kd, j⟩, hp, hm⟩ := List.mem_filterMap.mp he
      obtain ⟨hj, hkd⟩ := mem_zip_range.mp hp
      have hl16 : kids.length = 16 := hwf.1
      cases kd with
      | node c1 c2 cr p1 p2 =>
        simp only [Option.some.injEq] at hm; subst hm
        have hcr : cr < P := hraw cr (by
          simp only [NodeV3.raw, List.mem_append, List.mem_flatMap]
          left; right
          exact ⟨_, List.getElem_mem hj, by rw [hkd]; simp [NKid.raw]⟩)
        refine ⟨rfl, fun y hy => ?_, rfl, by show j ≤ 16; omega⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold EK_DOWN; omega)
      | none => simp at hm
      | hash => simp at hm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton] at he; subst he
        have hi : i < P := hraw i (by simp [NodeV3.raw, NSlot3.raw])
        refine ⟨rfl, fun x hx => ?_, rfl, Nat.le_refl SYM_END⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (unfold EK_VAL; omega) | (unfold SYM_END; omega)

theorem flatMap_map_eq {α β γ : Type} (s : α → List β) (G : β → γ) :
    ∀ (l : List α), l.flatMap (fun a => (s a).map G) = (l.flatMap s).map G
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.flatMap_cons, List.map_append, flatMap_map_eq s G l]

theorem flatMap_filter_len {β : Type} (p : WStep3 → Bool) (g : WStep3 → β) : ∀ (ws : List WalkR),
    (ws.flatMap fun wv => (wv.steps.filter p).map g).length ≤ (ws.flatMap (·.steps)).length
  | [] => by simp
  | wv :: ws => by
    have := flatMap_filter_len p g ws
    have := List.length_filter_le p wv.steps
    simp only [List.flatMap_cons, List.length_append, List.length_map]; omega

theorem stepOk_of_mem {wv : WalkR} {ws : List WalkR} (hW : WalkWf3 ws) (hw : wv ∈ ws)
    {st : WStep3} (hst : st ∈ wv.steps) : ∃ b, StepOk st b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hst
  exact ⟨_, hW.rows wv hw i hi⟩

/-- The balance hypotheses (`Fp` images of the traffic are permutations of each other). -/
def BusBal (vs : List NodeS3) (hs : List HeadE) (ws : List WalkR) (b : Nat) : Prop :=
  ((nodeSends3 vs b ++ headSends hs b ++ walkSends3 ws b).map Msg.toFp).Perm
    ((nodeRecvs3 vs b ++ headRecvs hs b ++ walkRecvs3 ws b).map Msg.toFp)

section Prov
variable {vs : List NodeS3} {hs : List HeadE} {ws : List WalkR}

theorem nodeSends3_edge (vs : List NodeS3) : nodeSends3 vs B_EDGE =
    (vs.zip (List.range vs.length)).flatMap fun (s, n) => (edgesOf3 n s).map (· ++ [0]) := by
  simp [nodeSends3, B_EDGE, B_BYTES, B_PARENT, B_VPARENT]

theorem nodeRecvs3_edge (vs : List NodeS3) : nodeRecvs3 vs B_EDGE =
    (vs.zip (List.range vs.length)).flatMap fun (s, n) => ((edgesOf3 n s).zip s.uses).map fun (e, u) => e ++ [u] := by
  simp [nodeRecvs3, B_EDGE, B_DIGEST, B_PARENT]

theorem walkSends3_edge (ws : List WalkR) : walkSends3 ws B_EDGE =
    (ws.flatMap fun wv => (wv.steps.filter fun st => st.mode ≤ 1).map fun st => (st.e, st.u)).map
      fun s => s.1 ++ [s.2 + 1] := by
  simp only [walkSends3, if_pos rfl]
  rw [← flatMap_map_eq]; simp [WStep3.edgeMsg, Function.comp_def]

theorem walkRecvs3_edge (ws : List WalkR) : walkRecvs3 ws B_EDGE =
    (ws.flatMap fun wv => (wv.steps.filter fun st => st.mode ≤ 1).map fun st => (st.e, st.u)).map
      fun s => s.1 ++ [s.2] := by
  simp only [walkRecvs3, if_pos rfl]
  rw [← flatMap_map_eq]; simp [WStep3.edgeMsg, Function.comp_def]

theorem headSends_edge (hs : List HeadE) : headSends hs B_EDGE = hs.map fun h => startEdgeMsg h 0 := by
  simp [headSends, B_EDGE, B_MIDROOT, B_PARENT]

theorem headRecvs_edge (hs : List HeadE) : headRecvs hs B_EDGE = hs.map fun h => startEdgeMsg h h.mE := by
  simp [headRecvs, B_EDGE, B_DIGEST, B_ROOT]

/-- **Every edge a walk row uses is provided** (by a node record or a head). -/
theorem edge_provided3 (hN : NodeWf3 vs) (hH : HeadWf hs) (hW : WalkWf3 ws)
    (hbal : BusBal vs hs ws B_EDGE) (hT : (ws.flatMap (·.steps)).length < P)
    (hkl : ∀ s ∈ vs, klen3 s.v < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode ≤ 1) :
    (∃ n, ∃ hn : n < vs.length, st.e ∈ edgesOf3 n vs[n]) ∨
      ∃ h ∈ hs, st.e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] := by
  apply Classical.byContradiction; intro hno
  have hno1 : ∀ n (hn : n < vs.length), st.e ∉ edgesOf3 n vs[n] :=
    fun n hn he => hno (Or.inl ⟨n, hn, he⟩)
  have hno2 : ∀ h ∈ hs, st.e ≠ [0, h.tau, SYM_START, h.rres, 0, EK_DOWN] :=
    fun h hh he => hno (Or.inr ⟨h, hh, he⟩)
  obtain ⟨b, hok⟩ := stepOk_of_mem hW hw hst
  have hcanW := hW.canon wv hw
  have hec : Canon st.e := (hcanW.2.2 st hst).2.2.2
  have hcount := hN.count
  have hP := P_big
  unfold BusBal at hbal
  rw [nodeSends3_edge, nodeRecvs3_edge, headSends_edge, headRecvs_edge, walkSends3_edge,
    walkRecvs3_edge] at hbal
  refine chain_provided (k := 6) _ _ _ st.e ?_ ?_ ?_ hok.elen hec (u := st.u) ?_ hbal
  · intro m hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · rcases List.mem_append.mp hm' with hm' | hm'
      · obtain ⟨⟨s, n⟩, hp, hm'⟩ := List.mem_flatMap.mp hm'
        obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm'
        have hsm := List.getElem_mem hn
        obtain ⟨h6, hc, -, -⟩ := edges3_canon n vs[n] (by omega) (hN.canon _ hsm) (hkl _ hsm)
          (hN.wf _ hsm) e' he'
        exact ⟨e', 0, rfl, h6, hc, fun he => hno1 n hn (he ▸ he')⟩
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm'
        have hc := hH.canon h hh
        refine ⟨[0, h.tau, SYM_START, h.rres, 0, EK_DOWN], 0, rfl, rfl, ?_, fun he => hno2 h hh he.symm⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (unfold SYM_START P; omega) | (unfold EK_DOWN P; omega)
    · rcases List.mem_append.mp hm' with hm' | hm'
      · obtain ⟨⟨s, n⟩, hp, hm'⟩ := List.mem_flatMap.mp hm'
        obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
        obtain ⟨⟨e', u⟩, he', rfl⟩ := List.mem_map.mp hm'
        have he'' := (List.of_mem_zip he').1
        have hsm := List.getElem_mem hn
        obtain ⟨h6, hc, -, -⟩ := edges3_canon n vs[n] (by omega) (hN.canon _ hsm) (hkl _ hsm)
          (hN.wf _ hsm) e' he''
        exact ⟨e', u, rfl, h6, hc, fun he => hno1 n hn (he ▸ he'')⟩
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm'
        have hc := hH.canon h hh
        refine ⟨[0, h.tau, SYM_START, h.rres, 0, EK_DOWN], h.mE, rfl, rfl, ?_, fun he => hno2 h hh he.symm⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (unfold SYM_START P; omega) | (unfold EK_DOWN P; omega)
  · intro s hs
    obtain ⟨wv', hw', hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hs'
    have hst'' := (List.mem_filter.mp hst').1
    obtain ⟨b', hok'⟩ := stepOk_of_mem hW hw' hst''
    have hc' := (hW.canon wv' hw').2.2 st' hst''
    exact ⟨hok'.elen, hc'.2.2.2, hc'.2.1⟩
  · have := flatMap_filter_len (fun st : WStep3 => decide (st.mode ≤ 1)) (fun st => (st.e, st.u)) ws
    omega
  · exact List.mem_flatMap.mpr ⟨wv, hw, List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hm⟩, rfl⟩⟩

theorem mem_nodeBmap {vs : List NodeS3} {m : Msg}
    (hm : m ∈ nodeSends3 vs B_BMAP ∨ m ∈ nodeRecvs3 vs B_BMAP) :
    ∃ n, ∃ hn : n < vs.length, ∃ bm hv x, vs[n].v.bmap = some (bm, hv) ∧ m = [n, bm, hv] ++ [x] := by
  rcases hm with hm | hm
  · simp [nodeSends3, B_EDGE, B_BYTES, B_PARENT, B_VPARENT, B_BMAP] at hm
    obtain ⟨s, n, hp, hm⟩ := hm
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
    rcases hb : vs[n].v.bmap with _ | ⟨bm, hv⟩ <;> simp only [hb, List.mem_singleton] at hm
    · simp at hm
    · exact ⟨n, hn, bm, hv, 0, hb, hm⟩
  · simp [nodeRecvs3, B_EDGE, B_DIGEST, B_PARENT, B_BMAP] at hm
    obtain ⟨s, n, hp, hm⟩ := hm
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
    rcases hb : vs[n].v.bmap with _ | ⟨bm, hv⟩ <;> simp only [hb, List.mem_singleton] at hm
    · simp at hm
    · exact ⟨n, hn, bm, hv, _, hb, hm⟩

theorem walkSends3_bmap (ws : List WalkR) : walkSends3 ws B_BMAP =
    (ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 2).map
      fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)).map fun s => s.1 ++ [s.2 + 1] := by
  simp only [walkSends3, B_EDGE, B_BMAP, show (11 : Nat) ≠ 4 from by decide, if_false, if_true]
  rw [← flatMap_map_eq]; simp [WStep3.bmapMsg, Function.comp_def]

theorem walkRecvs3_bmap (ws : List WalkR) : walkRecvs3 ws B_BMAP =
    (ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 2).map
      fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)).map fun s => s.1 ++ [s.2] := by
  simp only [walkRecvs3, B_EDGE, B_BMAP, show (11 : Nat) ≠ 4 from by decide, if_false, if_true]
  rw [← flatMap_map_eq]; simp [WStep3.bmapMsg, Function.comp_def]

theorem bmap_canon {kids : List NKid} (h16 : kids.length = 16) (n : Nat) (hn : n < P) (v : Option NSlot3) :
    Canon [n, kidBitmap kids, if v.isSome then 1 else 0] := by
  have := kidBitmap_lt h16
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hn
  · unfold P; omega
  · split <;> (unfold P; omega)

/-- **Every `BMAP` message of an absent-at-branch row is a branch record's.** -/
theorem bmap_provided3 (hN : NodeWf3 vs) (hW : WalkWf3 ws)
    (hbal : BusBal vs hs ws B_BMAP) (hT : (ws.flatMap (·.steps)).length < P)
    {wv : WalkR} (hw : wv ∈ ws) {st : WStep3} (hst : st ∈ wv.steps) (hm : st.mode = 2) :
    ∃ n, ∃ hn : n < vs.length, st.e.getD 0 0 = n ∧ vs[n].v.bmap = some (st.bm, st.hv) := by
  apply Classical.byContradiction; intro hno
  have hno1 : ∀ n (hn : n < vs.length) bm hv, vs[n].v.bmap = some (bm, hv) →
      [n, bm, hv] ≠ [st.e.getD 0 0, st.bm, st.hv] := by
    intro n hn bm hv hb he
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨h1, rfl, rfl⟩ := he
    exact hno ⟨n, hn, h1.symm, hb⟩
  obtain ⟨b, hok⟩ := stepOk_of_mem hW hw hst
  have hcanW := hW.canon wv hw
  have hab := hok.absB hm
  have hcount := hN.count
  have hP := P_big
  have hcanon : ∀ st' ∈ wv.steps, ∀ x ∈ st'.e, x < P := fun st' h => (hcanW.2.2 st' h).2.2.2
  have hwalkC : ∀ {wv' : WalkR}, wv' ∈ ws → ∀ st' ∈ wv'.steps, st'.mode = 2 →
      Canon [st'.e.getD 0 0, st'.bm, st'.hv] := by
    intro wv' hw' st' hst' hm2
    obtain ⟨b', hok'⟩ := stepOk_of_mem hW hw' hst'
    have hab' := hok'.absB hm2
    have hc' := (hW.canon wv' hw').2.2 st' hst'
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact getD_lt hc'.2.2.2 0
    · have := hab'.2.1; unfold P; omega
    · have := hab'.2.2.1; unfold P; omega
  have hheadS : headSends hs B_BMAP = [] := by simp [headSends, B_BMAP, B_MIDROOT, B_PARENT, B_EDGE, B_DIGS]
  have hheadR : headRecvs hs B_BMAP = [] := by simp [headRecvs, B_BMAP, B_DIGEST, B_ROOT, B_EDGE]
  unfold BusBal at hbal
  rw [walkSends3_bmap, walkRecvs3_bmap, hheadS, hheadR, List.append_nil, List.append_nil] at hbal
  have hprov : ∀ m, m ∈ nodeSends3 vs B_BMAP ∨ m ∈ nodeRecvs3 vs B_BMAP →
      ∃ e' x, m = e' ++ [x] ∧ e'.length = 3 ∧ Canon e' ∧ e' ≠ [st.e.getD 0 0, st.bm, st.hv] := by
    intro m hm'
    obtain ⟨n, hn, bm, hv, x, hb, rfl⟩ := mem_nodeBmap hm'
    have hsm := List.getElem_mem hn
    refine ⟨[n, bm, hv], x, rfl, rfl, ?_, hno1 n hn bm hv hb⟩
    have hwf := hN.wf _ hsm
    generalize hvv : vs[n].v = v at hb hwf
    cases v with
    | branch sv kids m =>
      simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact bmap_canon hwf.1 n (by omega) sv
    | leaf => simp [NodeV3.bmap] at hb
    | ext => simp [NodeV3.bmap] at hb
  refine chain_provided (k := 3) _ _ _ [st.e.getD 0 0, st.bm, st.hv] ?_ ?_ ?_ rfl
    (hwalkC hw st hst hm) (u := st.ub) ?_ hbal
  · intro m hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hprov m (Or.inl hm')
    · exact hprov m (Or.inr hm')
  · intro s hs
    obtain ⟨wv', hw', hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hs'
    have hst'' := List.mem_filter.mp hst'
    have hm2 : st'.mode = 2 := by simpa using hst''.2
    exact ⟨rfl, hwalkC hw' st' hst''.1 hm2, ((hW.canon wv' hw').2.2 st' hst''.1).2.2.1⟩
  · have := flatMap_filter_len (fun st : WStep3 => decide (st.mode = 2))
      (fun st => ([st.e.getD 0 0, st.bm, st.hv], st.ub)) ws
    omega
  · exact List.mem_flatMap.mpr ⟨wv, hw, List.mem_map.mpr ⟨st, List.mem_filter.mpr ⟨hst, by simpa using hm⟩, rfl⟩⟩

end Prov

end ZkFormal.NearV3.Walk3
