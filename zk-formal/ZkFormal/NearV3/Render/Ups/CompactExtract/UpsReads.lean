import ZkFormal.NearV3.Render.Ups.CompactExtract.GlobalParts
import ZkFormal.NearV3.Extract.Ups.UpsReads
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A read row is a node-part row. -/
theorem rd_qb (h : C rd = 1) : C qb = 1 := by
  have f := factN ok hC hD (e := .mul (not (c qb)) (c rd)) (by simp [compactConstraints, UpsV3.cBytes])
  have hb := rowBool ok hC (x := qb) (by simp [rowBools])
  nev_simp at f
  rcases hb with h' | h'
  · simp [h', h] at f
  · exact h'

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- The `UPB` messages of a row (either side). -/
theorem upbMsgs {i : Nat} (hi : i < s.rows.length) (sd : Bool) :
    uMsgs (s.row i) (s.next i) B_UPB sd =
      if s.row i rd = 1 then [upbN (s.row i) (if sd then (s.row i u + 1) % P else s.row i u)] else [] := by
  obtain ⟨ps, fls, ws, hL⟩ := ups_layout hw s hs
  rcases Nat.lt_or_ge i (4) with h | h
  · have hrd : s.row i rd ≠ 1 := fun h1 => by
      have := qbAfter hw hs hL hi (rd_qb (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _) h1); omega
    rw [if_neg hrd]
    rw [hL.msgsW i h B_UPB sd]
    cases sd <;> simp [B_UPB,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_EDGE,B_BMAP]
  · rw [hL.msgsQ i h hi B_UPB sd]
    cases sd <;> simp [B_UPB, B_DIGEST, B_BYTES, B_MEMD]

end

/-- The read rows of the segments: `(key, use count)`. -/
def upbW (v : List UpsSeg) : List (Msg × Nat) :=
  v.flatMap fun s => (List.range s.rows.length).flatMap fun i =>
    if s.row i rd = 1 then [(upbK (s.row i), s.row i u)] else []

theorem flatMap_congrR {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [h a (by simp), flatMap_congrR (fun x hx => h x (by simp [hx]))]

theorem toFp_succ_mod (m : Msg) (x : Nat) : (m ++ [(x + 1) % P]).toFp = (m ++ [x + 1]).toFp := by
  simp only [Msg.toFp, List.map_append, List.map_cons, List.map_nil]
  congr 2
  exact Link.ofNat_eq_iff.2 (Nat.mod_mod _ _)

theorem upsUpb_sends {v : List UpsSeg} (hw : Wf v) :
    ((upsTraffic v).sends B_UPB).map Msg.toFp = ((upbW v).map fun s => s.1 ++ [s.2 + 1]).map Msg.toFp := by
  simp only [upsTraffic, upbW, UpsSeg.msgs, List.map_flatMap]
  apply flatMap_congrR; intro s hs
  apply flatMap_congrR; intro i hi
  rw [upbMsgs hw hs (List.mem_range.1 hi) true]
  split <;> simp [upbN_eq, toFp_succ_mod]

theorem upsUpb_recvs {v : List UpsSeg} (hw : Wf v) :
    ((upsTraffic v).recvs B_UPB).map Msg.toFp = ((upbW v).map fun s => s.1 ++ [s.2]).map Msg.toFp := by
  simp only [upsTraffic, upbW, UpsSeg.msgs, List.map_flatMap]
  apply flatMap_congrR; intro s hs
  apply flatMap_congrR; intro i hi
  rw [upbMsgs hw hs (List.mem_range.1 hi) false]
  split <;> simp [upbN_eq]

theorem nodeSends3_upb (vs : List NodeS3) :
    nodeSends3 vs B_UPB = (vs.zip (List.range vs.length)).flatMap fun (s, n) => upbOf n s fun _ => 0 := by
  simp [nodeSends3, B_UPB, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_SIZE]

theorem nodeRecvs3_upb (vs : List NodeS3) :
    nodeRecvs3 vs B_UPB = (vs.zip (List.range vs.length)).flatMap fun (s, n) => upbOf n s fun p => s.mU.getD p 0 := by
  simp [nodeRecvs3, B_UPB, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_ENT]

theorem upbOf_mem {n : Nat} {s : NodeS3} {f : Nat → Nat} {m : Msg} (h : m ∈ upbOf n s f) :
    ∃ p, p < (s.v.ser false).length ∧ m = nodeK n s p ++ [f p] := by
  simp only [upbOf, List.mem_map, List.mem_range] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, hp, rfl⟩

theorem flatMap_opt_len {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length ≤ 1) :
    ∀ (r : List α), (r.flatMap f).length ≤ r.length
  | [] => by simp
  | a :: r => by
    have := flatMap_opt_len f hf r; have := hf a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem upbW_len {v : List UpsSeg} (hw : Wf v) : (upbW v).length ≤ 2 ^ 22 := by
  have h : ∀ (l : List UpsSeg), (upbW l).length ≤ (l.map (·.rows.length)).sum := by
    intro l
    induction l with
    | nil => simp [upbW]
    | cons a l ih =>
      simp only [upbW, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
      have := flatMap_opt_len (fun i => if a.row i rd = 1 then [(upbK (a.row i), a.row i u)] else [])
        (fun i => by split <;> simp) (List.range a.rows.length)
      simp only [List.length_range] at this
      omega
  exact Nat.le_trans (h v) hw.count

theorem npost_eq {x n : Nat} (hx : x < P) (hn : n < 2 ^ 22) (h : (K_NPOST + 16 * x) % P = K_NPOST + 16 * n) :
    x = n := by
  unfold K_NPOST at h; rw [P_lit] at h hx; omega

/-- **A read row reads record `sN`.** -/
theorem upb_read {vs : List NodeS3} {v : List UpsSeg} (hN : NodeWf3 vs) (hw : Wf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {i : Nat} (hi : i < s.rows.length) (hrd : s.row i rd = 1) :
    UpbRead vs (s.row i) := by
  have hC := fun x => rowLt hw hs i x
  have hK : ∃ n, ∃ hn : n < vs.length, ∃ p, p < (vs[n].v.ser false).length ∧ upbK (s.row i) = nodeK n vs[n] p := by
    apply Classical.byContradiction; intro hno
    unfold UpbBal at hbal
    rw [List.map_append, List.map_append, upsUpb_sends hw, upsUpb_recvs hw, ← List.map_append, ← List.map_append,
      nodeSends3_upb, nodeRecvs3_upb] at hbal
    refine Walk3.chain_provided (k := 6) _ _ (upbW v) (upbK (s.row i)) ?_ ?_ ?_ rfl ?_ (u := s.row i u) ?_ hbal
    · intro m hm
      have hm' : ∃ n, ∃ hn : n < vs.length, ∃ f : Nat → Nat, m ∈ upbOf n vs[n] f := by
        rcases List.mem_append.1 hm with hm | hm <;>
        · obtain ⟨⟨t, n⟩, hp, hm⟩ := List.mem_flatMap.1 hm
          obtain ⟨hn, rfl⟩ := Link3.mem_zip_range hp
          exact ⟨n, hn, _, hm⟩
      obtain ⟨n, hn, f, hm⟩ := hm'
      obtain ⟨p, hp, rfl⟩ := upbOf_mem hm
      refine ⟨nodeK n vs[n] p, f p, rfl, rfl, ?_, fun he => hno ⟨n, hn, p, hp, he.symm⟩⟩
      have hl := Link3.ser_len_lt hN hn
      have hsm := List.getElem_mem hn
      intro x hx
      simp only [nodeK, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Link3.nid_lt hN hn K_NPOST (by decide)
      · rw [P_lit]; omega
      · rw [List.getD_eq_getElem?_getD]
        rcases h' : (vs[n].v.ser true)[p]? with _ | y
        · simp; rw [P_lit]; omega
        · simp only [Option.getD_some]
          exact Link3.post_lt_P hN hn y (List.mem_of_getElem? h')
      · rw [P_lit]; omega
      · exact (hN.small _ hsm).2.1
      · rw [List.getD_eq_getElem?_getD]
        rcases h' : vs[n].ucid[p]? with _ | y
        · simp; rw [P_lit]; omega
        · simp only [Option.getD_some]
          exact (hN.upbSmall _ hsm).1 y (List.mem_of_getElem? h')
    · intro w hw'
      simp only [upbW, List.mem_flatMap, List.mem_range] at hw'
      obtain ⟨t, ht, r, hr, hw'⟩ := hw'
      split at hw'
      · simp only [List.mem_singleton] at hw'; subst hw'
        refine ⟨rfl, ?_, rowLt hw ht _ _⟩
        intro x hx
        simp only [upbK, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Nat.mod_lt _ (by rw [P_lit]; omega)
        all_goals exact rowLt hw ht _ _
      · simp at hw'
    · have := upbW_len hw; rw [P_lit]; omega
    · intro x hx
      simp only [upbK, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Nat.mod_lt _ (by rw [P_lit]; omega)
      all_goals exact hC _
    · simp only [upbW, List.mem_flatMap, List.mem_range]
      exact ⟨s, hs, i, hi, by rw [if_pos hrd]; simp⟩
  obtain ⟨n, hn, p, hp, he⟩ := hK
  simp only [upbK, nodeK, List.cons.injEq, and_true] at he
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := he
  have hsN : s.row i sN = n := npost_eq (hC _) (by have := hN.count; omega) (by rw [e1]; rfl)
  subst hsN
  exact ⟨hn, by rw [e2]; exact hp, by rw [e3, e2], e4, e5, by rw [e6, e2]⟩

/-- **`UpsExt0.reads`** from the `UPB` balance. -/
theorem upb_reads {vs : List NodeS3} {v : List UpsSeg} (hN : NodeWf3 vs) (hw : Wf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) : UpbReads s (postB vs) := by
  intro i hi hrd
  obtain ⟨hn, -, h1, h2, -, -⟩ := upb_read hN hw hbal hs hi hrd
  have hg : vs.getD (s.row i sN) default = vs[s.row i sN] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
  refine ⟨by rw [postB, hg]; exact h1, ?_⟩
  rw [postB, hg, Link3.ser_length_post3 (hN.wf _ (List.getElem_mem hn))]; exact h2

/-! ## The number of parts -/

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- A part other than the new leaf reads on its first `MEM` row (with the part's `sN` and `pdep`). -/
theorem memRead (c : Nat) (hc : c < ps.length) (hc8 : kd c ≠ 8) :
    ps[c].1 + ps[c].2 - 8 < s.rows.length ∧ s.row (ps[c].1 + ps[c].2 - 8) rd = 1 ∧
    s.row (ps[c].1 + ps[c].2 - 8) sN = s.row ps[c].1 sN ∧
    s.row (ps[c].1 + ps[c].2 - 8) pdep = s.row ps[c].1 pdep := by
  obtain ⟨h8, hR8⟩ := memRows8 hw hs hL hP c hc
  have U := (hL.part c hc).2
  have hle := U.le
  obtain ⟨hm, -⟩ := hR8 0 (by omega)
  have hd : ps[c].2 - 8 < ps[c].2 := by omega
  rw [show ps[c].1 + ps[c].2 - 8 + 0 = ps[c].1 + (ps[c].2 - 8) by omega] at hm
  have hlt : ps[c].1 + (ps[c].2 - 8) < s.rows.length := by omega
  have hq := (U.rows _ hd).1
  have hoh := oneHot hw hs hlt hq
  obtain ⟨-, bK, -, -⟩ := partBits hw hs hL hP c hc _ hd
  rw [if_neg hc8] at bK
  have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hm bK hoh
  rw [show ps[c].1 + ps[c].2 - 8 = ps[c].1 + (ps[c].2 - 8) by omega]
  exact ⟨hlt, hrd, partPc hw hs hL hP c hc _ hd (by decide), partPc hw hs hL hP c hc _ hd (by decide)⟩

end

/-- **At most 404 parts**: `|ps| = nT + dep_D` with `nT ≤ 4`, and `dep_D ≤ 400` since the first upper
part reads a record at depth `dep_D − 1 < 400` (`depth_lt`). -/
theorem ups_nparts {vs : List NodeS3} {hds : List HeadE} {v : List UpsSeg} (hN : NodeWf3 vs) (hhw : HeadWf hds)
    (hb : Link3.ParentBal vs hds) (hw : Wf v) (hbal : UpbBal vs v) {s : UpsSeg} (hs : s ∈ v)
    {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) : ps.length ≤ 404 := by
  obtain ⟨ci, ti, di, si, kd, sdx, hP⟩ := ups_plan hw hs hL
  have hlen := hP.len
  have hT := nTof_le ci hP.ix.1 ti hP.ix.2.1
  by_cases h0 : s.row 0 (176 + di) = 0
  · omega
  · have hk : nTof ci ti < ps.length := by omega
    obtain ⟨hku, -, hpd⟩ := hP.upper _ hk (Nat.le_refl _)
    obtain ⟨hlt, hrd, -, hp⟩ := memRead hw hs hL hP _ hk (by omega)
    obtain ⟨hn, -, -, -, hdep, -⟩ := upb_read hN hw hbal hs hlt hrd
    have := Link3.depth_lt hN hhw hb hn
    rw [hp] at hdep
    omega

/-- **`UpsIdBound`** from the part bound and instances below `2^17`. -/
theorem ups_idBound {vs : List NodeS3} {hds : List HeadE} {v : List UpsSeg} (hN : NodeWf3 vs) (hhw : HeadWf hds)
    (hb : Link3.ParentBal vs hds) (hw : Wf v) (hbal : UpbBal vs v) (hτ : ∀ s ∈ v, s.row 0 tau < 32) :
    CompactIdBound v :=
  fun s hs => ⟨hτ s hs, fun _ _ _ hL => by have := ups_nparts hN hhw hb hw hbal hs hL; omega⟩

end ZkFormal.NearV3.Render.UpsRelay.Extract
