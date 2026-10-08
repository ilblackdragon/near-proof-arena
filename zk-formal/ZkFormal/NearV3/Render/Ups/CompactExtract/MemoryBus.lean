import ZkFormal.NearV3.Render.Ups.CompactExtract.Plan
import ZkFormal.NearV3.Extract.Ups.UpsBus
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A row receiving on `MEMD` is a `MEM` row. -/
theorem gMr_mem (hg : C gMr = 1) : C sMEM = 1 := by
  have f := factN ok hC hD (e := sub (c gMr) (.mul (c sMEM) (c bN))) (memMem (by simp [cMem]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a gMr
  have hb := stBool ok hC (x := sMEM) (by simp [states])
  nev_simp at f
  rcases hb with h | h
  · simp [h, hg] at f
  · exact h

theorem mem_qb (hm : C sMEM=1) : C qb=1 := by
  have := stSum ok hC
  have hq:=rowBool ok hC (x:=qb) (by simp [rowBools])
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws)
include hw hs hL

/-- A row with `qb = 1` lies after the value rows. -/
theorem qbAfter {i : Nat} (hi : i < s.rows.length) (hq : s.row i qb = 1) : 4 ≤ i := by
  apply Classical.byContradiction; intro hc
  obtain ⟨ha, hact, -⟩ := kinds (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  have h4 : i<4 := by omega
  have := hL.wk i h4
  omega

/-- The `MEMD` messages of a row (either side). -/
theorem memdMsgs {i : Nat} (hi : i < s.rows.length) :
    uMsgs (s.row i) (s.next i) B_MEMD true =
      (if 4 ≤ i ∧ s.row i gMs = 1 then
        [[s.row i tau, s.row i j, s.row i idx, s.row i rx, s.row i rb, s.row i UpsV3.qlen]] else []) ∧
    uMsgs (s.row i) (s.next i) B_MEMD false =
      (if 4 ≤ i ∧ s.row i gMr = 1 then
        [[s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen]] else []) := by
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · have e1 := hL.msgsW i h4 B_MEMD true
    have e2 := hL.msgsW i h4 B_MEMD false
    simp only [show ¬ (4 ≤ i) by omega, false_and, ite_false]
    refine ⟨by rw [e1]; simp [B_MEMD, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP],
      by rw [e2]; simp [B_MEMD, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP]⟩
  · have e1 := hL.msgsQ i h4 hi B_MEMD true
    have e2 := hL.msgsQ i h4 hi B_MEMD false
    simp only [h4, true_and]
    refine ⟨by rw [e1]; simp [B_MEMD, B_DIGEST, B_BYTES, B_UPB], by rw [e2]; simp [B_MEMD, B_DIGEST, B_BYTES, B_UPB]⟩

end

/-- **`MEMD` inside each segment**, from the `MEMD` balance and distinct instances. -/
theorem memd_seg {v : List UpsSeg} (hw : Wf v)
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) : ∀ s ∈ v, UpsMemdSeg s := by
  intro s hs i hi hg
  obtain ⟨ps, fls, ws, hL⟩ := ups_layout hw s hs
  have hq := mem_qb (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
    (gMr_mem (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _) hg)
  have h4 := qbAfter hw hs hL hi hq
  have hmem : [s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen] ∈
      (upsTraffic v).recvs B_MEMD :=
    mem_upsRecvs.2 ⟨s, hs, i, hi, by rw [(memdMsgs hw hs hL hi).2, if_pos ⟨h4, hg⟩]; simp⟩
  obtain ⟨m', hm', he⟩ := List.mem_map.1 (hM.symm.subset (List.mem_map.2 ⟨_, hmem, rfl⟩))
  obtain ⟨s', hs', i', hi', hm''⟩ := mem_upsSends.1 hm'
  obtain ⟨ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
  rw [(memdMsgs hw hs' hL' hi').1] at hm''
  split at hm''
  · rename_i hc
    simp only [List.mem_singleton] at hm''
    subst hm''
    have cv := fun (t : UpsSeg) (ht : t ∈ v) (r x : Nat) => rowLt hw ht r x
    have e := Link.toFp_inj (a := [s'.row i' tau, s'.row i' j, s'.row i' idx, s'.row i' rx, s'.row i' rb,
        s'.row i' UpsV3.qlen]) (b := [s.row i tau, s.row i jm, s.row i idx, s.row i mBv, s.row i mCv, s.row i UpsV3.clen])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h <;> rw [h] <;> exact cv _ hs' _ _)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h <;> rw [h] <;> exact cv _ hs _ _) he
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨et, ej, ei, ex, eb, eq⟩ := e
    have hss : s' = s := by
      apply htau s' hs' s hs
      rw [← hL'.segc i' hi' tau (by decide), ← hL.segc i hi tau (by decide), et]
    subst hss
    exact ⟨i', hi', hc.2, ej, ei, ex, eb, eq⟩
  · simp at hm''



end ZkFormal.NearV3.Render.UpsRelay.Extract
