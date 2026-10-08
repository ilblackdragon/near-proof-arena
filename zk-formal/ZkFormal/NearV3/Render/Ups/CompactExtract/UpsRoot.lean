import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsChain
import ZkFormal.NearV3.Extract.Ups.UpsRoot
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The root part reads `rootRid`.** -/
theorem rootSrcRow (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    s.row ps[k].1 sN = s.row 0 rootRid := by
  obtain ⟨hlt0, hq0, -⟩ := pFirst hw hs hL k hk
  have hr := (hP.root k hk).2 hroot
  have f := UpsRows.factN (nodeRowOk (okRow hw hs hlt0) (rowLt hw hs _) hq0) (rowLt hw hs _) (nextLt hw hs _)
    (e := mul3 (c qb) (c rootP) (sub (c sN) (c rootRid))) (memRows (by simp [cRows]))
  have h1 := rowLt hw hs ps[k].1 sN
  have h2 := rowLt hw hs ps[k].1 rootRid
  rw [P_lit] at h1 h2
  nev_simp at f
  simp [hq0, hr] at f
  rw [← hL.segc _ hlt0 rootRid (by decide)]
  omega

end

/-- **The root part's source is the root record of the head of `τ`.** -/
theorem ups_rootSrc {hds : List HeadE} {v : List UpsSeg} {K : Nat} {r0 rK : List Nat}
    (hC : RootChain hds (v.map upsE) K r0 rK) (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
    {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    s.row ps[k].1 sN = (headAt hds (s.row 0 tau)).rid := by
  rw [rootSrcRow hw hs hL hP k hk hroot]
  obtain ⟨hle, he⟩ := hC.ups_all (upsE s) (List.mem_map.2 ⟨s, hs, rfl⟩)
  have := hC.rid _ hle
  rw [← he] at this
  exact this

end ZkFormal.NearV3.Render.UpsRelay.Extract
