import ZkFormal.NearV3.Extract.Ups.UpsVb
import ZkFormal.NearV3.Extract.Ups.UpsChain

/-!
# ZkFormal.NearV3.Extract.Ups.UpsRoot — the root part reads the instance's root record (M7e, root binding)

`W0` receives `MIDROOT (τ, rid, mid)` from the head of `τ` into the segment constant `rootRid`, and the root
part's source is pinned to it (`qb·rootP·(sN − rootRid) = 0`).

* **`rootSrcRow`**: the root part's `sN` is `rootRid`;
* **`ups_rootSrc`**: with the instance chain (`RootChain`, whose `rid` field matches the `MIDROOT` messages),
  the root part's source is the root record `rid` of the head of `τ`.

This closes the gap where the pass-through parts above the walk's first record were bound to no instance
(STATUS §6 register).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The root part reads `rootRid`.** -/
theorem rootSrcRow (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    s.row ps[k].1 sN = s.row 0 rootRid := by
  obtain ⟨hlt0, hq0, -⟩ := pFirst hw hs hL k hk
  have hr := (hP.root k hk).2 hroot
  have f := factN (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _)
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
    (hC : RootChain hds (v.map upsE) K r0 rK) (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
    {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    s.row ps[k].1 sN = (headAt hds (s.row 0 tau)).rid := by
  rw [rootSrcRow hw hs hL hP k hk hroot]
  obtain ⟨hle, he⟩ := hC.ups_all (upsE s) (List.mem_map.2 ⟨s, hs, rfl⟩)
  have := hC.rid _ hle
  rw [← he] at this
  exact this

end ZkFormal.NearV3.UpsRows
