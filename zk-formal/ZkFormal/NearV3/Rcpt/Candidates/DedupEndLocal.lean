import ZkFormal.NearV3.Rcpt.Candidates.DedupBlockFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupCrossLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupLayoutSize
import ZkFormal.NearV3.Rcpt.Candidates.DedupNextMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- A whole source block ends at the next public source header. The predecessor
counter advances only for a computed block; repeated headers preserve it. -/
theorem end_to_root (B C : SrcpB) (hB : BlockFacts B) (before : Nat)
    (rep terminalNext repNext : Bool)
    (hr : B.dup = true → rep = true) (hL : rep = true → B.L = 12)
    (hj : C.j = B.j + 1)
    (hq : C.ql = if B.dup then B.ql else B.lastQ + 1) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (lastKind B) false rep x : Int))
        (fun x => (localCells C (before + sizeStep B) .root terminalNext repNext x : Int))
        0 0 1 pub ex = 0 := by
  intro ex hex
  rw [next_metadata C (before + sizeStep B) .root terminalNext repNext _ 0 0 1 pub ex hex]
  cases hd : B.dup
  · have hq' : C.ql = B.lastQ + 1 := by simpa [hd] using hq
    by_cases hz : B.path.length = 0
    · have hn : B.path = [] := List.length_eq_zero_iff.mp hz
      have hqe : B.qe = B.ql := by simpa [SrcpB.lastQ, hz] using hB.counter.qe
      have hle : B.le = 32 := by simpa [hn] using hB.counter.le
      have hh := leaf_to_root B C before false hqe hle
        (by simpa [SrcpB.lastQ, hz] using hq') hj pub ex hex
      simpa only [leaf_metadata, path_metadata, lastKind, hd, Bool.false_eq_true, ite_false, Render.SrcpGen.lastKind,
        hz, ite_true, sizeStep, Nat.mul_zero, Nat.add_zero] using hh
    · have hi : B.path.length - 1 < B.path.length := by omega
      have he : B.path.length - 1 + 1 = B.path.length := by omega
      have hitem := hB.item B (B.path.length - 1) hi
      have hlast : (B.path.getD (B.path.length - 1) default).q = B.lastQ := by
        simp only [SrcpB.lastQ]
        omega
      have hqe : B.qe = (B.path.getD (B.path.length - 1) default).q :=
        hB.counter.qe.trans hlast.symm
      have hn : B.path ≠ [] := by intro h; simp [h] at hz
      have hle : B.le = 64 := by simpa [hn] using hB.counter.le
      have hh := path_to_root B C before (B.path.length - 1) false hqe hle
        (by rw [hlast]; exact hq') hj pub ex hex
      simpa only [leaf_metadata, path_metadata, lastKind, hd, Bool.false_eq_true, ite_false, Render.SrcpGen.lastKind,
        hz, he, sizeStep, Nat.add_assoc] using hh
  · have hq' : C.ql = B.ql := by simpa [hd] using hq
    have hr' := hr hd
    have hh := duplicate_to_root B C before false hd (hL hr') hj hq' pub ex hex
    simpa only [leaf_metadata, path_metadata, lastKind, hd, ite_true, hr', sizeStep, Nat.add_zero] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
