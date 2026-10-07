import ZkFormal.NearV3.Rcpt.Candidates.DedupEndLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTerminalLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTerminalPadding

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- A terminal source block enters padding with exactly its completed SIZE charge. -/
theorem end_to_padding (B : SrcpB) (hB : BlockFacts B) (before : Nat)
    (rep : Bool)
    (hr : B.dup = true → rep = true) (hL : rep = true → B.L = 12)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (lastKind B) true rep x : Int))
        (fun x => if x = SrcpV3.sz then ((before + sizeStep B : Nat) : Int) else 0)
        0 0 1 pub ex = 0 := by
  intro ex hex
  cases hd : B.dup
  · by_cases hz : B.path.length = 0
    · have hn : B.path = [] := List.length_eq_zero_iff.mp hz
      have hqe : B.qe = B.ql := by simpa [SrcpB.lastQ, hz] using hB.counter.qe
      have hle : B.le = 32 := by simpa [hn] using hB.counter.le
      have hh := leaf_to_padding B before hqe hle pub ex hex
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
      have hh := path_to_padding B before (B.path.length - 1) hqe hle pub ex hex
      simpa only [leaf_metadata, path_metadata, lastKind, hd, Bool.false_eq_true, ite_false, Render.SrcpGen.lastKind,
        hz, he, sizeStep, Nat.add_assoc] using hh
  · have hr' := hr hd
    have hh := duplicate_to_padding B before hd (hL hr') pub ex hex
    simpa only [leaf_metadata, path_metadata, lastKind, hd, ite_true, hr', sizeStep, Nat.add_zero] using hh


/-- A terminal source block satisfies the physical endpoint constraints when the cyclic successor is a root or padding. -/
theorem end_physical_last (B : SrcpB) (hB : BlockFacts B) (before : Nat)
    (rep : Bool)
    (hr : B.dup = true → rep = true) (hL : rep = true → B.L = 12)
    (next pub : Nat → Int) (hsg : next SrcpV3.sg = 0) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (lastKind B) true rep x : Int))
        next
        0 1 0 pub ex = 0 := by
  intro ex hex
  cases hd : B.dup
  · by_cases hz : B.path.length = 0
    · have hn : B.path = [] := List.length_eq_zero_iff.mp hz
      have hqe : B.qe = B.ql := by simpa [SrcpB.lastQ, hz] using hB.counter.qe
      have hle : B.le = 32 := by simpa [hn] using hB.counter.le
      have hh := leaf_physical_last B before hqe hle next pub hsg ex hex
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
      have hh := path_physical_last B before (B.path.length - 1) hqe hle next pub hsg ex hex
      simpa only [leaf_metadata, path_metadata, lastKind, hd, Bool.false_eq_true, ite_false, Render.SrcpGen.lastKind,
        hz, he, sizeStep, Nat.add_assoc] using hh
  · have hr' := hr hd
    have hh := duplicate_physical_last B before hd (hL hr') next pub ex hex
    simpa only [leaf_metadata, path_metadata, lastKind, hd, ite_true, hr', sizeStep, Nat.add_zero] using hh


end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
