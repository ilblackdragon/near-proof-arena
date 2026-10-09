import ZkFormal.NearV3.Rcpt.Candidates.DedupBlockFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupAdjacency
import ZkFormal.NearV3.Rcpt.Candidates.DedupNextMetadata
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathUpper
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathBoundary
import ZkFormal.NearV3.Rcpt.Candidates.DedupLeafExit
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathExit

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- Every actual internal descriptor step satisfies all candidate constraints;
the successor may independently be terminal or carry repetition metadata. -/
theorem internal_local (B : SrcpB) (hB : BlockFacts B) (before : Nat)
    (k next : Kind) (hk : k ∈ kinds B) (hn : nextKind B k = some next)
    (rep terminalNext repNext : Bool) (hrep : rep = true → B.L = 12)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before k false rep x : Int))
        (fun x => (localCells B before next terminalNext repNext x : Int))
        0 0 1 pub ex = 0 := by
  intro ex hex
  rw [next_metadata B before next terminalNext repNext _ 0 0 1 pub ex hex]
  have hd : B.dup = false := by
    cases he : B.dup
    · rfl
    · simp [nextKind, he] at hn
  have hk' : k ∈ Render.SrcpGen.kinds B := by simpa [kinds, hd] using hk
  have hn' : Render.SrcpGen.nextKind B k = some next := by simpa [nextKind, hd] using hn
  have hm := (Render.SrcpGen.mem_kinds B k).mp hk'
  cases k with
  | root =>
    simp only [Render.SrcpGen.nextKind, Option.some.injEq] at hn'
    subst next
    exact computed_root_to_leaf B before rep hd (by have := hB.counter.qpos; omega) hrep pub ex hex
  | leaf p =>
    simp only [leaf_metadata]
    have hp : p < 32 := by simpa using hm
    by_cases hs : p + 1 < 32
    · simp only [Render.SrcpGen.nextKind, hs, ite_true, Option.some.injEq] at hn'
      subst next
      exact leaf_step B before p (by omega) pub ex hex
    · have he : p = 31 := by omega
      subst p
      by_cases hz : 0 < B.path.length
      · simp only [Render.SrcpGen.nextKind, hs, hz, ite_true, Nat.reduceLT, ite_false,
          Option.some.injEq] at hn'
        subst next
        have hh := hB.item B 0 hz
        exact leaf_to_path B before (by simpa using hh.1) (by simpa using hh.2.2) pub ex hex
      · simp [Render.SrcpGen.nextKind, hz] at hn'
  | path i o =>
    simp only [path_metadata]
    have hh : i < B.path.length ∧ o < 64 := by simpa using hm
    have hi := hB.item B i hh.1
    by_cases hs : o + 1 < 64
    · simp only [Render.SrcpGen.nextKind, hs, ite_true, Option.some.injEq] at hn'
      subst next
      have hq : (B.path.getD i default).q = (B.path.getD i default).pq + 1 := by omega
      by_cases hl : o < 31
      · exact path_lower_step B before i o hl hq pub ex hex
      · by_cases he : o = 31
        · subst o; exact path_window_boundary B before i pub ex hex
        · have ho : Kind.path i o = Kind.path i ((o - 32) + 32) := by congr 1; omega
          have hon : Kind.path i (o + 1) = Kind.path i ((o - 32) + 1 + 32) := by congr 1; omega
          rw [ho, hon]
          exact path_upper_step B before i (o - 32) (by omega) hq pub ex hex
    · have he : o = 63 := by omega
      subst o
      by_cases hnext : i + 1 < B.path.length
      · simp only [Render.SrcpGen.nextKind, hs, hnext, ite_true, Nat.reduceLT, ite_false,
          Option.some.injEq] at hn'
        subst next
        have hj := hB.item B (i + 1) hnext
        exact path_to_path B before i (by omega) (by simpa using hj.2.2) pub ex hex
      · simp [Render.SrcpGen.nextKind, hnext] at hn'

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
