import ZkFormal.NearV3.Rcpt.Candidates.DedupComputedBlock

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3
open SrcpProof (regsN)

/-- A skipped occurrence has no private leaf or path traffic. Its public root
must later be linked to the same-key computed occurrence through prepared data. -/
def skipBlock (tr : Trace Fp) (tt s : Nat) : SrcpB :=
  { j := (tr.cell tt s j).toNat, L := (tr.cell tt s L).toNat,
    dup := true, root := regsN tr tt s, qe := (tr.cell tt s q).toNat,
    le := 0, ql := (tr.cell tt s q).toNat+1,
    leaf := List.replicate 32 0, path := [] }

/-- A source block is either an actual computed leaf/path proof or a constrained
one-row skipped header. -/
inductive BlockSpan (tr : Trace Fp) (tt : Nat) : Nat → SrcpB → Nat → Prop
  | computed (s m : Nat) (hs : s<tr.height tt) (ht : tr.cell tt s rt=1)
      (hd : tr.cell tt s dup=0) (hm : PathRun tr tt (s+32) m) :
      BlockSpan tr tt s (blockOf tr tt s m) (33+64*m)
  | skipped (s : Nat) (hs : s<tr.height tt) (hd : tr.cell tt s dup=1) :
      BlockSpan tr tt s (skipBlock tr tt s) 1

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- A skipped occurrence has exactly the empty-list encoded length. -/
theorem skip_length {s : Nat} (hs : s<tr.height tt) (hd : tr.cell tt s dup=1) :
    (skipBlock tr tt s).L=12 := by
  have hh := (duplicate_fields hL hs hd).2.2.2.1
  change (tr.cell tt s L).toNat=12
  rw [hh]
  decide +kernel

/-- No segment can follow a skipped header; only a new source root or padding. -/
theorem duplicate_next_no_segment {s : Nat} (hs : s+1<tr.height tt)
    (hd : tr.cell tt s dup=1) : tr.cell tt (s+1) sg=0 := by
  rcases isBool hL (r := s) (by omega) (x := gz) (by simp [SrcpProof.bools]) with hz | hz
  · have ht := (duplicate_step hL hs hd hz).1
    have hh := disjoint hL hs
    rw [ht] at hh
    grind
  · exact (gz_next_inactive hL hs hz).2

/-- Every actual root begins a finite computed or skipped source span. -/
theorem block_span_from {s : Nat} (hs : s<tr.height tt) (ht : tr.cell tt s rt=1) :
    ∃ B n, BlockSpan tr tt s B n := by
  rcases isBool hL hs (x := dup) (by simp [SrcpProof.bools]) with hd | hd
  · obtain ⟨m, hm⟩ := block_path_run hL hs ht hd
    exact ⟨_, _, .computed s m hs ht hd hm⟩
  · exact ⟨_, _, .skipped s hs hd⟩

omit hL in
theorem BlockSpan.bound {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    0<n ∧ s+n≤tr.height tt := by
  cases h with
  | computed m hs ht hd hm => have := hm.bound; omega
  | skipped hs hd => omega

omit hL in
theorem BlockSpan.rows {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    n=(if B.dup then 1 else 33+64*B.path.length) := by
  cases h with
  | computed m hs ht hd hm => simp [blockOf, hd, pathItems]
  | skipped hs hd => rfl

/-- Every span ends at a list boundary, including the one-row skip case. -/
theorem BlockSpan.next_no_segment {s n : Nat} {B : SrcpB}
    (h : BlockSpan tr tt s B n) (hn : s+n<tr.height tt) : tr.cell tt (s+n) sg=0 := by
  cases h with
  | computed m hs ht hd hm =>
    have hh := hm.stop
    rw [show s+32+64*m+1=s+(33+64*m) by omega, Nat.mod_eq_of_lt hn] at hh
    exact hh
  | skipped hs hd => exact duplicate_next_no_segment hL hn hd

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
