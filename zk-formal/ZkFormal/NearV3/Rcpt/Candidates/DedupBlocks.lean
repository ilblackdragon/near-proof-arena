import ZkFormal.NearV3.Rcpt.Candidates.DedupBlockSpan

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3

/-- A full candidate source decomposition, allowing skipped one-row headers. -/
inductive BlockChain (tr : Trace Fp) (tt : Nat) : Nat → List SrcpB → Nat → Prop
  | last (s n : Nat) (B : SrcpB) (span : BlockSpan tr tt s B n)
      (padding : ∀ r, s+n≤r → r<tr.height tt → tr.cell tt r rt=0 ∧ tr.cell tt r sg=0) :
      BlockChain tr tt s [B] (s+n)
  | cons (s n : Nat) (B : SrcpB) (span : BlockSpan tr tt s B n)
      (bs : List SrcpB) (e : Nat) (tail : BlockChain tr tt (s+n) bs e) :
      BlockChain tr tt s (B::bs) e

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem padding_from {s : Nat} (hs : s<tr.height tt)
    (ht : tr.cell tt s rt=0) (hg : tr.cell tt s sg=0) :
    ∀ r, s≤r → r<tr.height tt → tr.cell tt r rt=0 ∧ tr.cell tt r sg=0 := by
  have gen : ∀ d, s+d<tr.height tt → tr.cell tt (s+d) rt=0 ∧ tr.cell tt (s+d) sg=0 := by
    intro d
    induction d with
    | zero => intro _; simpa using And.intro ht hg
    | succ d ih =>
      intro hd
      have hp := ih (by omega)
      simpa only [Nat.add_assoc] using padStep hL (r := s+d) (by omega) hp.1 hp.2
  intro r hr hH
  simpa [Nat.add_sub_cancel' hr] using gen (r-s) (by omega)

/-- Every root begins a finite chain of computed or skipped source blocks. -/
theorem blocks_from {s : Nat} (hs : s<tr.height tt) (ht : tr.cell tt s rt=1) :
    ∃ bs e, BlockChain tr tt s bs e := by
  have gen : ∀ fuel s, tr.height tt-s≤fuel → s<tr.height tt → tr.cell tt s rt=1 →
      ∃ bs e, BlockChain tr tt s bs e := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro s hf hs ht
      obtain ⟨B, n, hn⟩ := block_span_from hL hs ht
      obtain ⟨hpos, hbound⟩ := hn.bound
      by_cases he : s+n<tr.height tt
      · have hnsg := hn.next_no_segment hL he
        rcases isBool hL he (x := rt) (by simp [SrcpProof.bools]) with hrt | hrt
        · exact ⟨_, _, .last s n B hn (padding_from hL he hrt hnsg)⟩
        · obtain ⟨bs, e, hc⟩ := ih (tr.height tt-(s+n)) (by omega)
            (s+n) (by omega) he hrt
          exact ⟨_, _, .cons s n B hn bs e hc⟩
      · exact ⟨_, _, .last s n B hn (by intro r hr hrH; omega)⟩
  exact gen (tr.height tt-s) s (by omega) hs ht

/-- The global first-row equations supply a complete extracted source sequence. -/
theorem extract_blocks : ∃ bs e, BlockChain tr tt 0 bs e :=
  blocks_from hL (Nat.two_pow_pos _) (row0 hL).1

omit hL in
theorem BlockChain.nonempty {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) : bs≠[] := by
  cases h <;> simp

omit hL in
theorem BlockChain.bound {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    s<e ∧ e≤tr.height tt := by
  induction h with
  | last s n B hs hp => have := hs.bound; omega
  | cons s n B hs bs e ht ih => have := hs.bound; omega

omit hL in
theorem BlockSpan.render_rows {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    n=1+DedupRender.payloadRows B := by
  rw [h.rows]
  cases hd : B.dup <;> simp [DedupRender.payloadRows, hd] <;> omega

omit hL in
theorem BlockChain.rows {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    e=s+DedupRender.R bs := by
  induction h with
  | last s n B hs hp =>
    rw [DedupRender.R_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [hs.render_rows]
  | cons s n B hs bs e ht ih =>
    rw [ih, hs.render_rows]
    simp only [DedupRender.R_eq, List.map_cons, List.sum_cons]
    omega

omit hL in
theorem BlockChain.padding {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ r, e≤r → r<tr.height tt → tr.cell tt r rt=0 ∧ tr.cell tt r sg=0 := by
  induction h with
  | last s n B hs hp => exact hp
  | cons s n B hs bs e ht ih => exact ih

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
