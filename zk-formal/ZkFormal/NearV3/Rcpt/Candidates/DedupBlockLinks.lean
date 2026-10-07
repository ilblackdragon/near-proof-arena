import ZkFormal.NearV3.Rcpt.Candidates.DedupBlocks

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3
variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem block_end_list (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) (hd : tr.cell tt s dup = 0)
    (hm : PathRun tr tt (s + 32) m) :
    ∀ x ∈ listConst, tr.cell tt (s + 32 + 64 * m) x = tr.cell tt s x := by
  obtain ⟨hH, hu, -, -, hc⟩ := root_leaf_unit hL hs ht hd
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := disjoint hL (r := s + 1) (by omega)
    rw [(computed_after_root hL (by omega) ht hd).1] at he; grind
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 31 (by omega)
  intro x hx
  rw [hm.list x hx, show s + 32 = s + 1 + 31 by omega, hrows.2.2.2.1 x hx, hc x hx]

theorem block_end_q (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) (hd : tr.cell tt s dup = 0)
    (hm : PathRun tr tt (s + 32) m) :
    (tr.cell tt (s + 32 + 64 * m) q).toNat = (blockOf tr tt s m).lastQ := by
  have hend := listEnd hL hm.bound hm.sl_end hm.stop
  rw [hend.1, block_end_list hL hs ht hd hm qe (by simp [listConst])]
  exact (block_wf hL hs ht hd hm).root.1

/-- List numbers advance by one while the next root carries the last message number. -/
theorem block_next (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) (hd : tr.cell tt s dup = 0)
    (hm : PathRun tr tt (s + 32) m)
    (hn : s + 33 + 64 * m < tr.height tt) (hnt : tr.cell tt (s + 33 + 64 * m) rt = 1) :
    (tr.cell tt (s + 33 + 64 * m) j).toNat = (tr.cell tt s j).toNat + 1 ∧
    (tr.cell tt (s + 33 + 64 * m) q).toNat = (blockOf tr tt s m).lastQ := by
  have he : s + 32 + 64 * m + 1 = s + 33 + 64 * m := by omega
  have hj := list_j_succ hL (r := s + 32 + 64 * m) (by omega) hm.sl_end (by simpa [he] using hnt)
  have hq := (afterSegRt hL (r := s + 32 + 64 * m) (by omega) hm.sl_end (by simpa [he] using hnt)).1
  rw [he, block_end_list hL hs ht hd hm j (by simp [listConst])] at hj
  rw [he] at hq
  exact ⟨hj, (congrArg Fp.toNat hq).trans (block_end_q hL hs ht hd hm)⟩


theorem BlockSpan.start {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    s<tr.height tt ∧ tr.cell tt s rt=1 := by
  cases h with
  | computed m hs ht hd hm => exact ⟨hs, ht⟩
  | skipped hs hd => exact ⟨hs, duplicate_root hL hs hd⟩

omit hL in
theorem BlockSpan.j_eq {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    B.j=(tr.cell tt s j).toNat := by cases h <;> rfl

theorem BlockSpan.ql_eq {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    B.ql=(tr.cell tt s q).toNat+1 := by
  cases h with
  | computed m hs ht hd hm => exact root_q_succ hL (by have := hm.bound; omega) ht hd
  | skipped hs hd => rfl

/-- The endpoint hash counter advances only for actual computed blocks. -/
theorem BlockSpan.next {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n)
    (hn : s+n<tr.height tt) (hnt : tr.cell tt (s+n) rt=1) :
    (tr.cell tt (s+n) j).toNat=B.j+1 ∧ (tr.cell tt (s+n) q).toNat=B.qe := by
  cases h with
  | computed m hs ht hd hm =>
    have he := block_next hL hs ht hd hm (by simpa [Nat.add_assoc] using hn)
      (by simpa [Nat.add_assoc] using hnt)
    rw [← (block_wf hL hs ht hd hm).root.1] at he
    simpa [blockOf, Nat.add_assoc] using he
  | skipped hs hd =>
    exact ⟨duplicate_j_succ hL hn hd hnt,
      congrArg Fp.toNat (duplicate_active_step hL hn hd (Or.inl hnt)).2.1⟩

theorem BlockSpan.local {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    if B.dup then B.L=12 ∧ B.path=[] ∧ B.le=0 ∧ B.qe+1=B.ql else BlockWf B := by
  cases h with
  | computed m hs ht hd hm =>
    have hb : (blockOf tr tt s m).dup=false := by simp [blockOf, hd]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact block_wf hL hs ht hd hm
  | skipped hs hd => exact ⟨skip_length hL hs hd, rfl, rfl, rfl⟩

theorem BlockChain.start {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    s<tr.height tt ∧ tr.cell tt s rt=1 := by
  cases h with
  | last s n B hs hp => exact hs.start hL
  | cons s n B hs bs e ht => exact hs.start hL

theorem BlockChain.local {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ B∈bs, if B.dup then B.L=12 ∧ B.path=[] ∧ B.le=0 ∧ B.qe+1=B.ql else BlockWf B := by
  induction h with
  | last s n B hs hp =>
    intro B' hB; obtain rfl := List.mem_singleton.mp hB; exact hs.local hL
  | cons s n B hs bs e ht ih =>
    intro B' hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hs.local hL
    · exact ih B' hB

theorem BlockChain.j_indices {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ k (hk : k<bs.length), bs[k].j=(tr.cell tt s j).toNat+k := by
  induction h with
  | last s n B hs hp =>
    intro k hk
    have hk0 : k=0 := by simp only [List.length_singleton] at hk; omega
    subst k; simpa using hs.j_eq
  | cons s n B hs bs e ht ih =>
    intro k hk
    cases k with
    | zero => simpa using hs.j_eq
    | succ k =>
      have hn := hs.next hL (ht.start hL).1 (ht.start hL).2
      have he := ih k (by simpa using hk)
      rw [hn.1, hs.j_eq] at he
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem BlockChain.q_start {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ hb : 0<bs.length, bs[0].ql=(tr.cell tt s q).toNat+1 := by
  cases h with
  | last s n B hs hp => intro _; exact hs.ql_eq hL
  | cons s n B hs bs e ht => intro _; exact hs.ql_eq hL

/-- Consecutive views use the prior endpoint, including zero-work duplicate skips. -/
theorem BlockChain.q_next {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ k (hk : k+1<bs.length), bs[k+1].ql=bs[k].qe+1 := by
  induction h with
  | last s n B hs hp => intro k hk; simp at hk
  | cons s n B hs bs e ht ih =>
    intro k hk
    cases k with
    | zero =>
      have hn := hs.next hL (ht.start hL).1 (ht.start hL).2
      have he := ht.q_start hL (by simp at hk; omega)
      simpa [hn.2] using he
    | succ k => simpa using ih k (by simpa using hk)

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
