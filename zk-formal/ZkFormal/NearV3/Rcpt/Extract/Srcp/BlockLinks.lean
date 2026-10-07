import ZkFormal.NearV3.Rcpt.Extract.Srcp.Blocks

/-! Natural counter links between consecutive parsed source-proof blocks. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem block_end_list (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m) :
    ∀ x ∈ listConst, tr.cell tt (s + 32 + 64 * m) x = tr.cell tt s x := by
  obtain ⟨hH, hu, -, -, hc⟩ := root_leaf_unit hL hs ht
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := (local_ hL (r := s + 1) (by omega)).1
    rw [(afterRoot hL (by omega) ht).1] at he; grind
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 31 (by omega)
  intro x hx
  rw [hm.list x hx, show s + 32 = s + 1 + 31 by omega, hrows.2.2.2.1 x hx, hc x hx]

theorem block_end_q (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m) :
    (tr.cell tt (s + 32 + 64 * m) q).toNat = (blockOf tr tt s m).lastQ := by
  have hend := listEnd hL hm.bound hm.sl_end hm.stop
  rw [hend.1, block_end_list hL hs ht hm qe (by simp [listConst])]
  exact (block_wf hL hs ht hm).root.1

/-- List numbers advance by one while the next root carries the last message number. -/
theorem block_next (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m)
    (hn : s + 33 + 64 * m < tr.height tt) (hnt : tr.cell tt (s + 33 + 64 * m) rt = 1) :
    (tr.cell tt (s + 33 + 64 * m) j).toNat = (tr.cell tt s j).toNat + 1 ∧
    (tr.cell tt (s + 33 + 64 * m) q).toNat = (blockOf tr tt s m).lastQ := by
  have he : s + 32 + 64 * m + 1 = s + 33 + 64 * m := by omega
  have hj := list_j_succ hL (r := s + 32 + 64 * m) (by omega) hm.sl_end (by simpa [he] using hnt)
  have hq := (afterSegRt hL (r := s + 32 + 64 * m) (by omega) hm.sl_end (by simpa [he] using hnt)).1
  rw [he, block_end_list hL hs ht hm j (by simp [listConst])] at hj
  rw [he] at hq
  exact ⟨hj, (congrArg Fp.toNat hq).trans (block_end_q hL hs ht hm)⟩

theorem BlockChain.local {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    ∀ B ∈ bs, BlockWf B := by
  induction hc with
  | last s m hs ht hm hp =>
    intro B hB
    obtain rfl := List.mem_singleton.mp hB
    exact block_wf hL hs ht hm
  | cons s m hs ht hm bs e hc ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact block_wf hL hs ht hm
    · exact ih B hB

theorem BlockChain.j_indices {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    ∀ k (hk : k < bs.length), bs[k].j = (tr.cell tt s j).toNat + k := by
  induction hc with
  | last s m hs ht hm hp =>
    intro k hk
    have hk0 : k = 0 := by simp only [List.length_singleton] at hk; omega
    subst k; rfl
  | cons s m hs ht hm bs e hc ih =>
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      have hn := block_next hL hs ht hm hc.start.1 hc.start.2
      have he := ih k (by simpa using hk)
      rw [hn.1] at he
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem BlockChain.q_start {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    ∀ h : 0 < bs.length, bs[0].ql = (tr.cell tt s q).toNat + 1 := by
  cases hc with
  | last s m hs ht hm hp =>
    intro _; exact root_q_succ hL (root_not_last hL hs ht) ht
  | cons s m hs ht hm bs e hc =>
    intro _; exact root_q_succ hL (root_not_last hL hs ht) ht

theorem BlockChain.q_next {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    ∀ k (hk : k + 1 < bs.length), bs[k + 1].ql = bs[k].lastQ + 1 := by
  induction hc with
  | last s m hs ht hm hp => intro k hk; simp at hk
  | cons s m hs ht hm bs e hc ih =>
    intro k hk
    cases k with
    | zero =>
      have hn := block_next hL hs ht hm hc.start.1 hc.start.2
      have he := BlockChain.q_start hL hc (by simp at hk; omega)
      simpa [hn.2] using he
    | succ k => simpa using ih k (by simpa using hk)

end ZkFormal.NearV3.SrcpProof
