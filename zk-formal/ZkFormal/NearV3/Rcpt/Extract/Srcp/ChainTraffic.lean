import ZkFormal.NearV3.Rcpt.Extract.Srcp.BlockLinks

/-! Aggregate block traffic, size charges, and canonical well-formedness. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem BlockChain.wf {bs : List SrcpB} {e : Nat} (hc : BlockChain tr tt 0 bs e) : SrcpWf bs := by
  have h0 := row0 hL hc.start.1
  have hw := BlockChain.local hL hc
  constructor
  · exact hc.nonempty
  · intro k hk
    have hj := BlockChain.j_indices hL hc k hk
    rw [h0.2.1] at hj
    simpa [show (0 : Fp).toNat = 0 from rfl] using hj
  · intro h
    have hq := BlockChain.q_start hL hc h
    rw [h0.2.2.1] at hq
    simpa [show (0 : Fp).toNat = 0 from rfl] using hq
  · exact BlockChain.q_next hL hc
  · intro B hB; exact (hw B hB).items
  · intro B hB; exact (hw B hB).root
  · intro B hB; exact (hw B hB).dup
  · intro B hB; exact (hw B hB).len
  · intro B hB; exact (hw B hB).canon
  · have hb := hc.bound.2
    have hr := hc.rows
    have hh := height_le hL
    unfold SrcpV3.maxLog
    omega

/-- Exact aggregate traffic before padding, for all buses other than SIZE. -/
theorem BlockChain.traffic {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e)
    (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowSpan tr tt pub s (srcpRows bs) bb sd =
      (bs.flatMap fun B => srcpBlockMsgs B bb sd).map Msg.toFp := by
  induction hc with
  | last s m hs ht hm hp =>
    simpa [srcpRows, blockOf, pathItems] using block_traffic hL hs ht hm bb hb sd
  | cons s m hs ht hm bs e hc ih =>
    have hr : srcpRows (blockOf tr tt s m :: bs) = 33 + 64 * m + srcpRows bs := by
      simp [srcpRows, blockOf, pathItems]
    rw [hr, rowSpan_add, block_traffic hL hs ht hm bb hb sd,
      show s + (33 + 64 * m) = s + 33 + 64 * m by omega, ih]
    simp

/-- Natural aggregate charges before padding are the view's source-proof byte total. -/
theorem BlockChain.size {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    chargeSpan tr tt s (srcpRows bs) = srcpSize bs := by
  induction hc with
  | last s m hs ht hm hp =>
    simpa [srcpRows, srcpSize, blockOf, pathItems] using block_size hL hs ht hm
  | cons s m hs ht hm bs e hc ih =>
    have hr : srcpRows (blockOf tr tt s m :: bs) = 33 + 64 * m + srcpRows bs := by
      simp [srcpRows, blockOf, pathItems]
    rw [hr, chargeSpan_add, block_size hL hs ht hm,
      show s + (33 + 64 * m) = s + 33 + 64 * m by omega, ih]
    simp [srcpSize]

theorem sl_sg {r : Nat} (hr : r < tr.height tt) (hl : tr.cell tt r sl = 1) :
    tr.cell tt r sg = 1 := by
  obtain ⟨-, -, -, hw, -, hs, -⟩ := local_ hL hr
  rcases isBool hL hr (x := wl) (by simp [bools]) with h | h
  · rw [hs, h] at hl; exact False.elim (by grind)
  · exact (hw h).1

theorem BlockChain.last_active {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    tr.cell tt (e - 1) sg = 1 := by
  induction hc with
  | last s m hs ht hm hp =>
    rw [show s + 33 + 64 * m - 1 = s + 32 + 64 * m by omega]
    exact sl_sg hL hm.bound hm.sl_end
  | cons s m hs ht hm bs e hc ih => exact ih

/-- Padding contributes no messages, regardless of the values in inactive payload cells. -/
theorem padding_traffic {r : Nat} (hr : r < tr.height tt)
    (ht : tr.cell tt r rt = 0) (hs : tr.cell tt r sg = 0) (bb : Nat) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt r pub bb sd = [] := by
  obtain ⟨-, -, hw, hl, -, heSl, -, -, -, heGd, -, -, -, hz⟩ := local_ hL hr
  have hw0 : tr.cell tt r wf = 0 := by
    rcases isBool hL hr (x := wf) (by simp [bools]) with h | h
    · exact h
    · have he := (hw h).1; rw [hs] at he; exact False.elim (by simpa using he)
  have hl0 : tr.cell tt r wl = 0 := by
    rcases isBool hL hr (x := wl) (by simp [bools]) with h | h
    · exact h
    · have he := (hl h).1; rw [hs] at he; exact False.elim (by simpa using he)
  have hsl0 : tr.cell tt r sl = 0 := by rw [heSl, hl0]; grind
  have hg0 : tr.cell tt r gD = 0 := by rw [heGd, ht, hw0]; grind
  have hz0 : tr.cell tt r gz = 0 := by
    rcases isBool hL hr (x := gz) (by simp [bools]) with h | h
    · exact h
    · have he := hz h; rw [hsl0] at he; exact False.elim (by simpa using he)
  rw [rowT, ht, hs, hg0, hz0]
  simp

/-- Two descriptions of the final active row have the same endpoint. -/
theorem BlockChain.end_eq {s e K : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e)
    (hK : 0 < K) (hKH : K ≤ tr.height tt)
    (ha : ∀ r, r < K → tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1)
    (hp : ∀ r, K ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0) : e = K := by
  have he := hc.bound
  have heK : e ≤ K := by
    apply Classical.byContradiction; intro hn
    have hz := (hp (e - 1) (by omega) (by omega)).2
    have hlast := BlockChain.last_active hL hc
    rw [hz] at hlast; exact absurd hlast (by decide)
  have hKe : K ≤ e := by
    apply Classical.byContradiction; intro hn
    have hz := hc.padding e (by omega) (by omega)
    rcases ha e (by omega) with h | h <;> simp_all
  omega

end ZkFormal.NearV3.SrcpProof
