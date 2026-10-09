import ZkFormal.NearV3.Rcpt.Extract.Srcp.BlockSize

/-! Parse the entire remaining source-proof table into consecutive complete blocks. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

/-- A concrete block decomposition terminating at padding or the physical table end. -/
inductive BlockChain (tr : Trace Fp) (tt : Nat) : Nat → List SrcpB → Nat → Prop
  | last (s m : Nat) (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
      (hm : PathRun tr tt (s + 32) m)
      (hpad : ∀ r, s + 33 + 64 * m ≤ r → r < tr.height tt →
        tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0) :
      BlockChain tr tt s [blockOf tr tt s m] (s + 33 + 64 * m)
  | cons (s m : Nat) (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
      (hm : PathRun tr tt (s + 32) m) (bs : List SrcpB) (e : Nat)
      (tail : BlockChain tr tt (s + 33 + 64 * m) bs e) :
      BlockChain tr tt s (blockOf tr tt s m :: bs) e

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem padding_from {s : Nat} (hs : s < tr.height tt)
    (ht : tr.cell tt s rt = 0) (hg : tr.cell tt s sg = 0) :
    ∀ r, s ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0 := by
  have gen : ∀ d, s + d < tr.height tt →
      tr.cell tt (s + d) rt = 0 ∧ tr.cell tt (s + d) sg = 0 := by
    intro d
    induction d with
    | zero => intro _; simpa using And.intro ht hg
    | succ d ih =>
      intro hd
      have hp := ih (by omega)
      simpa only [Nat.add_assoc] using padStep hL (r := s + d) (by omega) hp.1 hp.2
  intro r hr hH
  simpa [Nat.add_sub_cancel' hr] using gen (r - s) (by omega)

/-- Every root begins a finite chain of complete source-proof blocks. -/
theorem blocks_from {s : Nat} (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) :
    ∃ bs e, BlockChain tr tt s bs e := by
  have gen : ∀ fuel s, tr.height tt - s ≤ fuel → s < tr.height tt → tr.cell tt s rt = 1 →
      ∃ bs e, BlockChain tr tt s bs e := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro s hf hs ht
      obtain ⟨m, hm⟩ := block_path_run hL hs ht
      have heH : s + 33 + 64 * m ≤ tr.height tt := by have := hm.bound; omega
      by_cases he : s + 33 + 64 * m < tr.height tt
      · have hnsg : tr.cell tt (s + 33 + 64 * m) sg = 0 := by
          have hz := hm.stop
          rw [show s + 32 + 64 * m + 1 = s + 33 + 64 * m by omega, Nat.mod_eq_of_lt he] at hz
          exact hz
        rcases isBool hL he (x := rt) (by simp [bools]) with hrt | hrt
        · exact ⟨_, _, BlockChain.last s m hs ht hm (padding_from hL he hrt hnsg)⟩
        · obtain ⟨bs, e, hc⟩ := ih (tr.height tt - (s + 33 + 64 * m)) (by omega)
            (s + 33 + 64 * m) (by omega) he hrt
          exact ⟨_, _, BlockChain.cons s m hs ht hm bs e hc⟩
      · exact ⟨_, _, BlockChain.last s m hs ht hm (by intro r hr hrH; omega)⟩
  exact gen (tr.height tt - s) s (by omega) hs ht

omit hL in
theorem BlockChain.start {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    s < tr.height tt ∧ tr.cell tt s rt = 1 := by
  cases hc <;> exact ⟨by assumption, by assumption⟩

omit hL in
theorem BlockChain.nonempty {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) : bs ≠ [] := by
  cases hc <;> simp

omit hL in
/-- The endpoint and semantic row count agree exactly. -/
theorem BlockChain.rows {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    e = s + srcpRows bs := by
  induction hc with
  | last s m hs ht hm hp => simp [srcpRows, blockOf, pathItems, Nat.add_assoc]
  | cons s m hs ht hm bs e hc ih =>
    rw [ih]
    simp [srcpRows, blockOf, pathItems, Nat.add_assoc]

omit hL in
theorem BlockChain.bound {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    s < e ∧ e ≤ tr.height tt := by
  induction hc with
  | last s m hs ht hm hp => have := hm.bound; omega
  | cons s m hs ht hm bs e hc ih => omega

omit hL in
theorem BlockChain.padding {s e : Nat} {bs : List SrcpB} (hc : BlockChain tr tt s bs e) :
    ∀ r, e ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0 := by
  induction hc with
  | last s m hs ht hm hp => exact hp
  | cons s m hs ht hm bs e hc ih => exact ih

end ZkFormal.NearV3.SrcpProof
