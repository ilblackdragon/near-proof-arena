import ZkFormal.Chacha.Bus
import ZkFormal.V2.Verifier
import ZkFormal.Chacha.Rng.Sound

/-!
# ZkFormal.Chacha.Link — the tables inside a v2 AIR

From `HoldsP AP pub tr` with the ChaCha table at index `tc` (the only sender on
`busChacha`) and the stream table at index `tg`:
`chLocal_of_holdsP`, `gLocal_of_holdsP`, and `chachaRecv_of_holdsP` (the receive hypothesis
of `genIndex_contract`), hence `genIndex_sound`.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem tables_get {AP : AirP} {t : Nat} (ht : t < AP.tables.length) : AP.tables[t]! = AP.tables[t] := by
  simp [ht]

theorem local_of_holdsP (hH : HoldsP AP pub tr) {t : Nat} (ht : t < AP.tables.length) :
    Local AP.tables[t]!.constraints tr t pub := by
  intro r hr e he
  rw [tables_get ht] at he
  exact hH.constr t ht r hr e he

theorem chLocal_of_holdsP (hH : HoldsP AP pub tr) {tc busChacha : Nat} (ht : tc < AP.tables.length)
    (hT : AP.tables[tc]! = Table.table busChacha) : Sound.ChLocal tr tc pub where
  log_ge := (hH.logBound tc ht).1
  log_le := by have := (hH.logBound tc ht).2; rw [← tables_get ht, hT] at this; exact this
  constr := fun r hr e he => by
    have := local_of_holdsP hH ht r hr e; rw [hT] at this; exact this he

theorem gLocal_of_holdsP (hH : HoldsP AP pub tr) {tg busChacha busGen : Nat} (ht : tg < AP.tables.length)
    (hT : AP.tables[tg]! = Rng.Table.table busChacha busGen) : Rng.GLocal tr tg pub := by
  have := local_of_holdsP hH ht; rw [hT] at this; exact this

theorem multNat_one_col {tr : Trace Fp} {t r : Nat} {pub : List Fp} {i : Interaction} {x : Nat}
    (hi : i.mult = [Table.E.c x]) (h : cv tr t r x = 1) : i.multNat tr t r pub ≠ 0 := by
  unfold Interaction.multNat
  rw [hi]
  simp only [Interaction.multNat.go]
  have : (Table.E.c x).eval tr t r pub = 1 := by
    show tr.cell t r x = 1
    unfold cv at h; rw [← Fp.ofNat_toNat (tr.cell t r x), h]; rfl
  simp [this]

/-- **The ChaCha receives of the stream table are ChaCha20 outputs.** -/
theorem chachaRecv_of_holdsP (hH : HoldsP AP pub tr) {tc tg busChacha busGen : Nat}
    (htc : tc < AP.tables.length) (hTc : AP.tables[tc]! = Table.table busChacha)
    (htg : tg < AP.tables.length) (hTg : AP.tables[tg]! = Rng.Table.table busChacha busGen)
    (honly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = busChacha → i.send = false)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus = busChacha → seg.send = false) :
    Rng.ChachaRecv tr tg pub busChacha busGen := by
  intro r hr ha
  have hi : (Rng.Table.interactions busChacha busGen).head! ∈ AP.tables[tg]!.interactions := by
    rw [hTg]; show _ ∈ Rng.Table.interactions busChacha busGen
    unfold Rng.Table.interactions; exact List.mem_cons_self ..
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := recv_matched hH htc honly hpub htg hr hi rfl rfl
    (multNat_one_col rfl ha)
  rw [hTc] at hi'
  obtain ⟨key, ctr, idx, hk, hkey, hc, hidx, -, -, hmv⟩ :=
    Sound.chacha_contract (chLocal_of_holdsP hH htc hTc) busChacha hr' hi' hm'
  exact ⟨key, ctr, idx, hk, hkey, hc, hidx, by rw [← Rng.recvMsg_eq busChacha busGen, ← hmsg, hmv]⟩

/-- **`genIndex` soundness inside a v2 AIR.** -/
theorem genIndex_sound (hH : HoldsP AP pub tr) {tc tg busChacha busGen : Nat}
    (htc : tc < AP.tables.length) (hTc : AP.tables[tc]! = Table.table busChacha)
    (htg : tg < AP.tables.length) (hTg : AP.tables[tg]! = Rng.Table.table busChacha busGen)
    (honly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = busChacha → i.send = false)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus = busChacha → seg.send = false)
    {r : Nat} (hr : r < tr.height tg) (hacc : cv tr tg r Rng.Table.colAcc = 1) :
    ∃ key kstart n j kend, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ 1 ≤ n ∧ n < 2 ^ 14 ∧
      kstart < 2013265921 ∧ kend < 2 ^ 30 + 1 ∧ genAt 64 n key kstart = some (j, kend) ∧
      genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend) ∧
      (Rng.Table.interactions busChacha busGen)[1]!.msgVal tr tg r pub = Rng.genMsg key kstart n j kend :=
  Rng.genIndex_contract (gLocal_of_holdsP hH htg hTg)
    (chachaRecv_of_holdsP hH htc hTc htg hTg honly hpub) hr hacc

end ZkFormal.Chacha
