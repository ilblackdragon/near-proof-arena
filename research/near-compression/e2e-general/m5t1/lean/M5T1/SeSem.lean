import M5T1.Se
import M5T1.RbSem

/-!
# M5T1.SeSem — the STATE engine half's boundary rules, on any satisfying trace (F-5)

`SE` (table 0 of `Se.fullSe xtape`) carries `Se.cons` on row 0 over the public boundary pair
(`B_in` = 450 B engine record at offset 0, `B_out` = 450 B engine record at offset 450). On every
`Holds (Se.fullSe xtape)` trace:

* `se_phase`: an input record `B` that is the public `B_in` has `phase 1`;
* **`se_out`**: an engine record `B'` whose copied fields (`Se.seRule … = .copy`) are `B`'s, whose
  constant fields are the rules' constants (`phase 1`, out of a call, `rPrepaid = rBurnt = rUsed =
  0`, `vmAcc = bdigest []`), and whose free fields (`stRoot`, the counters, the accumulators) are
  the public `B_out`'s bytes, **is** the public `B_out`: `B'.encode = bytesOf pub 450 450`;
* `se_gas`: the public `B_out` has `gasUsed = gasBurnt` (byte for byte).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false

namespace M5T1.SeSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd
open ArenaCore.Bytes (beN beN_length beToNat beToNat_beN)

abbrev Tp := List (Nat × Bool × List Nat)

/-! ## 1. Row 0 of `SE` -/

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
include H

theorem se_row0 : ∀ e ∈ Se.table.constraints, ev tr 0 0 pub e = 0 := by
  intro e he
  have hpos : 0 < tr.height 0 := by unfold Trace.height; exact Nat.two_pow_pos _
  exact ev_of_eval (H.constr 0 (by simp [Se.fullSe, Se.seAir]) 0 hpos e he)

omit H in
theorem mem_field {p : String × Nat} (hp : p ∈ engF) {e : Expr}
    (he : e ∈ ruleCons Se.SI Se.SO p.1 p.2 (Se.seRule p.1)) : e ∈ Se.table.constraints := by
  show e ∈ Se.cons
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, he⟩))

omit H in
theorem si_b (f : String) (j : Nat) : Se.SI.b f j = .pub (engF.off f + j) := by
  simp [Se.SI, Side.b]

omit H in
theorem so_b (f : String) (j : Nat) : Se.SO.b f j = .pub (450 + engF.off f + j) := by
  simp [Se.SO, Side.b]

/-- A copied field equals the input's, byte for byte. -/
theorem copy_sem {p : String × Nat} (hp : p ∈ engF) (hr : Se.seRule p.1 = .copy) :
    ∀ j < fw engF p.1, pv pub (engF.off p.1 + j) = pv pub (450 + engF.off p.1 + j) := by
  intro j hj
  have hm : gate (Se.SI.b p.1 j - Se.SO.b p.1 j) ∈ ruleCons Se.SI Se.SO p.1 p.2 (Se.seRule p.1) := by
    rw [hr]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have h := se_row0 H _ (mem_field hp hm)
  rw [si_b, so_b] at h
  exact gate_pub_eq h

/-- A constant field's little-endian byte `k`. -/
theorem num_sem {p : String × Nat} (hp : p ∈ engF) {v : Nat} (hr : Se.seRule p.1 = .num v) :
    ∀ k < fw engF p.1, pv pub (450 + engF.off p.1 + (fw engF p.1 - 1 - k)) = v / 256 ^ k % 256 := by
  intro k hk
  have hm : gate (Se.SO.le p.1 k - K (v / 256 ^ k % 256)) ∈ ruleCons Se.SI Se.SO p.1 p.2 (Se.seRule p.1) := by
    rw [hr]; exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  have h := se_row0 H _ (mem_field hp hm)
  simp only [Side.le, so_b] at h
  exact gate_const_eq (by have := Nat.mod_lt (v / 256 ^ k) (show 0 < 256 by decide); omega) h

/-- A constant digest field is the constant bytes. -/
theorem dig_sem {p : String × Nat} (hp : p ∈ engF) (hr : Se.seRule p.1 = .dig emptyDig) :
    ∀ j < p.2, pv pub (450 + engF.off p.1 + j) = emptyDig.getD j 0 := by
  intro j hj
  have hm : gate (Se.SO.b p.1 j - K (emptyDig.getD j 0)) ∈ ruleCons Se.SI Se.SO p.1 p.2 (Se.seRule p.1) := by
    rw [hr]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have h := se_row0 H _ (mem_field hp hm)
  rw [so_b] at h
  exact gate_const_eq (by have := emptyDig_lt j; omega) h

/-- The input record's phase bytes are `1`. -/
theorem in_phase : bytesOf pub 42 8 = beN 8 1 := by
  apply bytesOf_num
  intro k hk
  have hm : gate (Se.SI.le "phase" k - K (1 / 256 ^ k % 256)) ∈ Se.table.constraints := by
    show _ ∈ Se.cons
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))))
  have h := se_row0 H _ hm
  simp only [Side.le, Side.b] at h
  have := gate_const_eq (by have := Nat.mod_lt (1 / 256 ^ k) (show 0 < 256 by decide); omega) h
  have e : Se.SI.base + Se.SI.L.off "phase" + (fw Se.SI.L "phase" - 1 - k) = 42 + (8 - 1 - k) := by
    have e1 : engF.off "phase" = 42 := by decide
    have e2 : fw engF "phase" = 8 := by decide
    simp only [Se.SI, e1, e2]
  rw [e] at this
  exact this

/-- **`gasUsed = gasBurnt` in the public output** (`clearE`: both are the receipt state's gas). -/
theorem se_gas : bytesOf pub (450 + engF.off "gasUsed") 8 = bytesOf pub (450 + engF.off "gasBurnt") 8 := by
  apply bytesOf_congr
  intro j hj
  have hm : gate (Se.SO.b "gasUsed" j - Se.SO.b "gasBurnt" j) ∈ Se.table.constraints := by
    show _ ∈ Se.cons
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have h := se_row0 H _ hm
  rw [so_b, so_b] at h
  exact gate_pub_eq h
end

/-! ## 2. Records -/

/-- The input record of an accepted STATE engine half has phase `1`. -/
theorem se_phase {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
    {B : BndRec} (hwf : B.WF) (he : B.encode = bytesOf pub 0 450) : B.phase = 1 := by
  obtain ⟨rest, hr⟩ := enc_prefix B
  have hcd : B.claimDigest.length = 42 := hwf.1.1
  have hph : B.phase < 256 ^ 8 := hwf.1.2.1
  rw [hr, show (450 : Nat) = 42 + (8 + 400) from rfl, bytesOf_add, bytesOf_add] at he
  obtain ⟨-, he⟩ := List.append_inj he (by rw [hcd, bytesOf_length])
  obtain ⟨he, -⟩ := List.append_inj he (by rw [beN_length, bytesOf_length])
  rw [in_phase H] at he
  have := congrArg beToNat he
  rw [beToNat_beN, beToNat_beN, Nat.mod_eq_of_lt hph] at this
  simpa using this

/-- An engine record's fields, from its encoding at offset `a`. -/
theorem fields_eng {pub : List Fp} {B : BndRec} (hwf : B.WF) (hw : B.wasm = none) {d : ArenaCore.Bytes}
    (ho : B.outRcptAcc = [d]) {a : Nat} (he : B.encode = bytesOf pub a 450) :
    ∀ p ∈ engF, recVal B p.1 = bytesOf pub (a + engF.off p.1) p.2 := by
  rw [enc_eng _ hw ho, show (450 : Nat) = engF.width from by decide, bytesOf_lay pub engF a engF_nodup]
    at he
  have := flat_inj engF _ _ (·.2) (len_eng hwf hw ho) (fun p _ => bytesOf_length _ _ _) he
  simpa using this

/-- The fields `SE` copies from the input. -/
def copied : List String := ["claimDigest", "blockIdx", "actionIdx", "t", "ctxRoot", "outRcptN", "bwAcc"]

/-- The fields `SE` leaves to the step's owners (`stRoot`: lane B's `STC` on `STMA`; the
receipt-state counters and the accumulators: the step contract). -/
def free : List String :=
  ["stRoot", "receiptIdx", "gasUsed", "gasBurnt", "compute", "balanceBurnt", "outcomeAcc", "outRcpt0",
   "proposalsAcc"]

attribute [local irreducible] bdigest in
/-- **The STATE engine half's output record** (module header). -/
theorem se_out {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
    {B B' : BndRec} (hwf : B.WF) (hw : B.wasm = none) {d : ArenaCore.Bytes} (ho : B.outRcptAcc = [d])
    (he : B.encode = bytesOf pub 0 450)
    (hwf' : B'.WF) (hw' : B'.wasm = none) {d' : ArenaCore.Bytes} (ho' : B'.outRcptAcc = [d'])
    (hcopy : ∀ f ∈ copied, recVal B' f = recVal B f)
    (hph : B'.phase = 1) (hic : B'.inCall = false) (hrp : B'.rPrepaid = 0) (hrb : B'.rBurnt = 0)
    (hru : B'.rUsed = 0) (hvm : B'.vmAcc = bdigest [])
    (hfree : ∀ p ∈ engF, p.1 ∈ free → recVal B' p.1 = bytesOf pub (450 + engF.off p.1) p.2) :
    B'.encode = bytesOf pub 450 450 := by
  have hin := fields_eng hwf hw ho he
  rw [enc_eng _ hw' ho', show bytesOf pub 450 450 = bytesOf pub 450 engF.width by rw [engF_width],
    bytesOf_lay pub engF 450 engF_nodup]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hfw : fw engF p.1 = p.2 := by
    simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hc : Se.seRule p.1 = .copy → p.1 ∈ copied → recVal B' p.1 = bytesOf pub (450 + engF.off p.1) p.2 := by
    intro hr hm
    rw [hcopy _ hm, hin p hp]
    exact bytesOf_congr (fun j hj => by simpa using copy_sem H hp hr j (hfw ▸ hj))
  have hn : ∀ v, Se.seRule p.1 = .num v → bytesOf pub (450 + engF.off p.1) p.2 = beN p.2 v := by
    intro v hr
    apply bytesOf_num
    intro k hk
    have := num_sem H hp hr k (hfw ▸ hk)
    rwa [hfw] at this
  have hd : Se.seRule p.1 = .dig emptyDig → p.2 = 42 → bytesOf pub (450 + engF.off p.1) p.2 = bdigest [] := by
    intro hr h42
    rw [emptyDig_eq, h42]
    exact bytesOf_dig pub _ emptyDig (fun j hj => dig_sem H hp hr j (by rw [h42]; exact hj))
  have hf : p.1 ∈ free → recVal B' p.1 = bytesOf pub (450 + engF.off p.1) p.2 := hfree p hp
  have hwt : recVal B' "wasmTag" = [0] := by simp [recVal, hw']
  simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc rfl (by decide)
  · show beN 8 B'.phase = _; rw [hph, hn 1 rfl]
  · exact hc rfl (by decide)
  · exact hf (by decide)
  · exact hc rfl (by decide)
  · show [if B'.inCall then 1 else 0] = _; rw [hic, hn 0 rfl]; rfl
  · exact hc rfl (by decide)
  · exact hf (by decide)
  · exact hc rfl (by decide)
  · exact hf (by decide)
  · exact hf (by decide)
  · exact hf (by decide)
  · exact hf (by decide)
  · show beN 8 B'.rPrepaid = _; rw [hrp, hn 0 rfl]
  · show beN 8 B'.rBurnt = _; rw [hrb, hn 0 rfl]
  · show beN 8 B'.rUsed = _; rw [hru, hn 0 rfl]
  · exact hf (by decide)
  · exact hc rfl (by decide)
  · exact hf (by decide)
  · exact hf (by decide)
  · exact hc rfl (by decide)
  · show B'.vmAcc = _; rw [hvm, hd rfl rfl]
  · rw [hwt, hn 0 rfl]; rfl

#print axioms se_out
#print axioms se_gas
#print axioms se_phase

end M5T1.SeSem
