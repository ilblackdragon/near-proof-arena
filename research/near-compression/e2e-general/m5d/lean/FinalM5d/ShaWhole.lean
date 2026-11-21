import FinalM5d.Whole
import ZkFormal.Sha.Sound
import ZkFormal.Sha.Compose

/-!
# FinalM5d.ShaWhole — a SHA-256 digest received in the FINAL AIR is the hash of its senders' bytes

Generic message identification for every SHA-256 consumer of `finalAirS` (`PART`, `SHD`, `MRK`):

* `sha_digest_recv`: a received `SHA_DIGEST (id, len, dg)` was sent by the `SHA` table (table 0,
  the only sender), so by lane L5's closed contract (`sha_digest_contract_closed`) there is a
  message `msg` with `dg = sha256 msg`, `len = |msg|` (as field elements) and, for every position
  `i < |msg|`, a sender of `SHA_BYTES (id, i, msg[i])` somewhere in the AIR;
* the length bound `|msg| ≤ 2^28` (64 bytes per block, at most `2^22` rows);
* **`sha_msg`**: if the consumer's `len` is a natural `L < 2^28` and the senders on `(id, i)` are
  *functional* — every `SHA_BYTES (id, i, b)` with `i < L` has `b = B i` — then
  `dg = sha256 (B 0, …, B (L−1))`.

The functional-sender premise is per consumer (ids are disjoint ranges, positions are row
counters); it is what the table-level `Computed` proofs discharge.
-/

namespace FinalM5d.ShaWhole

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View
open FinalM5d FinalM5d.BusMem FinalM5d.Whole

variable {tr : Trace Fp} {pub : List Fp}

local notation "PR" => 2013265921

theorem tab0 : finalAirS.tables[0]'(by decide) = ZkFormal.Sha.Table.table B_SHA_BYTES B_SHA_DIGEST := rfl

theorem only_SD_send : onlyIn finalAirS B_SHA_DIGEST true [0] = true := by decide +kernel

theorem shaLocal (h : Holds finalAirS pub tr) : ShaLocal tr 0 pub :=
  shaLocal_of_holds h (by decide) tab0

/-- Who sends on `SHA_DIGEST`: the `SHA` table's digest interaction. -/
theorem sha_send_ix {i : Interaction}
    (hi : i ∈ (ZkFormal.Sha.Table.table B_SHA_BYTES B_SHA_DIGEST).interactions) (hb : i.bus = B_SHA_DIGEST)
    (hs : i.send = true) : i = (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[16]! := by
  unfold ZkFormal.Sha.Table.table ZkFormal.Sha.Table.interactions at hi
  rcases List.mem_append.1 hi with h1 | h2
  · obtain ⟨q, -, rfl⟩ := List.mem_map.1 h1
    simp at hs
  · rw [List.mem_singleton] at h2
    subst h2
    rfl

theorem chainStarts_length (t : Nat) : ∀ fuel d, (chainStarts tr t fuel d).length ≤ fuel
  | 0, _ => by simp [chainStarts]
  | fuel + 1, d => by
    unfold chainStarts
    split
    · have := chainStarts_length t fuel (d - 17)
      simp only [List.length_append, List.length_singleton]; omega
    · simp

theorem blockData_length (t s : Nat) : (blockData tr t s).length ≤ 64 := by
  unfold blockData
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem flatMap_len_le {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length ≤ n) :
    ∀ l : List α, (l.flatMap f).length ≤ n * l.length
  | [] => by simp
  | a :: l => by
    have := flatMap_len_le f n hf l
    have := hf a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.mul_succ]; omega

theorem msgOf_length (t d : Nat) : (msgOf tr t d).length ≤ 64 * tr.height t := by
  unfold msgOf chainOf
  have h1 := flatMap_len_le (blockData tr t) 64 (blockData_length t) (chainStarts tr t (tr.height t) d)
  have h2 := chainStarts_length (tr := tr) t (tr.height t) d
  exact Nat.le_trans h1 (Nat.mul_le_mul_left _ h2)

theorem height0_le (h : Holds finalAirS pub tr) : tr.height 0 ≤ 2 ^ 22 := by
  have := (h.logBound 0 (by decide)).2
  rw [tab0] at this
  exact Nat.pow_le_pow_right (by decide) this

/-- **A received SHA-256 digest is the hash of a message whose bytes were all sent.** -/
theorem sha_digest_recv (h : Holds finalAirS pub tr) {m : List Fp}
    (ho : Occ finalAirS tr pub B_SHA_DIGEST false m) :
    ∃ r, r < tr.height 0 ∧ ∃ msg dg : ArenaCore.Bytes, dg = ArenaCore.sha256 msg ∧
      msg.length ≤ 2 ^ 28 ∧
      m = [tr.cell 0 r colId, Fp.ofNat msg.length] ++ dg.map (fun x => Fp.ofNat x.toNat) ∧
      ∀ i, i < msg.length → Occ finalAirS tr pub B_SHA_BYTES true
        [tr.cell 0 r colId, Fp.ofNat i, Fp.ofNat (msg[i]!).toNat] := by
  obtain ⟨t, ht0, ht, r, hr, i, hi, hb, hs, hn, hmv⟩ := occ_in only_SD_send (recv_sent h ho)
  simp only [List.mem_singleton] at ht0
  subst ht0
  rw [tab0] at hi
  have hix := sha_send_ix hi hb hs
  subst hix
  have hm1 : tr.cell 0 r colDmult = 1 :=
    (multNat_one (g := ZkFormal.Sha.Table.E.c colDmult) rfl).1 hn
  obtain ⟨msg, dg, hmem, hdg, hmsg, hbytes⟩ :=
    sha_digest_contract_closed (shaLocal h) B_SHA_BYTES B_SHA_DIGEST hr hm1
  refine ⟨r, hr, msg, dg, hdg, ?_, by rw [← hmv, hmsg], ?_⟩
  · -- the message length bound
    unfold digests at hmem
    obtain ⟨d, -, he⟩ := List.mem_map.1 hmem
    have hl : msg.length = (msgOf tr 0 d).length := by
      have := congrArg (fun p => p.1.length) he
      simp only [List.length_map] at this
      exact this.symm
    have := msgOf_length (tr := tr) 0 d
    have := height0_le h
    omega
  · intro k hk
    obtain ⟨r', hr', q, hq, hf, hmq⟩ := hbytes k hk
    have hiq : (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! ∈
        (finalAirS.tables[0]'(by decide)).interactions := by
      rw [tab0]
      show _ ∈ ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST
      rw [getElem!_pos _ q (by simp [ZkFormal.Sha.Table.interactions]; omega)]
      exact List.getElem_mem _
    have hq' : (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! =
        { bus := B_SHA_BYTES, mult := [ZkFormal.Sha.Table.E.c (colF q)], msg := [ZkFormal.Sha.Table.E.c colId, ZkFormal.Sha.Table.posE q, ZkFormal.Sha.Table.byteE q], send := false } := by
      rw [getElem!_pos _ q (by simp [ZkFormal.Sha.Table.interactions]; omega)]
      simp only [ZkFormal.Sha.Table.interactions]
      rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
    have hn' : ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).multNat tr 0 r' pub ≠ 0 := by
      rw [hq']; exact (multNat_one (g := ZkFormal.Sha.Table.E.c (colF q)) rfl).2 hf
    have ho1 := occ_of (by decide) hr' hiq hn'
    have hb' : ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).bus = B_SHA_BYTES := by rw [hq']
    have hs' : ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).send = false := by rw [hq']
    rw [hb', hs', hmq] at ho1
    exact recv_sent h ho1

theorem ofNat_inj {a b : Nat} (ha : a < PR) (hb : b < PR) (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have := congrArg Fp.toNat h
  rw [Fp.toNat_ofNat, Fp.toNat_ofNat] at this
  have e : ZkFormal.Algebra.P = PR := rfl
  rw [e, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

/-- **SHA-256 message identification.** A consumer that receives `SHA_DIGEST (id, L, dg)` with
`L ≤ 2^28`, where every sender of `SHA_BYTES (id, i, b)` (`i < L`) sends `b = B i`, receives
`dg = sha256 (B 0 ‖ … ‖ B (L−1))`. -/
theorem sha_msg (h : Holds finalAirS pub tr) {id : Fp} {L : Nat} {dgF : List Fp} (hL : L ≤ 2 ^ 28)
    (B : Nat → Nat) (hB : ∀ i, i < L → B i < 256)
    (ho : Occ finalAirS tr pub B_SHA_DIGEST false ([id, Fp.ofNat L] ++ dgF))
    (hsend : ∀ i b, i < L → Occ finalAirS tr pub B_SHA_BYTES true [id, Fp.ofNat i, b] →
      b = Fp.ofNat (B i)) :
    dgF = (ArenaCore.sha256 ((List.range L).map fun i => UInt8.ofNat (B i))).map
      (fun x => Fp.ofNat x.toNat) := by
  obtain ⟨r, hr, msg, dg, hdg, hlen, hm, hbytes⟩ := sha_digest_recv h ho
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hm
  obtain ⟨hid, hl, hd⟩ := hm
  have hL' : L = msg.length := ofNat_inj (by omega) (by omega) hl
  have hmsg : msg = (List.range L).map fun i => UInt8.ofNat (B i) := by
    apply List.ext_getElem
    · simp [hL']
    · intro i h1 h2
      have hi : i < L := by omega
      have := hsend i _ hi (hid ▸ hbytes i h1)
      have hv := ofNat_inj (by have := (msg[i]!).toNat_lt; omega) (by have := hB i hi; omega) this
      rw [getElem!_pos msg i h1] at hv
      simp only [List.getElem_map, List.getElem_range]
      rw [← hv, UInt8.ofNat_toNat]
  rw [hd, hdg, hmsg]

end FinalM5d.ShaWhole
