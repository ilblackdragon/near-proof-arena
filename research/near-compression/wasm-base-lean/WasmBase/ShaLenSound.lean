import WasmBase.ShaSound
import WasmBase.PrepSound

/-!
# WasmBase.ShaLenSound — `HashLenLink` is a theorem of `wasmBaseHashAir` (E2E A-T5)

A-T3 found that the `sha256` host call's summary did not bind the hashed length: the SHA table's
`sh_len` (the call's `len`, constant along a message) and the classical byte counter `Nd` were tied
by no constraint, so a digest row could answer `sha256(len, ptr, reg)` with the digest of a message
of another length (`ShaAir.HashLenLink`, stated, A-T4 §11.5).

A-T5 changes the wire (`ShaAir.lean`):

* the digest row receives `Sha.callMsgL = [ts, hid, sh_len, ptr, reg, Nd, 0, 0]` (count `Dmult`);
* `HOSTO` sends `HostOH.callMsg = [ts, hid, a0, a1, a2, a0, 0, 0]` (`a0 = len`, count `mult·sha`);
* `Dmult` is a bit (`Sha.cDmultB`, as in PREP's table).

**`hashLenLink_of_holds`**: `Holds (wasmBaseHashAir nloc ngl) pub tr → HashLenLink tr 26`.  On a
digest row with `Dmult = 1` the receive is counted once; every receive on bus 211 has a bit count, so
the balance puts a sender of the same message on the bus; the only 8-field sender is `HOSTO`'s summary,
whose fields 2 and 5 are the same `a0`, so `sh_len = a0 = Nd`.

The segment AIR (`wasmBaseSegAirMP`) has no SHA-256 table (a `sha256` call there is answered by the
state side through the σ-pinned host contract), so this change does not touch the segment AIR.
-/

namespace WasmBase
namespace ShaLenSound

open ZkFormal.Algebra Chips

set_option maxRecDepth 100000

/-- No table of `wasmBaseHostAir` has an interaction on bus 211 (the bus is new in `ShaAir`). -/
theorem host_no211 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseHostAir nloc ngl).tables, ∀ i ∈ T.inters, i.bus ≠ busHashCall := by
  intro T hT i hi
  simp only [wasmBaseHostAir, wasmBaseAir, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb : ∀ i ∈ (Boundary.table nloc ngl).inters, i.bus ≠ busHashCall := by
      simp [Boundary.table, Boundary.inters, stateOut, chSend, chRecv, stkRecv, busState, busStk, busHashCall]
      intro a ha
      rcases ha with ⟨_, _, h | h⟩ | ⟨_, _, h⟩ | h <;> subst h <;> simp
    exact hb i hi
  all_goals exact PrepSound.bus_ne_of_all (by decide) hi

/-- The tables of `wasmBaseHashAir`: `HOSTO` replaced by `HostOH`, then `SHA256`. -/
theorem hash_tables (nloc ngl : Nat) {T : Table} (hT : T ∈ (wasmBaseHashAir nloc ngl).tables) :
    T = HostOH.table ∨ T = Sha.table ∨ ∀ i ∈ T.inters, i.bus ≠ busHashCall := by
  simp only [wasmBaseHashAir, List.mem_append, List.mem_map, List.mem_singleton] at hT
  rcases hT with ⟨T', hT', rfl⟩ | rfl
  · split
    · exact .inl rfl
    · exact .inr (.inr (host_no211 nloc ngl T' hT'))
  · exact .inr (.inl rfl)

/-- `HostOH`'s only bus-211 interaction is the summary send. -/
theorem hostoh_211 {i : Inter} (hi : i ∈ HostOH.table.inters) (hb : i.bus = busHashCall) :
    i = ⟨busHashCall, true, v (WasmBase.Chips.HostO.mult) * v HostOH.sha, HostOH.callMsg⟩ := by
  simp only [HostOH.table, HostOH.inters, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact absurd hb (PrepSound.bus_ne_of_all (T := WasmBase.Chips.HostO.table) (by decide) hi)
  · rfl

/-- `SHA256`'s bus-211 interactions: the digest send / receive and the summary receive. -/
theorem sha_211 {i : Inter} (hi : i ∈ Sha.table.inters) (hb : i.bus = busHashCall) :
    i = ⟨busHashCall, true, Sha.dmultE, Sha.digMsg⟩ ∨ i = ⟨busHashCall, false, Sha.dmultE, Sha.digMsg⟩ ∨
      i = ⟨busHashCall, false, Sha.dmultE, Sha.callMsgL⟩ := by
  simp only [Sha.table, Sha.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inl rfl
  · simp [busHashDigest, busHashCall] at hb
  · simp [busHashDigest, busHashCall] at hb
  · exact .inr (.inr rfl)

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseHashAir nloc ngl) pub tr)
include H

/-- `Dmult` is a bit on every row of a `SHA256` table. -/
theorem dmult_bit {t : Nat} (ht : t < (wasmBaseHashAir nloc ngl).tables.length)
    (hT : (wasmBaseHashAir nloc ngl).tables[t]'ht = Sha.table) {r : Nat} (hr : r < tr.height t) :
    tr.cell t r ZkFormal.Sha.Layout.colDmult = 0 ∨ tr.cell t r ZkFormal.Sha.Layout.colDmult = 1 := by
  have c := H.constr t ht r hr Sha.cDmultB (by rw [hT]; simp [Sha.table])
  simp only [Sha.cDmultB, Chips.bool, Sha.dmultE, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_col, Trace.row, v] at c
  grind

/-- **Every occurrence on bus 211** is `HOSTO`'s summary send or a `SHA256` row's digest send /
receive or summary receive (count `Dmult`). -/
theorem occ211 {o : Occ} (ho : o ∈ occs (wasmBaseHashAir nloc ngl) tr pub) (hb : o.1 = busHashCall) :
    (∃ t, ∃ ht : t < (wasmBaseHashAir nloc ngl).tables.length, (wasmBaseHashAir nloc ngl).tables[t]'ht = HostOH.table ∧
      ∃ r, r < tr.height t ∧ o = (busHashCall, true, HostOH.callMsg.map (·.eval (tr.row pub t r)),
        ((v (WasmBase.Chips.HostO.mult) * v HostOH.sha).eval (tr.row pub t r)).toNat)) ∨
    (∃ t, ∃ ht : t < (wasmBaseHashAir nloc ngl).tables.length, (wasmBaseHashAir nloc ngl).tables[t]'ht = Sha.table ∧
      ∃ r, r < tr.height t ∧
        (o = (busHashCall, true, Sha.digMsg.map (·.eval (tr.row pub t r)), (tr.cell t r ZkFormal.Sha.Layout.colDmult).toNat) ∨
         o = (busHashCall, false, Sha.digMsg.map (·.eval (tr.row pub t r)), (tr.cell t r ZkFormal.Sha.Layout.colDmult).toNat) ∨
         o = (busHashCall, false, Sha.callMsgL.map (·.eval (tr.row pub t r)),
           (tr.cell t r ZkFormal.Sha.Layout.colDmult).toNat))) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.1 ho
  simp only at hb
  rcases hash_tables nloc ngl (List.getElem_mem ht) with hT | hT | hT
  · rw [hT] at hi
    have := hostoh_211 hi hb
    subst this
    exact .inl ⟨t, ht, hT, r, hr, rfl⟩
  · rw [hT] at hi
    rcases sha_211 hi hb with rfl | rfl | rfl
    · exact .inr ⟨t, ht, hT, r, hr, .inl rfl⟩
    · exact .inr ⟨t, ht, hT, r, hr, .inr (.inl rfl)⟩
    · exact .inr ⟨t, ht, hT, r, hr, .inr (.inr rfl)⟩
  · exact absurd hb (hT i hi)

theorem hash_t26 : (wasmBaseHashAir nloc ngl).tables[26]'(by rw [hash_air_len]; decide) = Sha.table :=
  hash_air_sha nloc ngl

/-- **`HashLenLink` holds**: on every claiming digest row of the `SHA256` table, `sh_len = Nd`. -/
theorem hashLenLink_of_holds : Sha.HashLenLink tr 26 := by
  classical
  intro r hr hd1
  have ht26 : 26 < (wasmBaseHashAir nloc ngl).tables.length := by rw [hash_air_len]; decide
  let m := Sha.callMsgL.map (·.eval (tr.row pub 26 r))
  have hrecv : ((busHashCall, false, m, (tr.cell 26 r ZkFormal.Sha.Layout.colDmult).toNat) : Occ) ∈
      occs (wasmBaseHashAir nloc ngl) tr pub :=
    mem_occs.2 ⟨26, ht26, r, hr, ⟨busHashCall, false, Sha.dmultE, Sha.callMsgL⟩,
      by rw [hash_air_sha nloc ngl]; simp [Sha.table, Sha.inters], rfl⟩
  have hbits : ∀ o ∈ occs (wasmBaseHashAir nloc ngl) tr pub, o.1 = busHashCall → o.2.1 = false →
      o.2.2.2 ≤ 1 := by
    intro o ho hb hs
    rcases occ211 H ho hb with ⟨t, ht, hT, r', hr', rfl⟩ | ⟨t, ht, hT, r', hr', rfl | rfl | rfl⟩
    · simp at hs
    · simp at hs
    · exact PrepSound.toNat_le_one (dmult_bit H ht hT hr')
    · exact PrepSound.toNat_le_one (dmult_bit H ht hT hr')
  have hge1 : 1 ≤ busNat (wasmBaseHashAir nloc ngl) tr pub busHashCall false m := by
    have := count_le_busNat hrecv rfl rfl rfl
    rw [hd1] at this; exact this
  have hlt := busNat_lt H busHashCall false m (fun o ho hb hs => hbits o ho hb hs)
  have hbal := H.balance busHashCall m
  rw [Nat.mod_eq_of_lt hlt] at hbal
  have hsend : busNat (wasmBaseHashAir nloc ngl) tr pub busHashCall true m ≠ 0 := by
    intro h; rw [h, Nat.zero_mod] at hbal; omega
  unfold busNat at hsend
  obtain ⟨c, hc, hc0⟩ := PrepSound.sum_ne_zero_mem hsend
  obtain ⟨o, hof, rfl⟩ := List.mem_map.1 hc
  obtain ⟨ho, hcond⟩ := List.mem_filter.1 hof
  simp only [decide_eq_true_eq] at hcond
  obtain ⟨hb, hs, hm⟩ := hcond
  rcases occ211 H ho hb with ⟨t, ht, hT, r', hr', rfl⟩ | ⟨t, ht, hT, r', hr', rfl | rfl | rfl⟩
  · -- `HOSTO`'s summary: field 2 is `a0 = len`, field 5 the effective length `elen`, and
    -- `(a0 − (2^64 − 1)) · (elen − a0) = 0`
    simp only at hm
    simp only [m, HostOH.callMsg, Sha.callMsgL, List.map_cons, List.map_nil, List.cons.injEq] at hm
    obtain ⟨-, -, h2, -, -, h5, -⟩ := hm
    have c := H.constr t ht r' hr' HostOH.cElen (by rw [hT]; simp [HostOH.table, HostOH.constraints])
    simp only [HostOH.cElen, Expr.eval_mul', Expr.eval_sub'] at c
    rw [h2, h5] at c
    have ec : ∀ rw : Row, (Expr.c (2 ^ 64 - 1)).eval rw = (((2 ^ 64 - 1 : Nat) : F)) := fun _ => rfl
    simp only [Sha.lenE, Expr.eval_col, v, Trace.row, ec] at c ⊢
    rcases mul_eq_zero' c with h | h
    · right; grind
    · left; grind
  · -- a digest send: 11 fields, not 8
    exfalso
    have := congrArg List.length hm
    simp only [List.length_map, m, Sha.digMsg_len, Sha.callMsgL_len] at this
    omega
  · simp at hs
  · simp at hs

end

#print axioms host_no211
#print axioms occ211
#print axioms hashLenLink_of_holds

end ShaLenSound
end WasmBase
