import WasmBase.StepMem
/-!
# WasmBase.MemIO — the memory-view extension for host byte buffers

`HOSTB` carries the bytes of a host call's `(ptr, len)` buffer.  A **request** byte is read out of
linear memory, so `HostB.inters` emits the space-3 message of `ptr + pos` twice: it consumes the live
message at the byte's producer time `mtp` and re-produces the *same* byte at the row's time `ts`
(`Chips.HostB.memCnt`, with `timeChk ts mtp hp`).  That is the LOAD shape of `StepMem`, and it is the
link from `(ptr, len)` to linear memory.

This file provides the *view* half of that link, i.e. what the re-timing does to `HeapOK`:

* `BufOK` — the statement-level `(ptr, len)` bound (`ptr + len ≤ memBytes`), which is not polynomial;
* `heap_retime` — the analogue of `StepMem.heap_update` for a **read**: the bytes `[ea, ea + w)` keep
  their values, only their producer times change to `t`.  `HeapOK` at `t + 1` follows from `HeapOK`
  at `t` plus "the bytes are live at their old times" — with no change to `s` at all.

## Why the re-timing is not vacuous

`busNat` (`Air.lean`) matches occurrences on `(bus, direction, message)`, so a `chRecv`/`chSend` pair of
the **identical** message contributes `+c` and `−c` to the same bucket and cancels for every `c`.  Such
a pair asserts nothing (`ch_pair_vacuous`).  The link uses `mtp < ts` (`timeChk`), so the produced
message is `encB a bv ts` and the consumed one `encB a bv mtp` with `mtp ≠ ts`; the pair is a real
re-timing, and the CH decomposition absorbs it (`Main/MemIOBus`).

## What the host may do to memory

The host's *effect* is still opaque (`README §14.2`): the Wasm proof is relative to the response
oracle.  What the extension fixes is the **interface**: the buffer bytes a request reads are the live
memory bytes, and the read leaves memory unchanged.  `HostStepRely`'s heap field is then discharged by
`heap_retime` rather than assumed (`Main/HostRel.host_rel_restart_buf`).
-/
namespace WasmBase

open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-! ## The statement-level buffer bounds -/

/-- **The `(ptr, len)` bound.**  `ptr` and `len` are each range-checked by the AIR (`ptr < 2^27`,
`len < 2^16`), but their *sum* is not a polynomial constraint, so "the buffer is inside memory" is a
statement-level premise — exactly like `memBytes s0 ≤ 2^27` in `Main/MemInit`.  It is what puts the
re-timed addresses in bounds. -/
def BufOK (s : St) (ptr len : Nat) : Prop :=
  ptr + len ≤ memBytes s

theorem BufOK.mono {s s' : St} {ptr len : Nat} (h : BufOK s ptr len) (hpg : s'.pages = s.pages) :
    BufOK s' ptr len := by
  unfold BufOK at h ⊢
  rwa [memBytes_congr hpg]

/-- A byte of a `BufOK` buffer is in bounds. -/
theorem BufOK.addr_lt {s : St} {ptr len i : Nat} (h : BufOK s ptr len) (hi : i < len) :
    ptr + i < memBytes s := by
  unfold BufOK at h; omega

/-! ## Re-timing the producer times of a byte range -/

/-- The re-timed messages are the same bytes at new times: a request byte of the buffer is *unchanged*
in value, so the `HeapOK` update only touches `tpm`. -/
theorem heap_retime_readByte {E : Env} {s : St} {t ea w : Nat} (H : HeapOK E s t)
    (bv tb : Nat → Nat) (hlive : ∀ i, i < w → E.live (encB (ea + i) (bv i) (tb i)))
    {i : Nat} (hi : i < w) :
    bv i = (readByte s (ea + i)).toNat := by
  obtain ⟨T, tpm, -, -, -, hv⟩ := H.mem
  obtain ⟨a', ha', he⟩ := mem_memView.mp ((hv _ rfl).mp (hlive i hi))
  obtain ⟨e1, e2, -⟩ := encB_inj he
  subst e1
  exact e2

/-- **The heap after a *read* of the bytes `[ea, ea + w)`.**  This is `StepMem.heap_update`'s
counterpart for a read: the values are unchanged (the state stays `s`), only the producer time of each
byte in the range moves to `t`.  The proof is `heap_update`'s with `s' = s`: the consumed messages are
the `memView` entries of their addresses, so the `tpm` map updated on the range is again a `memView` of
the *same* memory.

This is what makes the `HOSTB` memory link sound: a request byte does not change memory, it only
re-times the byte it read. -/
theorem heap_retime {E : Env} {s : St} {t ea w : Nat} (H : HeapOK E s t)
    (bv tb : Nat → Nat) (hlive : ∀ i, i < w → E.live (encB (ea + i) (bv i) (tb i))) :
    HeapOK { E with live := (stepLive E.live ((List.range w).map fun i => encB (ea + i) (bv i) (tb i))
        ((List.range w).map fun i => encB (ea + i) (bv i) t)) } s (t + 1) := by
  -- a read is `heap_update` with the values unchanged: `s' = s`, `nb = bv`
  have hnew : ∀ i, i < w → (readByte s (ea + i)).toNat = bv i := by
    intro i hi
    exact (heap_retime_readByte H bv tb hlive hi).symm
  exact heap_update (s' := s) H H.pages rfl rfl (fun _ _ => rfl) bv tb bv hlive hnew

/-- **A same-time `recv`/`send` pair of the identical message cancels identically.**  This is the
vacuous device the link must *not* use: `busNat` keys on `(bus, direction, message)`, so a recv and a
send of the same message are `−c` and `+c` in the same bucket, with no constraint on `c`.  Recorded
because the obvious-looking cheap design is exactly this, and it proves nothing. -/
theorem ch_pair_vacuous (c : Int) : -c + c = 0 := by
  omega

end WasmBase
