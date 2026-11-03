import StateM5a.SnFinal6
import StateM5a.StSoundF

/-!
# StateM5a.M5bFinal — the batched FINAL of the M5b AIR, end to end (M5a-7)

**`m5b_final`**: from `Holds` of the AIR the prover runs for M5b (`fullAir D (m5bX host prev post n)`:
the M5a tables, the STATE rows producing the writes from the execution side's raw key / value bytes,
the public tape), the semantic premises of `M5b.prem` (chip contract, `CompressOK`, `NodeCR`,
`LeafCR`, `Sha256CR`, `1 ≤ D ≤ 20`), the producer premise `StSound.HostReqs` (the execution side's
`SREQ`/`HB` sends are the request list `reqs`, memory a function of `(ts, pos)`, requests in
`(seg, ts)` order) — no continued-key premise left (M5a-8, `SnFinal6`: `SnFreshLong`,
`SnContRest`, `hlongS`, `hlongM` from `Holds` + `Sha256CR`): the spec's own overlay of the requests (`StSound.committedOf T reqs`, nearcore's
`TrieUpdate` set / remove / commit), applied in key order to the pre-state trie `T` (root `prev`),
reaches `post`.

Pieces: `M5b.prem` (static premises), `StSound.final_changes_m5b` (`committed ~ cs`),
`SnFinal6.air_final_sorted_sn6` (every continued-key premise from `Holds`).
-/

namespace StateM5a.M5bFinal

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.SnSplitLoc StateM5a.RowSnAll StateM5a.RowSnAll2
open StateM5a.SnAssembly StateM5a.SnResp StateM5a.SnLimbsAll StateM5a.SnFreshLimbs StateM5a.SnStore2 StateM5a.RowBrN

open StateM5a.Tape StateM5a.FinalOrder StateM5a.VerStore StateM5a.M5b StateM5a.StSound NearSpecV3.D2 StateM5a.SnFinal5

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- **M5b end to end**: the spec's overlay of the execution's storage requests, applied to the
pre-state, reaches the claimed post-state root. -/
theorem m5b_final {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {compress : List Nat → List Nat → List Nat}
    {host : List (Nat × Bool × List Nat)} (hh : HostOK host) {prev post : Bytes} {n : Nat}
    (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    (hcomp : Sha512If.CompressOK compress)
    (hC : Sha512If.Sha512IfContract compress
      ((busList (fullAir D (m5bX host prev post n) nb np) tr pub B_IF384 true).map WsDecode.decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hNCR : Sha512If.NodeCR compress) (hLCR : WsKey.LeafCR compress)
    (hCR : Walk.Sha256CR)
    {reqs : List Req} (hR : HostReqs (fullAir D (m5bX host prev post n) nb np) tr pub host reqs)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV (committedOf T reqs)) = some (some T') ∧ rootHash (some T') = post := by
  have hP := M5b.prem hh hH hcomp hC hD1 hD hNCR hLCR hCR
  have hX := x_buses hh prev post n
  have hRb := rest_buses hh
  obtain ⟨cs, hlen, hcs, hcomm⟩ := final_changes_m5b hP hh hR T
  -- the number of writing rows is `n` (the `TCH` chain)
  have hT := tch_perm [] prev post n (m5bRest host) hH (fun T hT i hi => (rest_hr hh T hT i hi).2.2) hn hprev hpost
  have hN := (Traffic.tch_chain hT).1
  exact SnFinal6.air_final_sorted_sn6 D [] prev post n (m5bRest host) nb np hP (rest_hr hh) (rest_hrN hh) (rest_hrS hh)
    (fun T hT => ⟨no_send hRb (by decide) T hT, no_send hRb (by decide) T hT, no_send hRb (by decide) T hT,
      no_send hRb (by decide) T hT, no_send hRb (by decide) T hT⟩)
    (no_bus hRb (by decide)) (x_hxV hh prev post n) hn hprev hpost hCR cs (by rw [hlen]; omega) hcs
    (committedOf T reqs) hcomm T hT0 hF

end StateM5a.M5bFinal
