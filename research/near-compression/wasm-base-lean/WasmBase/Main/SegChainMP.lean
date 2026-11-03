import WasmBase.Main.SegS.SegChain
import WasmBase.Main.SegSoundMP
/-!
# WasmBase.Main.SegChainMP — chained segments of the multiproof AIR (E2E M4c, sub-lane MP)

**`seg_chain_mp`**, **`seg_chain_csteps_mp`**: CUTI's `Cuti.seg_chain` / `Cuti.seg_chain_csteps` for
segments of `wasmBaseSegAirMP`.  The per-segment premises `SegPremMP` are `Cuti.SegPrem`'s field for
field, with `HoldsX`/`ChipIf` of the multiproof AIR; the memory interface stays the per-segment
premises `memIn`/`memOut` (`SegIface`, the MEM lane's).  Both `SegPrem` (M4 AIR) and `SegPremMP`
convert to the generic `SegPremS` (`HoldsXS`/`ChipIfS`, `Main/SegS/SegChain.lean`), whose
`seg_chainS` / `seg_chain_cstepsS` (CUTI's proofs over `HoldsXS`) give the chain.
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P

/-- **The per-segment named premises for the multiproof AIR** (`SegPrem` with `wasmBaseSegAirMP`). -/
structure SegPremMP (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAirMP nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hbL : HostBLinkedL d.tr d.pub
  hg : RegCLinked d.tr d.pub
  hkeep : SegKeepM2 d.tr d.pub sg
  hhold : HoldRowS X.toCtx d.tr d.pub sg
  hrely : HostRely X.toCtx d.tr d.pub
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  /-- MEM: the in-root binds MEMB's in-side bytes. -/
  memIn : ∀ s, MemRootIn d.pub s → MembIn d.tr d.pub s ∨ NearSpecV3.E2E.Bnd.Sha384Coll
  /-- MEM: a run from a state with the in-root (and its MEMB bytes) ends at a state with the out-root. -/
  memOut : ∀ s0 sN, BndC X.toCtx sg s0 d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) →
    MembIn d.tr d.pub s0 → MemRootIn d.pub s0 → NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s0 = .cont sN →
    BndC X.toCtx sg sN d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) →
    MemRootOut d.pub sN ∨ NearSpecV3.E2E.Bnd.Sha384Coll

theorem SegPremMP.toS {X : M2Ctx} {nloc ngl : Nat} {sg : Nat → Nat × Nat} {d : SegD}
    (h : SegPremMP X nloc ngl sg d) : SegPremS X nloc ngl sg d :=
  ⟨h.H.toSMP, SegSha.ChipIf.toSMP h.H h.hC, h.hl, h.hcode, h.hfunc, h.hbL, h.hg, h.hkeep, h.hhold, h.hrely,
    h.hst0, h.hlen, h.htin, h.hfeeN, h.memIn, h.memOut⟩

theorem SegPrem.toS {X : M2Ctx} {nloc ngl : Nat} {sg : Nat → Nat × Nat} {d : SegD}
    (h : SegPrem X nloc ngl sg d) : SegPremS X nloc ngl sg d :=
  ⟨h.H.toS, SegSha.ChipIf.toS h.H h.hC, h.hl, h.hcode, h.hfunc, h.hbL, h.hg, h.hkeep, h.hhold, h.hrely,
    h.hst0, h.hlen, h.htin, h.hfeeN, h.memIn, h.memOut⟩

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **The chained-segments theorem for the multiproof AIR** (`seg_chain` with `SegPremMP`). -/
theorem seg_chain_mp (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremMP X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chainS X hstepgas hg64 d0 ds (fun d hd => (hok d hd).toS) hL h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **The chained-segments theorem on lane E's call machine, multiproof AIR.** -/
theorem seg_chain_csteps_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremMP X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chain_cstepsS X hstepgas hg64 q hq k d0 ds (fun d hd => (hok d hd).toS) hL h0 n hn

include hstepgas hg64 in
/-- `seg_chain` (M4 AIR) through `SegPremS` — a check that `seg_chainS` generalises it. -/
theorem seg_chain_viaS (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPrem X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chainS X hstepgas hg64 d0 ds (fun d hd => (hok d hd).toS) hL h0

end

end Cuti

#print axioms Cuti.seg_chain_mp
#print axioms Cuti.seg_chain_csteps_mp
#print axioms Cuti.seg_chain_viaS

end WasmBase
