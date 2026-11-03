import WasmBase.Main.SegKey
import WasmBase.Main.SegChainMP
import WasmBase.Main.SegSoundCMP

/-!
# WasmBase.Main.SegSoundK — segment soundness and the chain without the linking premises (E2E M4c, LINK)

`seg_sound_c` / `seg_sound_any` / `seg_chain` (and their multiproof instances `…_mp`) with the named
premises `HostBLinkedL` and `RegCLinked` **discharged** by the call-key bus (`Main/SegKey.lean`:
`seg_hostBLinkedL`, `seg_regCLinked`, from `HoldsXS`, which both segment AIRs imply).

* `seg_sound_k`, `seg_sound_k_mp` — `seg_sound_c(_mp)` minus `hbL`, `hg` (conclusion: `t_out = t_in + n`
  and `SegCutOut`, i.e. `seg_sound_c`'s conclusion verbatim);
* `seg_sound_any_k`, `seg_sound_any_k_mp` — `seg_sound_any(_mp)` minus `hbL`, `hg`;
* `SegPremK` / `SegPremKMP` — `SegPrem` / `SegPremMP` without the fields `hbL`, `hg`;
  `seg_chain_k`, `seg_chain_k_mp`, `seg_chain_csteps_k`, `seg_chain_csteps_k_mp`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P

/-- **`seg_sound_c` without `HostBLinkedL`/`RegCLinked`** (the call-key bus gives both). -/
theorem seg_sound_k (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
      SegCutOut X tr pub sg s0 :=
  seg_sound_c X H hC hl hcode hfunc (seg_hostBLinkedL H.toS) (seg_regCLinked H.toS) hkeep hhold hrely hst0
    hlen htin hfeeN hstepgas hg64 hinit h0 hw0

/-- **`seg_sound_c_mp` without `HostBLinkedL`/`RegCLinked`.** -/
theorem seg_sound_k_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
      SegCutOut X tr pub sg s0 :=
  seg_sound_c_mp X H hC hl hcode hfunc (seg_hostBLinkedL H.toSMP) (seg_regCLinked H.toSMP) hkeep hhold hrely
    hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw0

/-- **`seg_sound_any` without `HostBLinkedL`/`RegCLinked`.** -/
theorem seg_sound_any_k (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    (st = 0 → SegCutOut X tr pub sg s0) ∧ (st ≠ 0 → SegHaltOut X tr pub sg s0 st) :=
  seg_sound_any X H hC hl hcode hfunc (seg_hostBLinkedL H.toS) (seg_regCLinked H.toS) hkeep hhold hrely st
    hst2 hstN hlen htin hfeeN hstepgas hg64 hinit h0 hw0

/-- **`seg_sound_any_mp` without `HostBLinkedL`/`RegCLinked`.** -/
theorem seg_sound_any_k_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    (st = 0 → SegCutOut X tr pub sg s0) ∧ (st ≠ 0 → SegHaltOut X tr pub sg s0 st) :=
  seg_sound_any_mp X H hC hl hcode hfunc (seg_hostBLinkedL H.toSMP) (seg_regCLinked H.toSMP) hkeep hhold hrely
    st hst2 hstN hlen htin hfeeN hstepgas hg64 hinit h0 hw0

#print axioms seg_sound_k
#print axioms seg_sound_k_mp
#print axioms seg_sound_any_k
#print axioms seg_sound_any_k_mp

namespace Cuti

/-- **The per-segment named premises without the linking premises** (`SegPrem` minus `hbL`, `hg`). -/
structure SegPremK (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAir nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hkeep : SegKeepM2 d.tr d.pub sg
  hhold : HoldRowS X.toCtx d.tr d.pub sg
  hrely : HostRely X.toCtx d.tr d.pub
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  memIn : ∀ s, MemRootIn d.pub s → MembIn d.tr d.pub s ∨ NearSpecV3.E2E.Bnd.Sha384Coll
  memOut : ∀ s0 sN, BndC X.toCtx sg s0 d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) →
    MembIn d.tr d.pub s0 → MemRootIn d.pub s0 → NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s0 = .cont sN →
    BndC X.toCtx sg sN d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) →
    MemRootOut d.pub sN ∨ NearSpecV3.E2E.Bnd.Sha384Coll

/-- **The multiproof AIR's per-segment premises without the linking premises.** -/
structure SegPremKMP (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAirMP nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hkeep : SegKeepM2 d.tr d.pub sg
  hhold : HoldRowS X.toCtx d.tr d.pub sg
  hrely : HostRely X.toCtx d.tr d.pub
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  memIn : ∀ s, MemRootIn d.pub s → MembIn d.tr d.pub s ∨ NearSpecV3.E2E.Bnd.Sha384Coll
  memOut : ∀ s0 sN, BndC X.toCtx sg s0 d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) →
    MembIn d.tr d.pub s0 → MemRootIn d.pub s0 → NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s0 = .cont sN →
    BndC X.toCtx sg sN d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) →
    MemRootOut d.pub sN ∨ NearSpecV3.E2E.Bnd.Sha384Coll

theorem SegPremK.toPrem {X : M2Ctx} {nloc ngl : Nat} {sg : Nat → Nat × Nat} {d : SegD}
    (h : SegPremK X nloc ngl sg d) : SegPrem X nloc ngl sg d :=
  ⟨h.H, h.hC, h.hl, h.hcode, h.hfunc, seg_hostBLinkedL h.H.toS, seg_regCLinked h.H.toS, h.hkeep, h.hhold,
    h.hrely, h.hst0, h.hlen, h.htin, h.hfeeN, h.memIn, h.memOut⟩

theorem SegPremKMP.toPrem {X : M2Ctx} {nloc ngl : Nat} {sg : Nat → Nat × Nat} {d : SegD}
    (h : SegPremKMP X nloc ngl sg d) : SegPremMP X nloc ngl sg d :=
  ⟨h.H, h.hC, h.hl, h.hcode, h.hfunc, seg_hostBLinkedL h.H.toSMP, seg_regCLinked h.H.toSMP, h.hkeep, h.hhold,
    h.hrely, h.hst0, h.hlen, h.htin, h.hfeeN, h.memIn, h.memOut⟩

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **`seg_chain` without the linking premises.** -/
theorem seg_chain_k (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremK X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chain X hstepgas hg64 d0 ds (fun d hd => (hok d hd).toPrem) hL h0

include hstepgas hg64 in
/-- **`seg_chain_mp` without the linking premises.** -/
theorem seg_chain_k_mp (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremKMP X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chain_mp X hstepgas hg64 d0 ds (fun d hd => (hok d hd).toPrem) hL h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **`seg_chain_csteps` without the linking premises.** -/
theorem seg_chain_csteps_k (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremK X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chain_csteps X hstepgas hg64 q hq k d0 ds (fun d hd => (hok d hd).toPrem) hL h0 n hn

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **`seg_chain_csteps_mp` without the linking premises.** -/
theorem seg_chain_csteps_k_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremKMP X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  seg_chain_csteps_mp X hstepgas hg64 q hq k d0 ds (fun d hd => (hok d hd).toPrem) hL h0 n hn

end

end Cuti

#print axioms Cuti.seg_chain_k
#print axioms Cuti.seg_chain_k_mp
#print axioms Cuti.seg_chain_csteps_k
#print axioms Cuti.seg_chain_csteps_k_mp

end WasmBase
