import WasmBase.Main.SegSoundAll

/-!
# WasmBase.Main.SegChainAll — one chained-segments theorem: σ-pinned host premises, key bus, memory root (E2E M6)

Merges the three chain theorems
* `Cuti.seg_chain_σ` (`Main/SegChainSigma.lean`: σ-pinned host premises; `HostBLinkedL`, `RegCLinked`,
  `memIn`, `memOut` named; base AIR),
* `Cuti.seg_chain_k(_mp)` (`Main/SegSoundK.lean`: `HostBLinkedL`/`RegCLinked` discharged by the key
  bus 214; host premises unrestricted, hence vacuous on host traces),
* `Cuti.seg_chain_mem(_mp)` (`Main/SegChainMem(MP).lean`: memory interface discharged; host premises
  unrestricted)

into **one** statement per AIR, with the single-segment pieces of `Main/SegSoundAll.lean`
(`seg_sound_cσS`, `seg_tombDeadσS`, `seg_mem_soundσ(_mp)`):

* **`Cuti.seg_chain_all_mp`** / **`Cuti.seg_chain_all_csteps_mp`** — the default multiproof AIR
  `wasmBaseSegAirMP`, per-segment premises **`SegPremAMP`**;
* `Cuti.seg_chain_all` / `Cuti.seg_chain_all_csteps` — the base AIR `wasmBaseSegAir`, `SegPremA`.

Relations: **`InSA = InSM ∧ sideR s = σ (t_in + 1)`** (`InSM`: `BndC` at the in-boundary, `RegWF`,
`initS` nodup, `MemRootIn`, `MemGeom`, `ctx_in` = digest of `cutView s` with `MsgWF` views),
**`OutSA = OutSM ∧ sideR s = σ (t_out + 1)`** (`OutSM`: `BndC` at the out-boundary, `RegWF`, `ctx_out`
= digest of `cutView s`, `MsgWF`, `cid_out` = depth, `MemRootOut`, `InDom` under `MemGeom`,
`MemGeom`); links **`LinkPubM`** (`LinkPub` + equal depth/`nblk` publics).

Per-segment named premises left (`SegPremAMP`): the σ-pinned host contract `HoldRowSσ`, `HostRelyσ`,
`SigKeep` (M6.2; one global thread `σ`), `HostPagesRely` (host calls keep the page count), the
commitment bindings `CodeOK`/`FuncOK`, the gas thread `SegKeepM2`, `CutoHiLimbs`, the SHA chip
interface `ChipIf`, `Dn pub ≤ 30` (MP only) and the size bounds.  **No** `HostBLinkedL`, `RegCLinked`
(key bus), `memIn`, `memOut` (MEM).
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- **The per-segment premises of the merged chain, multiproof AIR.**  `SegPremMMP` with the
σ-pinned host premises (`HoldRowSσ`, `HostRelyσ`, `SigKeep` for the global thread `σ`) and without
the linking premises (key bus 214). -/
structure SegPremAMP (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) :
    Prop where
  H : HoldsX (wasmBaseSegAirMP nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hkeep : SegKeepM2 d.tr d.pub sg
  hsk : SigKeep d.tr d.pub σ
  hhold : HoldRowSσ X.toCtx d.tr d.pub sg σ
  hrely : HostRelyσ X.toCtx d.tr d.pub σ
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  /-- MEM (M6): a HOST row's step keeps the page count. -/
  hpr : HostPagesRely X.toCtx d.tr d.pub
  /-- MEM: the public depth fits the multiproof's position arithmetic (the verifier fixes `D = 16`). -/
  hD30 : Dn d.pub ≤ 30

/-- **The per-segment premises of the merged chain, base AIR** (`SegPremAMP` without `hD30`). -/
structure SegPremA (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) :
    Prop where
  H : HoldsX (wasmBaseSegAir nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hkeep : SegKeepM2 d.tr d.pub sg
  hsk : SigKeep d.tr d.pub σ
  hhold : HoldRowSσ X.toCtx d.tr d.pub sg σ
  hrely : HostRelyσ X.toCtx d.tr d.pub σ
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  hpr : HostPagesRely X.toCtx d.tr d.pub

/-- **The merged in-relation**: `InSM` (boundary relation, `RegWF`, `initS` nodup, in-root, geometry,
`ctx_in` digest of the view) and the σ pin at the in-time. -/
def InSA (X : M2Ctx) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) (s : St) : Prop :=
  InSM X sg d s ∧ sideR s = σ (d.tIn + 1)

/-- **The merged out-relation**: `OutSM` (boundary relation, `RegWF`, `ctx_out` digest of the view,
`cid_out`, out-root, `InDom`, geometry) and the σ pin at the out-time. -/
def OutSA (X : M2Ctx) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) (s : St) : Prop :=
  OutSM X sg d s ∧ sideR s = σ (d.tOut + 1)

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

/-! ### Multiproof AIR -/

include hstepgas hg64 in
/-- **One segment of the multiproof AIR, all interfaces merged.** -/
theorem seg_stepAMP {d : SegD} (hp : SegPremAMP X nloc ngl sg σ d) {s : St} (hin : InSA X sg σ d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutSA X sg σ d s' := by
  have hP := P_val
  obtain ⟨⟨⟨h0, hw, hinit, hroot⟩, hG, hctx, hvwf⟩, hσ0⟩ := hin
  obtain ⟨HM, hCM, hl, hcode, hfunc, hkeep, hsk, hhold, hrely, hst0, hlen, htin, hfeeN, hpr, hD30⟩ := hp
  have H := HM.toSMP
  have hC := SegSha.ChipIf.toSMP HM hCM
  have hbL : HostBLinkedL d.tr d.pub := seg_hostBLinkedL H
  have hg : RegCLinked d.tr d.pub := seg_regCLinked H
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom, hσN⟩ :=
    seg_sound_cσS X H hC hl hcode hfunc hbL hg hkeep hsk hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit
      h0 hw hσ0
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_ofS H hts (by omega) hbL
  have hT := seg_tombDeadσS X H hcode hfunc hb hg hkeep hsk hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin
    hfeeN hstepgas hg64 hinit h0.1 hσ0
  have hcid := seg_cid_outS H (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases cuti_viewS H hC hvwf hctx with hc | hcuti
  · exact Or.inl hc
  have hcu := cutiNoMem_of_view hcuti
  obtain ⟨-, hout⟩ := seg_mem_soundσ_mp X HM hCM hD30 hcode hfunc hb hg hkeep hsk hhold hpr hcu hst0 hlen
    htin hfeeN hstepgas hg64 hinit hG hroot h0.1 hσ0
  rcases hout sN h1 h3.1 with ⟨hro, hGN⟩ | hc
  · exact Or.inr ⟨sN, h1, ⟨⟨h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩, hGN⟩, hσN⟩
  · exact Or.inl hc

/-- **One link of the multiproof AIR, all interfaces merged** (`link_stepMMP`; the pin moves along
`LinkPub.t`). -/
theorem link_stepAMP {d d' : SegD} (hp' : SegPremAMP X nloc ngl sg σ d') (hL : LinkPubM d.pub d'.pub)
    {s : St} (ho : OutSA X sg σ d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSA X sg σ d' s := by
  obtain ⟨⟨⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩, hG⟩, hσ⟩ := ho
  have H' := hp'.H.toSMP
  have hC' := SegSha.ChipIf.toSMP hp'.H hp'.hC
  have hctx : PubDigIs d'.pub pubCtxIn (cutDigest (cutView X.toCtx s)) :=
    ⟨dd, h6, hW, by rw [hL.link.ctx]; exact hpub, hsha⟩
  rcases cuti_viewS H' hC' hwf hctx with hc | hcuti
  · exact Or.inl hc
  have hroot : MemRootIn d'.pub s := by
    obtain ⟨e, h6', hW', hp'', hs'⟩ := hro
    exact ⟨e, h6', hW', by rw [hL.link.mem]; exact hp'', hs'⟩
  have hG' : MemGeom d'.pub s := ⟨by rw [hL.depth]; exact hG.1, by rw [hL.nblk]; exact hG.2⟩
  rcases MemRoot.seg_membIn_mp hp'.H hp'.hC hp'.hD30 hG' hroot with hmb | hc
  case inr => exact Or.inl hc
  have ht : (d'.pub.getD pubTIn 0).toNat = d.tOut := by rw [hL.link.t]; rfl
  have hS : (d'.pub.getD pubSIn 0).toNat = d.SOut := by rw [hL.link.S]; rfl
  have hm := segM0_link (tr := d.tr) (tr' := d'.tr) hL.link.pc hL.link.t hL.link.S hL.link.sb
    (by rw [hL.link.cid]; exact hcid)
  have hB' := seg_reentryS (M2Ctx.toCtx_fns_nodup X) hB H' hcuti hmb ht hS hm
  refine Or.inr ⟨⟨⟨hB', hw, initS_nodupS H' hw hwf hcuti, hroot⟩, hG', hctx, hwf⟩, ?_⟩
  show sideR s = σ ((d'.pub.getD pubTIn 0).toNat + 1)
  rw [ht]; exact hσ

include hstepgas hg64 in
/-- **The merged chained-segments theorem, multiproof AIR.**  Cut segments `d0 :: ds` of
`wasmBaseSegAirMP`, each with `SegPremAMP` for one global σ-thread, consecutive ones linked by
`LinkPubM`, and `s0` in the first segment's `InSA`: either SHA-384 collides, or `foldSegments` runs
from `s0` to `sN` with `OutSA` of the last segment (σ pin, memory root and geometry, `RegWF`, `BndC`,
`ctx_out` digest, `cid_out`, `InDom`). -/
theorem seg_chain_all_mp (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremAMP X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSA X sg σ d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutSA X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPremAMP X nloc ngl sg σ) (InSA X sg σ) (OutSA X sg σ)
    (fun d d' => LinkPubM d.pub d'.pub)
    (fun _ hp _ hin => seg_stepAMP X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_stepAMP X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **`seg_chain_all_mp` on lane E's call machine.** -/
theorem seg_chain_all_csteps_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremAMP X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSA X sg σ d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n)
          (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutSA X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chain_all_mp X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

/-! ### Base AIR -/

include hstepgas hg64 in
/-- **One segment of the base AIR, all interfaces merged.** -/
theorem seg_stepA {d : SegD} (hp : SegPremA X nloc ngl sg σ d) {s : St} (hin : InSA X sg σ d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutSA X sg σ d s' := by
  have hP := P_val
  obtain ⟨⟨⟨h0, hw, hinit, hroot⟩, hG, hctx, hvwf⟩, hσ0⟩ := hin
  obtain ⟨HB, hCB, hl, hcode, hfunc, hkeep, hsk, hhold, hrely, hst0, hlen, htin, hfeeN, hpr⟩ := hp
  have H := HB.toS
  have hC := SegSha.ChipIf.toS HB hCB
  have hbL : HostBLinkedL d.tr d.pub := seg_hostBLinkedL H
  have hg : RegCLinked d.tr d.pub := seg_regCLinked H
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom, hσN⟩ :=
    seg_sound_cσS X H hC hl hcode hfunc hbL hg hkeep hsk hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit
      h0 hw hσ0
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_ofS H hts (by omega) hbL
  have hT := seg_tombDeadσS X H hcode hfunc hb hg hkeep hsk hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin
    hfeeN hstepgas hg64 hinit h0.1 hσ0
  have hcid := seg_cid_out HB (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases cuti_view HB hCB hvwf hctx with hc | hcuti
  · exact Or.inl hc
  have hcu := cutiNoMem_of_view hcuti
  obtain ⟨-, hout⟩ := seg_mem_soundσ X HB hCB hcode hfunc hb hg hkeep hsk hhold hpr hcu hst0 hlen
    htin hfeeN hstepgas hg64 hinit hG hroot h0.1 hσ0
  rcases hout sN h1 h3.1 with ⟨hro, hGN⟩ | hc
  · exact Or.inr ⟨sN, h1, ⟨⟨h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩, hGN⟩, hσN⟩
  · exact Or.inl hc

/-- **One link of the base AIR, all interfaces merged.** -/
theorem link_stepA {d d' : SegD} (hp' : SegPremA X nloc ngl sg σ d') (hL : LinkPubM d.pub d'.pub)
    {s : St} (ho : OutSA X sg σ d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSA X sg σ d' s := by
  obtain ⟨⟨⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩, hG⟩, hσ⟩ := ho
  have hctx : PubDigIs d'.pub pubCtxIn (cutDigest (cutView X.toCtx s)) :=
    ⟨dd, h6, hW, by rw [hL.link.ctx]; exact hpub, hsha⟩
  rcases cuti_view hp'.H hp'.hC hwf hctx with hc | hcuti
  · exact Or.inl hc
  have hroot : MemRootIn d'.pub s := by
    obtain ⟨e, h6', hW', hp'', hs'⟩ := hro
    exact ⟨e, h6', hW', by rw [hL.link.mem]; exact hp'', hs'⟩
  have hG' : MemGeom d'.pub s := ⟨by rw [hL.depth]; exact hG.1, by rw [hL.nblk]; exact hG.2⟩
  rcases MemRoot.seg_membIn hp'.H hp'.hC hG' hroot with hmb | hc
  case inr => exact Or.inl hc
  have ht : (d'.pub.getD pubTIn 0).toNat = d.tOut := by rw [hL.link.t]; rfl
  have hS : (d'.pub.getD pubSIn 0).toNat = d.SOut := by rw [hL.link.S]; rfl
  have hm := segM0_link (tr := d.tr) (tr' := d'.tr) hL.link.pc hL.link.t hL.link.S hL.link.sb
    (by rw [hL.link.cid]; exact hcid)
  have hB' := seg_reentry (M2Ctx.toCtx_fns_nodup X) hB hp'.H hcuti hmb ht hS hm
  refine Or.inr ⟨⟨⟨hB', hw, initS_nodup hp'.H hw hwf hcuti, hroot⟩, hG', hctx, hwf⟩, ?_⟩
  show sideR s = σ ((d'.pub.getD pubTIn 0).toNat + 1)
  rw [ht]; exact hσ

include hstepgas hg64 in
/-- **The merged chained-segments theorem, base AIR** (`seg_chain_all_mp` for `wasmBaseSegAir`). -/
theorem seg_chain_all (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremA X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSA X sg σ d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutSA X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPremA X nloc ngl sg σ) (InSA X sg σ) (OutSA X sg σ)
    (fun d d' => LinkPubM d.pub d'.pub)
    (fun _ hp _ hin => seg_stepA X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_stepA X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **`seg_chain_all` on lane E's call machine.** -/
theorem seg_chain_all_csteps (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremA X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSA X sg σ d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n)
          (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutSA X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chain_all X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

end

end Cuti

#print axioms Cuti.seg_stepAMP
#print axioms Cuti.link_stepAMP
#print axioms Cuti.seg_chain_all_mp
#print axioms Cuti.seg_chain_all_csteps_mp
#print axioms Cuti.seg_stepA
#print axioms Cuti.link_stepA
#print axioms Cuti.seg_chain_all
#print axioms Cuti.seg_chain_all_csteps

end WasmBase
