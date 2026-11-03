import WasmBase.Main.SegChain
import WasmBase.Main.SegS.SegReentry
/-!
# WasmBase.Main.SegS.SegChain — `SegChain`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegChain.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P

namespace Cuti

/-- **The per-segment named premises** (those of `seg_sound_cS`, plus the memory interface). -/
structure SegPremS (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
  H : HoldsXS nloc ngl d.pub d.tr
  hC : SegSha.ChipIfS SegSha.compressW nloc ngl d.pub d.tr d.chip
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

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **One segment** (`seg_sound_cS`, `seg_cid_outS`, MEM's out-root). -/
theorem seg_stepS {d : SegD} (hp : SegPremS X nloc ngl sg d) {s : St} (hin : InS X sg d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutS X sg d s' := by
  have hP := P_val
  obtain ⟨h0, hw, hinit, hroot⟩ := hin
  obtain ⟨H, hC, hl, hcode, hfunc, hbL, hg, hkeep, hhold, hrely, hst0, hlen, htin, hfeeN, memIn, memOut⟩ := hp
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom⟩ :=
    seg_sound_cS X H hC hl hcode hfunc hbL hg hkeep hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw
  -- `TombDead`, as inside `seg_sound_cS` (CORE)
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_ofS H hts (by omega) hbL
  have hT := seg_tombDeadS X H hcode hfunc hb hg hkeep hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin hfeeN
    hstepgas hg64 hinit h0.1
  have hcid := seg_cid_outS H (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  rcases memOut s sN h0 hmb hroot h1 h3 with hro | hc
  case inr => exact Or.inl hc
  exact Or.inr ⟨sN, h1, h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩

/-- **One link** (`cuti_viewS`, `seg_reentryS`, `initS_nodupS`, MEM's `MembIn`). -/
theorem link_stepS {d d' : SegD} (hp' : SegPremS X nloc ngl sg d') (hL : LinkPub d.pub d'.pub) {s : St}
    (ho : OutS X sg d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InS X sg d' s := by
  obtain ⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩ := ho
  have hctx : PubDigIs d'.pub pubCtxIn (cutDigest (cutView X.toCtx s)) := ⟨dd, h6, hW, by rw [hL.ctx]; exact hpub, hsha⟩
  rcases cuti_viewS hp'.H hp'.hC hwf hctx with hc | hcuti
  · exact Or.inl hc
  have hroot : MemRootIn d'.pub s := by
    obtain ⟨e, h6', hW', hp'', hs'⟩ := hro
    exact ⟨e, h6', hW', by rw [hL.mem]; exact hp'', hs'⟩
  rcases hp'.memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  have ht : (d'.pub.getD pubTIn 0).toNat = d.tOut := by rw [hL.t]; rfl
  have hS : (d'.pub.getD pubSIn 0).toNat = d.SOut := by rw [hL.S]; rfl
  have hm := segM0_link (tr := d.tr) (tr' := d'.tr) hL.pc hL.t hL.S hL.sb (by rw [hL.cid]; exact hcid)
  have hB' := seg_reentryS (M2Ctx.toCtx_fns_nodup X) hB hp'.H hcuti hmb ht hS hm
  exact Or.inr ⟨hB', hw, initS_nodupS hp'.H hw hwf hcuti, hroot⟩

include hstepgas hg64 in
/-- **The chained-segments theorem.**  Cut segments `d0 :: ds` of `wasmBaseSegAir`, each with the named
premises `SegPremS`, consecutive ones linked by their public values (`LinkPub`), and a state `s0` in the
first segment's in-relation: either SHA-384 collides, or `foldSegments` over the segments' lengths runs
from `s0` to a state `sN` in the last segment's out-relation (`BndC` at its out-cut, the public
`ctx_out` the digest of `cutView X sN`, `cid_out` the depth, `MemRootOut`, …). -/
theorem seg_chainS (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremS X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPremS X nloc ngl sg) (InS X sg) (OutS X sg)
    (fun d d' => LinkPub d.pub d'.pub)
    (fun _ hp _ hin => seg_stepS X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_stepS X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **The chained-segments theorem on lane E's call machine** (as `cuts_csteps`). -/
theorem seg_chain_cstepsS (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremS X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chainS X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

end

end Cuti

end WasmBase
