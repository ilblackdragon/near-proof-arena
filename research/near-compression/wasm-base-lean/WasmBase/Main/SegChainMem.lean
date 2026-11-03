import WasmBase.Main.SegChain
import WasmBase.Main.SegMemRoot

/-!
# WasmBase.Main.SegChainMem — the chained-segments theorem with the memory interface discharged (E2E M4c, MEM)

`Main/SegChain.lean`'s `seg_chain` takes the memory interface as per-segment premises (`SegPrem.memIn`,
`SegPrem.memOut`).  Here they are theorems (sub-lane MEM, `Main/SegMemRoot.lean`):

* `memIn` is `MemRoot.seg_membIn` (needs `MemGeom pub s`: the public depth / `nblk` are the state's);
* `memOut` is `MemRoot.seg_mem_sound` (needs, besides `MemGeom`, `HostPagesRely` — M6 — and that CUTI
  produces no memory message, `CutiNoMem`, which follows from `cuti_view` once the public `ctx_in` is
  the digest of the in-state's view).

The relations thread the geometry: `InSM = InS ∧ MemGeom ∧ (ctx_in = cutDigest (cutView X s), view
MsgWF)`, `OutSM = OutS ∧ MemGeom`, and the public link `LinkPubM = LinkPub ∧` equal depth / `nblk`
publics (segments contain no `memory.grow`).

* `seg_stepM`, `link_stepM`, **`seg_chain_mem`**, **`seg_chain_mem_csteps`**: `seg_chain` /
  `seg_chain_csteps` with per-segment premises `SegPremM` (= `SegPrem` without `memIn`/`memOut`, plus
  `HostPagesRely`).  Memory-related premises left: `HostPagesRely` (per segment, M6) and, for the
  first segment only, `MemRootIn`, `MemGeom` (in `InS`/`InSM`) and the first `ctx_in`.
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- **The per-segment named premises without the memory interface** (`SegPrem` minus `memIn`/`memOut`,
plus `HostPagesRely`). -/
structure SegPremM (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAir nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) d.pub d.tr d.chip
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
  /-- MEM (M6): a HOST row's step keeps the page count. -/
  hpr : HostPagesRely X.toCtx d.tr d.pub

/-- The in-relation with the memory geometry and the in-context digest of the state's view. -/
def InSM (X : M2Ctx) (sg : Nat → Nat × Nat) (d : SegD) (s : St) : Prop :=
  InS X sg d s ∧ MemGeom d.pub s ∧ PubDigIs d.pub pubCtxIn (cutDigest (cutView X.toCtx s)) ∧
    ∀ y ∈ cutView X.toCtx s, MsgWF y

/-- The out-relation with the memory geometry. -/
def OutSM (X : M2Ctx) (sg : Nat → Nat × Nat) (d : SegD) (s : St) : Prop :=
  OutS X sg d s ∧ MemGeom d.pub s

/-- The public link, with the memory geometry publics equal. -/
structure LinkPubM (pub pub' : List F) : Prop where
  link : LinkPub pub pub'
  depth : pub'.getD pubDepth 0 = pub.getD pubDepth 0
  nblk : pub'.getD pubNblk 0 = pub.getD pubNblk 0

/-- CUTI's productions are a view's: no memory message. -/
theorem cutiNoMem_of_view {X : Ctx} {s : St} {tr : Trace} {pub : List F}
    (h : (part Cut.In.table tr pub 30 busStk true).map decMsg =
      (cutView X s).map (fun y => ofFields y (pub.getD pubTIn 0).toNat)) : MemRoot.CutiNoMem tr pub := by
  intro x hx
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨m, hm, rfl⟩ := mem_cutView.mp hy
  rw [ofFields_fieldsOf]
  show m.space ≠ 3
  rcases cutMsgs_space hm with h | h | h | h | ⟨h, -⟩ | h <;> omega

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **One segment**, memory interface discharged. -/
theorem seg_stepM {d : SegD} (hp : SegPremM X nloc ngl sg d) {s : St} (hin : InSM X sg d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutSM X sg d s' := by
  have hP := P_val
  obtain ⟨⟨h0, hw, hinit, hroot⟩, hG, hctx, hvwf⟩ := hin
  obtain ⟨H, hC, hl, hcode, hfunc, hbL, hg, hkeep, hhold, hrely, hst0, hlen, htin, hfeeN, hpr⟩ := hp
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom⟩ :=
    seg_sound_c X H hC hl hcode hfunc hbL hg hkeep hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_of H hts (by omega) hbL
  have hT := seg_tombDead X H hcode hfunc hb hg hkeep hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin hfeeN
    hstepgas hg64 hinit h0.1
  have hcid := seg_cid_out H (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases cuti_view H hC hvwf hctx with hc | hcuti
  · exact Or.inl hc
  have hcu := cutiNoMem_of_view hcuti
  obtain ⟨-, hout⟩ := MemRoot.seg_mem_sound X H hC hcode hfunc hb hg hkeep hhold hpr hcu hst0 hlen htin hfeeN
    hstepgas hg64 hinit hG hroot h0.1
  rcases hout sN h1 h3.1 with ⟨hro, hGN⟩ | hc
  · exact Or.inr ⟨sN, h1, ⟨h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩, hGN⟩
  · exact Or.inl hc

/-- **One link**, memory interface discharged. -/
theorem link_stepM {d d' : SegD} (hp' : SegPremM X nloc ngl sg d') (hL : LinkPubM d.pub d'.pub) {s : St}
    (ho : OutSM X sg d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSM X sg d' s := by
  obtain ⟨⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩, hG⟩ := ho
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
  exact Or.inr ⟨⟨hB', hw, initS_nodup hp'.H hw hwf hcuti, hroot⟩, hG', hctx, hwf⟩

include hstepgas hg64 in
/-- **The chained-segments theorem, memory interface discharged.**  Cut segments `d0 :: ds` of
`wasmBaseSegAir` with the premises `SegPremM`, linked by `LinkPubM`, and `s0` in the first segment's
`InSM`: SHA-384 collides, or `foldSegments` runs from `s0` to `sN` in the last segment's `OutSM`
(in particular `MemRootOut` and `MemGeom` at `sN`). -/
theorem seg_chain_mem (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremM X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSM X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutSM X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPremM X nloc ngl sg) (InSM X sg) (OutSM X sg)
    (fun d d' => LinkPubM d.pub d'.pub)
    (fun _ hp _ hin => seg_stepM X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_stepM X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **`seg_chain_mem` on lane E's call machine.** -/
theorem seg_chain_mem_csteps (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremM X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSM X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutSM X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chain_mem X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

end

end Cuti

#print axioms Cuti.seg_stepM
#print axioms Cuti.link_stepM
#print axioms Cuti.seg_chain_mem
#print axioms Cuti.seg_chain_mem_csteps

end WasmBase
