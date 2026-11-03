import WasmBase.Main.SegReentry
import WasmBase.Main.SegSoundC

/-!
# WasmBase.Main.SegChain — the chained-segments theorem (E2E M4c, CUTI item 5)

A Wasm call proved as a list of cut segments, consecutive segments linked only through their public
values, runs on the spec as one composed run — unless SHA-384 collides.

* **`chain_abs`** (generic): for any segment type `α` with a length, an in-relation `In`, an
  out-relation `Out`, a link `Lk` between consecutive segments and a "bad event" `Bad`: if every
  segment takes `In` to `Out` (or `Bad`) and every link takes `Out a` to `In b` (or `Bad`), the list of
  segments runs as `foldSegments` from `In` of the first to `Out` of the last (or `Bad`).
  `chain_abs_csteps`: the same as a run of lane E's call machine (`csteps_foldSegments`).
* **Instantiation** with today's segment theorem `seg_sound_c` (sub-lane CORE: `TombDead` discharged,
  `RegWF sN`, `InDom`), the re-entry of `Main/SegReentry.lean` and the CUTI decoding of
  `Main/SegCuti.lean`:
  - `InS d s` — the in-relation of segment `d` (`seg_sound_c`'s `h0`, `RegWF s`, `(initS).Nodup`,
    `MemRootIn`);
  - `OutS d s` — `seg_sound_c`'s out-boundary (`BndC`, `RegWF`, `ctx_out = cutDigest (cutView X s)`,
    view `MsgWF`, `MemGeom → InDom`) plus `cid_out` = depth (`seg_cid_out`) and `MemRootOut`;
  - `LinkPub pub pub'` — the public link: out `pc, t, S, sb, cid`, gas segment, `ctx`, memory root of
    one segment = in of the next;
  - `seg_step` (segment: `seg_sound_c` + `seg_cid_out` + MEM's out-root premise), `link_step`
    (link: `cuti_view`, `seg_reentry`, `initS_nodup`, MEM's `MembIn` premise).
* **`seg_chain`** / **`seg_chain_csteps`**: `Sha384Coll` or the composed run
  `CSteps q (.ent p k (.cont s0) n) (.ent p k (.cont sN) (n − Σ len))` with `OutS` of the last segment
  at `sN`.

## Named premises (per segment, `SegPrem`; plus `hstepgas`, `hg64` globally)

`ChipIf` + `CutoHiLimbs` (SHA-512 chip contract), `CodeOK`/`FuncOK` (commitments), `HostBLinkedL`,
`RegCLinked`, `SegKeepM2`, `HoldRowS`, `HostRely` (host-chip contract, M6), the cut flag and size
bounds, and the **memory interface** in sub-lane MEM's predicates: `memIn` (`MemRootIn pub s →
MembIn tr pub s ∨ Sha384Coll`) and `memOut` (the out-root of a run from a state with the in-root is
`MemRootOut`, or `Sha384Coll`).  The first segment's in-relation `InS d0 s0` is a premise (for a call's
first segment it is the entry relation, not discussed here).  `TombDead` is gone (CORE's
`seg_tombDead`).  The gas segment function `sg` is global (indexed by time); every segment's
`HoldRowS`/`SegKeepM2` constrain it, the gas publics are linked (`LinkPub.sseg`, `LinkPub.gb`) but
the relation needs nothing from them.
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-! ## 1. The generic chain -/

/-- Consecutive elements of a list are linked by `Lk`. -/
def LinkL {α : Type} (Lk : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => Lk a b ∧ LinkL Lk (b :: l)

/-- **The generic chain lemma.** -/
theorem chain_abs {α : Type} (cfg : NearCfg) (p : Prepared) {Bad : Prop} (len : α → Nat)
    (Ok : α → Prop) (In Out : α → St → Prop) (Lk : α → α → Prop)
    (hseg : ∀ a, Ok a → ∀ s, In a s → Bad ∨ ∃ s', NearSpecV3.Wasm.seg cfg p (len a) s = .cont s' ∧ Out a s')
    (hlink : ∀ a b, Ok a → Ok b → Lk a b → ∀ s, Out a s → Bad ∨ In b s) :
    ∀ (l : List α) (a : α), (∀ x ∈ a :: l, Ok x) → LinkL Lk (a :: l) → ∀ s0, In a s0 →
      Bad ∨ ∃ sN, foldSegments cfg p ((a :: l).map len) s0 = .cont sN ∧
        Out ((a :: l).getLast (List.cons_ne_nil _ _)) sN
  | [], a, hok, _, s0, h0 => by
    rcases hseg a (hok a List.mem_cons_self) s0 h0 with hb | ⟨s1, h1, ho⟩
    · exact Or.inl hb
    · refine Or.inr ⟨s1, ?_, ho⟩
      simp only [List.map_cons, List.map_nil, foldSegments, h1, Res.cont_bind]
  | b :: l, a, hok, hL, s0, h0 => by
    rcases hseg a (hok a List.mem_cons_self) s0 h0 with hb | ⟨s1, h1, ho⟩
    · exact Or.inl hb
    rcases hlink a b (hok a List.mem_cons_self) (hok b (List.mem_cons_of_mem _ List.mem_cons_self)) hL.1 s1 ho
      with hb | hi
    · exact Or.inl hb
    rcases chain_abs cfg p len Ok In Out Lk hseg hlink l b (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hL.2 s1 hi
      with hb | ⟨sN, hN, hoN⟩
    · exact Or.inl hb
    refine Or.inr ⟨sN, ?_, by rwa [List.getLast_cons (List.cons_ne_nil _ _)]⟩
    rw [List.map_cons, foldSegments, h1, Res.cont_bind]
    exact hN

open NearSpecV3.Wasm.CallCut in
/-- **The generic chain on the call machine.** -/
theorem chain_abs_csteps {α : Type} (q : CallArgs) (p : Prepared) (k : EntK) {Bad : Prop} (len : α → Nat)
    (Ok : α → Prop) (In Out : α → St → Prop) (Lk : α → α → Prop)
    (hseg : ∀ a, Ok a → ∀ s, In a s → Bad ∨ ∃ s', NearSpecV3.Wasm.seg q.cfg p (len a) s = .cont s' ∧ Out a s')
    (hlink : ∀ a b, Ok a → Ok b → Lk a b → ∀ s, Out a s → Bad ∨ In b s)
    (l : List α) (a : α) (hok : ∀ x ∈ a :: l, Ok x) (hL : LinkL Lk (a :: l)) (s0 : St) (h0 : In a s0)
    (n : Nat) (hn : ((a :: l).map len).sum ≤ n) :
    Bad ∨ ∃ sN, CSteps q (.ent p k (.cont s0) n) (.ent p k (.cont sN) (n - ((a :: l).map len).sum)) ∧
      Out ((a :: l).getLast (List.cons_ne_nil _ _)) sN := by
  rcases chain_abs q.cfg p len Ok In Out Lk hseg hlink l a hok hL s0 h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · exact Or.inr ⟨sN, csteps_foldSegments q p k _ s0 sN n h1 hn, h2⟩

/-! ## 2. Segments of `wasmBaseSegAir` -/

/-- One segment: its trace, public values and the chip's bus-103 traffic. -/
structure SegD where
  tr : Trace
  pub : List F
  chip : List StateM5a.Sha512If.IfMsg

/-- The segment's length (action rows = spec steps). -/
def SegD.n (d : SegD) : Nat := (actListM2 d.tr d.pub).length
def SegD.tIn (d : SegD) : Nat := (d.pub.getD pubTIn 0).toNat
def SegD.SIn (d : SegD) : Nat := (d.pub.getD pubSIn 0).toNat
def SegD.tOut (d : SegD) : Nat := (d.pub.getD pubTOut 0).toNat
def SegD.SOut (d : SegD) : Nat := (d.pub.getD pubSOut 0).toNat

/-- **The per-segment named premises** (those of `seg_sound_c`, plus the memory interface). -/
structure SegPrem (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (d : SegD) : Prop where
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
  /-- MEM: the in-root binds MEMB's in-side bytes. -/
  memIn : ∀ s, MemRootIn d.pub s → MembIn d.tr d.pub s ∨ NearSpecV3.E2E.Bnd.Sha384Coll
  /-- MEM: a run from a state with the in-root (and its MEMB bytes) ends at a state with the out-root. -/
  memOut : ∀ s0 sN, BndC X.toCtx sg s0 d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) →
    MembIn d.tr d.pub s0 → MemRootIn d.pub s0 → NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s0 = .cont sN →
    BndC X.toCtx sg sN d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) →
    MemRootOut d.pub sN ∨ NearSpecV3.E2E.Bnd.Sha384Coll

/-- The in-relation of a segment. -/
def InS (X : M2Ctx) (sg : Nat → Nat × Nat) (d : SegD) (s : St) : Prop :=
  BndC X.toCtx sg s d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) ∧ RegWF s ∧ (initS d.tr d.pub).Nodup ∧
    MemRootIn d.pub s

/-- The out-relation of a segment. -/
def OutS (X : M2Ctx) (sg : Nat → Nat × Nat) (d : SegD) (s : St) : Prop :=
  BndC X.toCtx sg s d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) ∧ RegWF s ∧
    PubDigIs d.pub pubCtxOut (cutDigest (cutView X.toCtx s)) ∧ (∀ y ∈ cutView X.toCtx s, MsgWF y) ∧
    d.pub.getD pubCidOut 0 = ((s.frames.length - 1 : Nat) : F) ∧ MemRootOut d.pub s ∧
    (MemGeom d.pub s → WasmView.InDom X.toCtx s)

/-- **The public link** between consecutive segments: out of `pub` = in of `pub'`. -/
structure LinkPub (pub pub' : List F) : Prop where
  pc : pub'.getD pubPcIn 0 = pub.getD pubPcOut 0
  t : pub'.getD pubTIn 0 = pub.getD pubTOut 0
  S : pub'.getD pubSIn 0 = pub.getD pubSOut 0
  sb : pub'.getD pubSbIn 0 = pub.getD pubSbOut 0
  cid : pub'.getD pubCidIn 0 = pub.getD pubCidOut 0
  sseg : pub'.getD pubSsegIn 0 = pub.getD pubSsegOut 0
  gb : ∀ i, i < 4 → pub'.getD (pubGbIn + i) 0 = pub.getD (pubGbOut + i) 0
  ctx : pubDig pub' pubCtxIn = pubDig pub pubCtxOut
  mem : pubDig pub' pubMemIn = pubDig pub pubMemOut

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **One segment** (`seg_sound_c`, `seg_cid_out`, MEM's out-root). -/
theorem seg_step {d : SegD} (hp : SegPrem X nloc ngl sg d) {s : St} (hin : InS X sg d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutS X sg d s' := by
  have hP := P_val
  obtain ⟨h0, hw, hinit, hroot⟩ := hin
  obtain ⟨H, hC, hl, hcode, hfunc, hbL, hg, hkeep, hhold, hrely, hst0, hlen, htin, hfeeN, memIn, memOut⟩ := hp
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom⟩ :=
    seg_sound_c X H hC hl hcode hfunc hbL hg hkeep hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw
  -- `TombDead`, as inside `seg_sound_c` (CORE)
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_of H hts (by omega) hbL
  have hT := seg_tombDead X H hcode hfunc hb hg hkeep hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin hfeeN
    hstepgas hg64 hinit h0.1
  have hcid := seg_cid_out H (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  rcases memOut s sN h0 hmb hroot h1 h3 with hro | hc
  case inr => exact Or.inl hc
  exact Or.inr ⟨sN, h1, h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩

/-- **One link** (`cuti_view`, `seg_reentry`, `initS_nodup`, MEM's `MembIn`). -/
theorem link_step {d d' : SegD} (hp' : SegPrem X nloc ngl sg d') (hL : LinkPub d.pub d'.pub) {s : St}
    (ho : OutS X sg d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InS X sg d' s := by
  obtain ⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩ := ho
  have hctx : PubDigIs d'.pub pubCtxIn (cutDigest (cutView X.toCtx s)) := ⟨dd, h6, hW, by rw [hL.ctx]; exact hpub, hsha⟩
  rcases cuti_view hp'.H hp'.hC hwf hctx with hc | hcuti
  · exact Or.inl hc
  have hroot : MemRootIn d'.pub s := by
    obtain ⟨e, h6', hW', hp'', hs'⟩ := hro
    exact ⟨e, h6', hW', by rw [hL.mem]; exact hp'', hs'⟩
  rcases hp'.memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  have ht : (d'.pub.getD pubTIn 0).toNat = d.tOut := by rw [hL.t]; rfl
  have hS : (d'.pub.getD pubSIn 0).toNat = d.SOut := by rw [hL.S]; rfl
  have hm := segM0_link (tr := d.tr) (tr' := d'.tr) hL.pc hL.t hL.S hL.sb (by rw [hL.cid]; exact hcid)
  have hB' := seg_reentry (M2Ctx.toCtx_fns_nodup X) hB hp'.H hcuti hmb ht hS hm
  exact Or.inr ⟨hB', hw, initS_nodup hp'.H hw hwf hcuti, hroot⟩

include hstepgas hg64 in
/-- **The chained-segments theorem.**  Cut segments `d0 :: ds` of `wasmBaseSegAir`, each with the named
premises `SegPrem`, consecutive ones linked by their public values (`LinkPub`), and a state `s0` in the
first segment's in-relation: either SHA-384 collides, or `foldSegments` over the segments' lengths runs
from `s0` to a state `sN` in the last segment's out-relation (`BndC` at its out-cut, the public
`ctx_out` the digest of `cutView X sN`, `cid_out` the depth, `MemRootOut`, …). -/
theorem seg_chain (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPrem X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPrem X nloc ngl sg) (InS X sg) (OutS X sg)
    (fun d d' => LinkPub d.pub d'.pub)
    (fun _ hp _ hin => seg_step X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_step X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **The chained-segments theorem on lane E's call machine** (as `cuts_csteps`). -/
theorem seg_chain_csteps (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPrem X nloc ngl sg d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InS X sg d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutS X sg ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chain X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

end

end Cuti

#print axioms Cuti.chain_abs
#print axioms Cuti.chain_abs_csteps
#print axioms Cuti.seg_step
#print axioms Cuti.link_step
#print axioms Cuti.seg_chain
#print axioms Cuti.seg_chain_csteps

end WasmBase
