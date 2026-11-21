import WasmBase.Main.SegChainAll

/-!
# WasmBase.Main.SegCallSigma — a call's segments from entry to exit, σ-pinned (E2E M6, M6.5 shape)

The merged chain `Cuti.seg_chain_all_mp` (`Main/SegChainAll.lean`) runs cut segments from the first
segment's in-relation `InSA` to the last cut's `OutSA`.  Here the two ends of a call:

## 1. Entry: the first segment's in-relation from the call's entry state

* **`EntryPub X pub s0 k t S dc dm`** — the checks a verifier makes on the **first** segment's public
  values, given the entry state `s0` (the state of lane E's `.ent p k (.cont s0) n`, i.e. `enter p
  (resetSt s) fi = .cont s0`), the entry function's checked index `k`, the in-time `t` and in-gas
  units `S`, and the 6-word SHA-384 digests `dc` of `cutView X s0` and `dm` of `memRootOf s0`:
  `t_in = t`, `S_in = S`, `pc_in = offOf k` (instruction 0 of the entry function), `sb_in = 0`,
  `cid_in = 0`, `ctx_in` = the limbs of `dc` (and `dc`'s bytes are `cutDigest (cutView X s0)`),
  `mem_in` = the limbs of `dm` (`dm`'s bytes are `memRootOf s0`), `depth`/`nblk` = the entry memory's.
  It is a **decidable** predicate (`EntryPub.decidable`).
* **`EntrySeed X sg s0 k t S`** — the named entry relation: `s0` is related (`Bnd`) at `(t, S)`, with
  STATE message `stMsg (offOf k) (t + 1) S 0 0 0`, to **some** live set.  It is the same kind of
  premise as `wasm_base_sound_m2`'s `h0` (a `RelW` of the entry state at time 1, `Bnd.of_relW`); the
  first segment re-labels it to its own `initS` (`bndC_reentry_bnd`, the `Bnd` form of
  `bndC_reentry`).
* **`entry_inSA_mp`**: `SegPremAMP` of the first segment `d0`, `EntryPub`, `EntrySeed`,
  `s0.frames.length = 1`, `RegWF s0`, `MsgWF` of `s0`'s view and the pin `sideR s0 = σ (t + 1)`
  (σ is a ghost: put `σ (t + 1) := sideR s0`) give: SHA-384 collides, or `InSA X sg σ d0 s0`.

## 2. Exit: the halting segment, and the call's result

* **`seg_sound_haltσS` / `seg_sound_haltσ_mp`** — the σ-pinned halting segment (`seg_sound_halt`'s
  shape, through `exec_rowsJH`): from `InSA`'s boundary relation and pin, the state `s` after
  `n − 1` rows is on the thread (`sideR s = σ t_out`) and its step is terminal: `.fin sN` (no frames)
  for status 1, `.abort sN e` for status 2, with the gas equation at `(S_out, sg (t_out + 1))`; and
  the public `ctx_out` is the digest of CUTO's list.  Per-segment premises `SegPremHMP` (no
  `HostRelyσ`, `HostPagesRely`: not needed for a halting segment; key bus discharges the links).
* **`call_halt_csteps_mp`** — a halting segment on lane E's call machine: `CSteps` from
  `.ent p k (.cont s0) n` to `.ent p k r (n − n_d)` with `r = step s`, and `cden` equal at both.
* **`call_chain_halt_csteps_mp`** — cut segments `d0 :: ds` (`seg_chain_all_mp`), a `LinkPubM` link,
  then the halting segment `dl`: SHA-384 collides, or the call machine runs from `.ent p k (.cont s0) n`
  to `.ent p k r m` with `r = step s`, `sideR s = σ (t_out dl)`.
* **`callResult_of_segments_mp`** (M6.5 shape) — with lane E's `CSteps q .pre (.ent p .method (.cont s0) n)`
  (the call reaches the method's first instruction with fuel `n`) and the entry premises of §1:
  SHA-384 collides, or **`callResult q = afterMethod (entPost r)`** with `r = step s` terminal and
  `sideR s = σ (t_out dl)`: the call's result (logs, return data, promises, gas — all in the state
  that `entPost`/`sync` reads) is a function of the last pre-state `s`, which is determined by its
  Wasm-visible part, its gas register and the pinned host side `σ (t_out dl)` (`sigJ_unique`).

## What is still open (named, not proved here)

* the per-segment host contract `HoldRowSσ`, `HostRelyσ`, `SigKeep` (M6.2: the two-run `callHost`
  footprint, sub-lane FOOT2) and `HostPagesRely`;
* `EntrySeed` (the entry relation: a `RelW` of the entry state; the same premise as
  `wasm_base_sound_m2`'s `h0`), `RegWF s0`, the entry view's `MsgWF`, `s0.frames.length = 1`;
* lane E's side: that `preConf q` reaches `.ent p .method (.cont s0) n` (`tailConf` with
  `enter p (resetSt s) mi = .cont s0`), and the `start`-function entry (`EntK.start`), which needs the
  same composition twice;
* the pin is on the **last pre-state** `s` of the halting step, not on its result: for an abort the
  result's host side is `sync`'s/the host's (`RowSpecSegJ` does not pin non-continuing results).  For a
  normal finish through a non-host instruction (`return`/`end` of the entry frame) the result's
  `sideR` equals `s`'s, but the `.fin` analogue of `StepSide.step_sideG` is not proved here.
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Entry -/

/-- **Re-entry from a plain boundary relation** (`bndC_reentry` with `hB : Bnd`: its `RegC`/`SpC`
halves are not used). -/
theorem bndC_reentry_bnd {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat}
    {m : List F} {L0 : List Msg} (hB : Bnd X sg s t S m L0) {L : List Msg}
    (hV : ∀ x, x.space ≠ 3 → x.space ≠ 7 → (x ∈ L ↔ viewAt X s t x))
    {T : List Nat} (hT : T.Nodup) (hTb : ∀ a ∈ T, a < memBytes s)
    (hM : ∀ x, x.space = 3 → (x ∈ L ↔ x ∈ memView T s (fun _ => t))) :
    BndC X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F)) L := by
  obtain ⟨k, pc, sb, cid, hm, E, f, tps, tpl, rfl, rfl, rfl, R⟩ := hB
  obtain ⟨σ, A, sv, -, R', hc, -, -, -⟩ := R.relabelV
  have R'' := RelW.ofView hnd R' rfl hc (idsDepth_svR sv) (tp := t) (by omega) (L := (· ∈ L)) hV hT hTb hM
  have hfr : s.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  have hb : Bnd X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F)) L := by
    refine ⟨E.k, pc, E.sb, E.rest.length, ?_,
      ⟨E.sb, E.rest.length, E.rest, fun x => x ∈ L ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.rest.length, E.k⟩, f,
      fun _ => t, fun _ => t, rfl, rfl, rfl, R''⟩
    rw [hm, hfr]; rfl
  refine bndC_of_view (tp := t) hb (fun x hx => ?_) (fun y hy => ?_)
  · by_cases h3 : x.space = 3
    · exact Or.inl h3
    by_cases h7 : x.space = 7
    · exact Or.inr (Or.inl h7)
    exact Or.inr (Or.inr ((hV x h3 h7).mp hx))
  · have hs : (ofFields y t).space = y.getD 0 0 := rfl
    have := cutView_sp hy
    exact (hV _ (by rw [hs]; exact this.1) (by rw [hs]; exact this.2)).mpr ⟨y, hy, rfl⟩

/-- **Re-entry from a plain boundary relation, segment trace** (`seg_reentryS` with `hB : Bnd`). -/
theorem seg_reentryS_bnd {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat}
    {m : List F} {L0 : List Msg} (hB : Bnd X sg s t S m L0)
    {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hcuti : (part Cut.In.table tr pub 30 busStk true).map decMsg =
      (cutView X s).map (fun y => ofFields y (pub.getD pubTIn 0).toNat))
    (hmemb : MembIn tr pub s) (ht : (pub.getD pubTIn 0).toNat = t) (hS : (pub.getD pubSIn 0).toNat = S)
    (hm : segM0 tr pub = m.set 5 ((s.frames.length - 1 : Nat) : F)) :
    BndC X sg s (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub) := by
  rw [ht, hS, hm]
  let MB := (part Memb.table tr pub 19 busStk true).map decMsg
  have hTn : (MB.map Msg.slot).Nodup := nodup_map_of_inj _ MB (memb_part_nodupS H) (fun a ha b hb e => by
    rw [(hmemb a ha).2, (hmemb b hb).2, ht, e])
  have hcv : ∀ x, x ∈ (part Cut.In.table tr pub 30 busStk true).map decMsg ↔ viewAt X s t x := by
    intro x; rw [hcuti, ht, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  have cuti_sp : ∀ x, x ∈ (part Cut.In.table tr pub 30 busStk true).map decMsg → x.space ≠ 3 ∧ x.space ≠ 7 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hcv x).mp hx
    exact cutView_sp hy
  refine bndC_reentry_bnd hnd hB (fun x h3 h7 => ?_) hTn (fun a ha => ?_) (fun x h3 => ?_)
  · rw [← hcv x]
    unfold initS
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact h
      · exact absurd (memb_mem_space h) h3
      · exact absurd (segb_mem_spaceS H h) h7
    · exact Or.inl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact (hmemb x hx).1
  · unfold initS
    simp only [List.mem_append]
    have hmv : x ∈ MB ↔ x ∈ memView (MB.map Msg.slot) s (fun _ => t) := by
      rw [mem_memView]
      constructor
      · intro hx
        refine ⟨x.slot, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
        have := (hmemb x hx).2; rw [ht] at this; exact this
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        have := (hmemb y hy).2; rw [ht] at this; rw [← this]; exact hy
    rw [← hmv]
    constructor
    · rintro (h | h | h)
      · exact absurd h3 (cuti_sp x h).1
      · exact h
      · have := segb_mem_spaceS H h; omega
    · exact fun h => Or.inr (Or.inl h)

/-- **What the verifier checks on the first segment's public values** (decidable, `EntryPub.decidable`):
for the entry state `s0`, the entry function's checked index `k`, in-time `t`, in-gas units `S` and
the 6-word digests `dc` (of `cutView X s0`) and `dm` (of the entry memory root). -/
def EntryPub (X : Ctx) (pub : List F) (s0 : St) (k t S : Nat) (dc dm : List Nat) : Prop :=
  (pub.getD pubTIn 0).toNat = t ∧ (pub.getD pubSIn 0).toNat = S ∧
  pub.getD pubPcIn 0 = ((X.offOf k : Nat) : F) ∧ pub.getD pubSbIn 0 = 0 ∧ pub.getD pubCidIn 0 = 0 ∧
  (dc.length = 6 ∧ (∀ w ∈ dc, w < 2 ^ 64) ∧ pubDig pub pubCtxIn = SegSha.limbsF dc ∧
    SegSha.wbytes dc = cutDigest (cutView X s0)) ∧
  (dm.length = 6 ∧ (∀ w ∈ dm, w < 2 ^ 64) ∧ pubDig pub pubMemIn = SegSha.limbsF dm ∧
    SegSha.wbytes dm = WasmView.memRootOf s0) ∧
  (pub.getD pubDepth 0).toNat = WasmView.memDepth s0 ∧ (pub.getD pubNblk 0).toNat = WasmView.nblkOf s0

instance EntryPub.decidable (X : Ctx) (pub : List F) (s0 : St) (k t S : Nat) (dc dm : List Nat) :
    Decidable (EntryPub X pub s0 k t S dc dm) := by
  unfold EntryPub; infer_instance

/-- **The named entry relation**: the entry state is related at `(t, S)`, at instruction 0 of the
checked function `k`, stack base 0, activation 0, to some live set (`wasm_base_sound_m2`'s `h0`
gives it via `Bnd.of_relW`). -/
def EntrySeed (X : Ctx) (sg : Nat → Nat × Nat) (s0 : St) (k t S : Nat) : Prop :=
  ∃ L0 : List Msg, Bnd X sg s0 t S (stMsg (X.offOf k + 0) (t + 1) S 0 0 0) L0

/-- **The first segment's in-relation from the call's entry state.** -/
theorem entry_inSA_mp (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St} {d0 : SegD}
    (hp : SegPremAMP X nloc ngl sg σ d0) {s0 : St} {k t S : Nat} {dc dm : List Nat}
    (hE : EntryPub X.toCtx d0.pub s0 k t S dc dm) (hseed : EntrySeed X.toCtx sg s0 k t S)
    (hfr : s0.frames.length = 1) (hw : RegWF s0) (hvwf : ∀ y ∈ cutView X.toCtx s0, MsgWF y)
    (hσ0 : sideR s0 = σ (t + 1)) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSA X sg σ d0 s0 := by
  have hP := P_val
  obtain ⟨ht, hS, hpc, hsb, hcid, ⟨hc6, hcW, hcp, hcd⟩, ⟨hm6, hmW, hmp, hmd⟩, hdep, hnb⟩ := hE
  obtain ⟨L0, hB⟩ := hseed
  have H' := hp.H.toSMP
  have hC' := SegSha.ChipIf.toSMP hp.H hp.hC
  have hctx : PubDigIs d0.pub pubCtxIn (cutDigest (cutView X.toCtx s0)) := ⟨dc, hc6, hcW, hcp, hcd⟩
  have hroot : MemRootIn d0.pub s0 := ⟨dm, hm6, hmW, hmp, hmd⟩
  have hG : MemGeom d0.pub s0 := ⟨hdep, hnb⟩
  rcases cuti_viewS H' hC' hvwf hctx with hc | hcuti
  · exact Or.inl hc
  rcases MemRoot.seg_membIn_mp hp.H hp.hC hp.hD30 hG hroot with hmb | hc
  case inr => exact Or.inl hc
  have htP : t < P := by rw [← ht]; exact Fp.toNat_lt _
  have hm : segM0 d0.tr d0.pub =
      (stMsg (X.toCtx.offOf k + 0) (t + 1) S 0 0 0).set 5 ((s0.frames.length - 1 : Nat) : F) := by
    rw [segM0_eq, hfr, hpc, hsb, hcid]
    have e1 : d0.pub.getD pubTIn 0 = ((t : Nat) : F) := by rw [← ht, Fp.cast_toNat]
    have e2 : d0.pub.getD pubSIn 0 = ((S : Nat) : F) := by rw [← hS, Fp.cast_toNat]
    rw [e1, e2]
    simp only [stMsg, Nat.add_zero, Nat.sub_self, List.set_cons_succ, List.set_cons_zero]
    simp only [Lean.Grind.Semiring.natCast_add, one_cast, zero_cast]
  have hB' := seg_reentryS_bnd (M2Ctx.toCtx_fns_nodup X) hB H' hcuti hmb ht hS hm
  refine Or.inr ⟨⟨⟨hB', hw, initS_nodupS H' hw hvwf hcuti, hroot⟩, hG, hctx, hvwf⟩, ?_⟩
  show sideR s0 = σ ((d0.pub.getD pubTIn 0).toNat + 1)
  rw [ht]; exact hσ0

/-! ## 2. Exit -/

/-- **The σ-pinned halting segment** (`seg_sound_haltS`'s shape through `exec_rowsJH`), `HoldsXS`.
The state `s` after `n − 1` rows is on the thread at `t_out` and its step is the terminal one. -/
theorem seg_sound_haltσS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hbL : HostBLinkedL tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (st : Nat) (hst12 : st = 1 ∨ st = 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    0 < (actListM2 tr pub).length ∧
    ∃ s, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length - 1) s0 = .cont s ∧
      sideR s = σ (pub.getD pubTOut 0).toNat ∧
      (st = 1 → ∃ sN, step X.toCtx.cfg X.toCtx.p s = .fin sN ∧
        NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
        X.toCtx.R * ((pub.getD pubSOut 0).toNat - (sg ((pub.getD pubTOut 0).toNat + 1)).1) + sN.gas.g =
          (sg ((pub.getD pubTOut 0).toNat + 1)).2) ∧
      (st = 2 → ∃ sN e, step X.toCtx.cfg X.toCtx.p s = .abort sN e ∧
        NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .abort sN e ∧
        X.toCtx.R * ((pub.getD pubSOut 0).toNat - (sg ((pub.getD pubTOut 0).toNat + 1)).1) + sN.gas.g =
          (sg ((pub.getD pubTOut 0).toNat + 1)).2) ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutoList tr)) := by
  have hP := P_val
  have hst2 : st ≤ 2 := by rcases hst12 with h | h <;> omega
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked tr pub := hostBLinked_ofS H hts (by omega) hbL
  have hlenEq := seg_lenS H hts (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  have hst := seg_hstS H
  rw [segMF_eq, hstN] at hst
  obtain ⟨_, _, hhalt, _⟩ := exec_rowsJH X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub)
    (consCHS tr pub) (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0)
    (pub.getD pubTOut 0 + 1) (pub.getD pubSOut 0) sg st hst2 (SigJ σ) hrows (pub.getD pubTIn 0).toNat
    (pub.getD pubSIn 0).toNat (segM0 tr pub) (pub.getD pubSbOut 0) (tr.cell 0 0 (ix Segb.cols "cidf")) hst
    (seg_hchS H X.toCtx hb hg) hinit (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas
    hg64 h0 (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial hσ0
  have hne : st ≠ 0 := by rcases hst12 with h | h <;> (subst h; decide)
  obtain ⟨hpos, s, hrun, hJ, hfin, hab⟩ := hhalt hne
  have eT : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 = (pub.getD pubTOut 0).toNat + 1 := by
    omega
  have eJ : sideR s = σ (pub.getD pubTOut 0).toNat := by
    have : SigJ σ ((pub.getD pubTIn 0).toNat + (actListM2 tr pub).length) s := hJ
    rw [show (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length = (pub.getD pubTOut 0).toNat by omega]
      at this
    exact this
  refine ⟨hlenEq, hpos, s, hrun, eJ, fun h1 => ?_, fun h2 => ?_, ctx_out_shaS H hC hl⟩
  · obtain ⟨sN, -, -, -, hstep, hs, -, hfr, hgas, -⟩ := hfin h1
    refine ⟨sN, hstep, hs, hfr, ?_⟩
    rw [eT] at hgas; exact hgas
  · obtain ⟨sN, e, hstep, hs, -, hgas⟩ := hab h2
    refine ⟨sN, e, hstep, hs, ?_⟩
    rw [eT] at hgas; exact hgas

/-- **The halting segment's premises, multiproof AIR** (no `HostRelyσ`/`HostPagesRely`; `hD30` for the
link into it). -/
structure SegPremHMP (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (σ : Nat → St) (st : Nat)
    (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAirMP nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hkeep : SegKeepM2 d.tr d.pub sg
  hsk : SigKeep d.tr d.pub σ
  hhold : HoldRowSσ X.toCtx d.tr d.pub sg σ
  hst12 : st = 1 ∨ st = 2
  hstN : d.pub.getD Boundary.pubStatus 0 = ((st : Nat) : F)
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  hD30 : Dn d.pub ≤ 30

/-- What the halting segment yields: the last pre-state `s` on the thread and its terminal step. -/
def HaltOut (X : M2Ctx) (sg : Nat → Nat × Nat) (σ : Nat → St) (st : Nat) (d : SegD) (s : St) (r : Res) :
    Prop :=
  sideR s = σ d.tOut ∧ step X.toCtx.cfg X.toCtx.p s = r ∧
  (st = 1 → ∃ sN, r = .fin sN ∧ sN.frames = [] ∧
    X.toCtx.R * (d.SOut - (sg (d.tOut + 1)).1) + sN.gas.g = (sg (d.tOut + 1)).2) ∧
  (st = 2 → ∃ sN e, r = .abort sN e ∧
    X.toCtx.R * (d.SOut - (sg (d.tOut + 1)).1) + sN.gas.g = (sg (d.tOut + 1)).2)

/-- **The pinned last pre-state is determined** by its Wasm-visible part, its gas register and the
thread (`sigJ_unique`): so `r = step s` (hence `callResult`) is a function of `σ (t_out)` and those. -/
theorem HaltOut.unique {X : M2Ctx} {sg : Nat → Nat × Nat} {σ : Nat → St} {st : Nat} {d : SegD} {s s' : St}
    {r : Res} (h : HaltOut X sg σ st d s r) (h' : sideR s' = σ d.tOut) (hv : HostFoot.vis s' = HostFoot.vis s)
    (hg : s'.gas.g = s.gas.g) : s' = s :=
  sigJ_unique (σ := σ) (t := d.tOut) h' h.1 hv hg

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **`seg_sound_haltσ_mp`**: the σ-pinned halting segment of the multiproof AIR, from `InSA`. -/
theorem seg_sound_haltσ_mp {st : Nat} {d : SegD} (hp : SegPremHMP X nloc ngl sg σ st d) {s0 : St}
    (hin : InSA X sg σ d s0) :
    0 < d.n ∧ ∃ s r, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (d.n - 1) s0 = .cont s ∧
      HaltOut X sg σ st d s r := by
  obtain ⟨⟨⟨h0, -, hinit, -⟩, -⟩, hσ0⟩ := hin
  have H := hp.H.toSMP
  obtain ⟨-, hpos, s, hrun, eJ, hfin, hab, -⟩ := seg_sound_haltσS X H (SegSha.ChipIf.toSMP hp.H hp.hC) hp.hl
    hp.hcode hp.hfunc (seg_hostBLinkedL H) (seg_regCLinked H) hp.hkeep hp.hsk hp.hhold st hp.hst12 hp.hstN
    hp.hlen hp.htin hp.hfeeN hstepgas hg64 hinit h0.1 hσ0
  refine ⟨hpos, s, step X.toCtx.cfg X.toCtx.p s, hrun, eJ, rfl, fun h1 => ?_, fun h2 => ?_⟩
  · obtain ⟨sN, hstep, -, hfr, hgas⟩ := hfin h1
    exact ⟨sN, hstep, hfr, hgas⟩
  · obtain ⟨sN, e, hstep, -, hgas⟩ := hab h2
    exact ⟨sN, e, hstep, hgas⟩

/-- **The link into the halting segment** (`link_stepAMP` with the halting segment's premises). -/
theorem link_stepHMP {st : Nat} {d d' : SegD} (hp' : SegPremHMP X nloc ngl sg σ st d')
    (hL : LinkPubM d.pub d'.pub) {s : St} (ho : OutSA X sg σ d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSA X sg σ d' s := by
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

open NearSpecV3.Wasm.CallCut in
/-- One terminal step on the call machine. -/
theorem csteps_last (q : CallArgs) (p : Prepared) (k : EntK) (s : St) (m : Nat) :
    CSteps q (.ent p k (.cont s) (m + 1)) (.ent p k (step q.cfg p s) m) := by
  have e : cstep q (.ent p k (.cont s) (m + 1)) = .ent p k (step q.cfg p s) m := by cases k <;> rfl
  exact .step (e ▸ .refl _)

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **A halting segment on lane E's call machine.** -/
theorem call_halt_csteps_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK) {st : Nat} {d : SegD}
    (hp : SegPremHMP X nloc ngl sg σ st d) {s0 : St} (hin : InSA X sg σ d s0) (n : Nat) (hn : d.n ≤ n) :
    ∃ s r, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k r (n - d.n)) ∧
      HaltOut X sg σ st d s r := by
  obtain ⟨hpos, s, r, hrun, hO⟩ := seg_sound_haltσ_mp X hstepgas hg64 hp hin
  refine ⟨s, r, ?_, hO⟩
  rw [← hq] at hrun
  have h1 := csteps_seg q X.toCtx.p k (d.n - 1) s0 s n hrun (by omega)
  have e : n - (d.n - 1) = (n - d.n) + 1 := by omega
  rw [e] at h1
  have h2 := csteps_last q X.toCtx.p k s (n - d.n)
  rw [hq, hO.2.1] at h2
  exact h1.trans h2

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **Cut segments, a link, then the halting segment, on lane E's call machine.** -/
theorem call_chain_halt_csteps_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) {st : Nat} (dl : SegD)
    (hok : ∀ d ∈ d0 :: ds, SegPremAMP X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds))
    (hLl : LinkPubM ((d0 :: ds).getLast (List.cons_ne_nil _ _)).pub dl.pub)
    (hpl : SegPremHMP X nloc ngl sg σ st dl) {s0 : St} (h0 : InSA X sg σ d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum + dl.n ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s r, CSteps q (.ent X.toCtx.p k (.cont s0) n)
          (.ent X.toCtx.p k r (n - ((d0 :: ds).map SegD.n).sum - dl.n)) ∧
        HaltOut X sg σ st dl s r := by
  rcases seg_chain_all_csteps_mp X hstepgas hg64 q hq k d0 ds hok hL h0 n (by omega) with hc | ⟨sC, h1, hO⟩
  · exact Or.inl hc
  rcases link_stepHMP X hpl hLl hO with hc | hin
  · exact Or.inl hc
  obtain ⟨s, r, h2, hH⟩ := call_halt_csteps_mp X hstepgas hg64 q hq k hpl hin
    (n - ((d0 :: ds).map SegD.n).sum) (by omega)
  exact Or.inr ⟨s, r, h1.trans h2, hH⟩

/-- `runFrom` at a terminal result is that result. -/
theorem runFrom_halt {cfg : NearCfg} {p : Prepared} {r : Res} {m : Nat}
    (h : (∃ sN, r = .fin sN) ∨ (∃ sN e, r = .abort sN e)) :
    NearSpecV3.Wasm.CallCut.runFrom cfg p r m = r := by
  rcases h with ⟨sN, rfl⟩ | ⟨sN, e, rfl⟩ <;> rfl

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **The call's result from its segments (M6.5 shape).**  Lane E's call machine reaches the
method's first instruction `.ent p .method (.cont s0) n`; the first segment `d0` starts at the entry
state (`EntryPub`, `EntrySeed`, …: `entry_inSA_mp`); cut segments `d0 :: ds` and a halting segment `dl`
of the multiproof AIR, all on one σ-thread with `σ (t_in d0 + 1) = sideR s0`.  Then SHA-384 collides,
or `callResult q = afterMethod (entPost r)` where `r = step s` is the terminal result (`.fin sN`
without frames for status 1, `.abort sN e` for status 2, gas equation at `dl`'s out-boundary) and
`sideR s = σ (t_out dl)`. -/
theorem callResult_of_segments_mp (q : CallArgs) (hq : q.cfg = X.toCtx.cfg)
    (d0 : SegD) (ds : List SegD) {st : Nat} (dl : SegD)
    (hok : ∀ d ∈ d0 :: ds, SegPremAMP X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPubM d.pub d'.pub) (d0 :: ds))
    (hLl : LinkPubM ((d0 :: ds).getLast (List.cons_ne_nil _ _)).pub dl.pub)
    (hpl : SegPremHMP X nloc ngl sg σ st dl)
    {s0 : St} {kf t S : Nat} {dc dm : List Nat}
    (hE : EntryPub X.toCtx d0.pub s0 kf t S dc dm) (hseed : EntrySeed X.toCtx sg s0 kf t S)
    (hfr : s0.frames.length = 1) (hw : RegWF s0) (hvwf : ∀ y ∈ cutView X.toCtx s0, MsgWF y)
    (hσ0 : sideR s0 = σ (t + 1))
    (n : Nat) (hpre : CSteps q .pre (.ent X.toCtx.p .method (.cont s0) n))
    (hn : ((d0 :: ds).map SegD.n).sum + dl.n ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s r, HaltOut X sg σ st dl s r ∧ callResult q = afterMethod (entPost r) := by
  rcases entry_inSA_mp X (hok d0 List.mem_cons_self) hE hseed hfr hw hvwf hσ0 with hc | h0
  · exact Or.inl hc
  rcases call_chain_halt_csteps_mp X hstepgas hg64 q hq .method d0 ds dl hok hL hLl hpl h0 n hn with
    hc | ⟨s, r, hcs, hH⟩
  · exact Or.inl hc
  refine Or.inr ⟨s, r, hH, ?_⟩
  have e1 : callResult q = cden q .pre := rfl
  rw [e1, cden_of_csteps hpre, cden_of_csteps hcs]
  have hr : (∃ sN, r = .fin sN) ∨ (∃ sN e, r = .abort sN e) := by
    rcases hpl.hst12 with h | h
    · obtain ⟨sN, e, -⟩ := hH.2.2.1 h; exact Or.inl ⟨sN, e⟩
    · obtain ⟨sN, e, e', -⟩ := hH.2.2.2 h; exact Or.inr ⟨sN, e, e'⟩
  show afterMethod (entPost (runFrom q.cfg X.toCtx.p r _)) = _
  rw [runFrom_halt hr]

end

end Cuti

#print axioms Cuti.bndC_reentry_bnd
#print axioms Cuti.seg_reentryS_bnd
#print axioms Cuti.entry_inSA_mp
#print axioms Cuti.seg_sound_haltσS
#print axioms Cuti.seg_sound_haltσ_mp
#print axioms Cuti.HaltOut.unique
#print axioms Cuti.link_stepHMP
#print axioms Cuti.call_halt_csteps_mp
#print axioms Cuti.call_chain_halt_csteps_mp
#print axioms Cuti.callResult_of_segments_mp

end WasmBase
