import WasmBase.Main.SegReentry
import WasmBase.Main.SegS.SegCuti
/-!
# WasmBase.Main.SegS.SegReentry — `SegReentry`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegReentry.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P

namespace Cuti

theorem segb_mem_spaceS {nloc ngl : Nat} {tr : Trace} {pub : List F} (H : HoldsXS nloc ngl pub tr)
    {x : Msg} (hx : x ∈ (part Segb.table tr pub 0 busStk true).map decMsg) : x.space = 7 := by
  rw [segb_part tr pub (seg_h0S H), List.mem_singleton] at hx
  rw [hx]; exact segb_gas_space tr pub

/-- **Re-entry for a segment trace (item 4).**  The previous out-boundary `BndC X sg s t S m L0`; the
next trace's CUTI part is the view of `s` at `t_in` (`cuti_viewS`), MEMB's in-side productions are
bytes of `s` (`MembIn`, sub-lane MEM), `t_in = t`, `S_in = S`, and SEGB's first STATE message is `m`
with `cid` the depth.  Then the next segment's `h0` holds. -/
theorem seg_reentryS {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F}
    {L0 : List Msg} (hB : BndC X sg s t S m L0)
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
  refine bndC_reentry hnd hB (fun x h3 h7 => ?_) hTn (fun a ha => ?_) (fun x h3 => ?_)
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

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **SEGB's CIDMAP query `[cidf, cid_out]` is answered**: by SEGB's own `0 ↦ 0`, or by an active
CUTO record row's `slot ↦ F1`. -/
theorem segb_cidm_answerS :
    (tr.cell 0 0 (ix Segb.cols "cidf") = 0 ∧ pub.getD pubCidOut 0 = 0) ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        tr.cell 0 0 (ix Segb.cols "cidf") = ((rowNat tr 31 r' 48 : Nat) : F) ∧
        pub.getD pubCidOut 0 = ((cutoF tr r' 1 : Nat) : F) := by
  have ht0 : 0 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hi : (⟨busCidm, false, .first, [Segb.c "cidf", pv pubCidOut]⟩ : Inter) ∈ Segb.table.inters := by
    simp [Segb.table, Segb.inters]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr
    ⟨0, ht0, 0, seg_h0S H, _, by rw [seg_t0]; exact hi, rfl⟩
  have hc : ((Expr.first).eval (tr.row pub 0 0)).toNat = 1 := by simp [Expr.eval, Trace.row]; rfl
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_sendS H 14 (cidm_recv_bitsS H) hocc rfl rfl hc
  obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' hm' hc'
  have hmsg : ([Segb.c "cidf", pv pubCidOut] : List Expr).map (·.eval (tr.row pub 0 0)) =
      [tr.cell 0 0 (ix Segb.cols "cidf"), pub.getD pubCidOut 0] := by
    simp [Segb.c, v, pv, Expr.eval, Trace.row]
  rw [hmsg] at hm'
  by_cases h0 : t' = 0
  · subst h0
    have hm := mem_filter14 hi' hb'
    rw [seg_t0, segb_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · simp at hs'
    · left
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm'
      exact ⟨hm'.1.symm, hm'.2.symm⟩
  by_cases h31 : t' = 31
  · subst h31
    have hm := mem_filter14 hi' hb'
    rw [seg_t31', cuto_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp at hs'
    · simp at hs'
    · right
      obtain ⟨-, i48, -, -, -, -, -, -, -, -, -, -, -, i60, -⟩ := cuto_ix2
      have hmm : rowNat tr 31 r' 60 ≠ 0 := by
        intro h0; simp only [cuto_evalc tr pub r' i60, h0] at hc'; exact hc' rfl
      have h53 := cuto_mmS H hr' hmm
      have ha : rowNat tr 31 r' 0 = 1 := by
        have := (cuto_kindsS H hr').2.2.2.2.2.2; have := (cuto_bitsS H hr').1; omega
      refine ⟨r', hr', h53, ha, ?_⟩
      simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r' i48,
        cuto_evalF tr pub r' (show 1 < 7 by omega), List.cons.injEq, and_true] at hm'
      exact ⟨hm'.1.symm, hm'.2.symm⟩
  · exact absurd hb' (seg_cidm_tables nloc ngl t' ht' h0 h31 i' hi')

/-- **The public `cid_out` is the depth of the out-state** (cut case): from the out-boundary
relation `BndC` of `seg_soundS`, with `CutoHiLimbs` and `TombDead` (as `seg_soundS`). -/
theorem seg_cid_outS {X : Ctx} (hnd : X.M.fns.Nodup) (hl : CutoHiLimbs tr) (hT : TombDead tr pub (finS tr pub))
    {sg : Nat → Nat × Nat} {sN : St} {t S : Nat} (hB : BndC X sg sN t S (segFinM tr pub) (finS tr pub)) :
    pub.getD pubCidOut 0 = ((sN.frames.length - 1 : Nat) : F) := by
  have hP := P_val
  obtain ⟨⟨k, pc, sb, cid, hm, E, f, tps, tpl, rfl, rfl, rfl, R⟩, hreg, hsp⟩ := hB
  have hcidf : tr.cell 0 0 (ix Segb.cols "cidf") = ((E.cid : Nat) : F) := by
    have := congrArg (fun l => l.getD 5 0) hm
    simpa [segFinM, stMsg] using this
  have hfr : sN.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  rw [hfr]
  have hcl := R.cidLt
  obtain ⟨σ, A, hok, -, -, -, -⟩ := R.relabel_viewL hnd hreg hsp
  have hI := idsOK_of_relW R hok
  obtain ⟨sv, hc, -, -, hd, rfl⟩ := hok
  have hF := cutoFin_ofS H (seg_cuto_in_fin (tr := tr) (pub := pub)) (seg_finSplitS H) hT
  rcases segb_cidm_answerS H with ⟨h0, hc0⟩ | ⟨r', hr', h53, ha, hsl, hco⟩
  · rw [hcidf] at h0
    have e0 : E.cid = 0 := natEq (R := 0) h0 (by omega) (by omega)
    rw [(R.entry e0).1, hc0]; rfl
  · rw [hcidf] at hsl
    have es : E.cid = rowNat tr 31 r' 48 := natEq hsl (by omega) (rowNat_lt _ _ _ _)
    obtain ⟨hdep, -⟩ := cuto_k4_depS H hl hI hF hr' h53
    have hF1 := (cuto_fieldfactsS H hl hr' ha).2.2.2.1 h53
    rw [hco, hF1, hdep, ← es, hd.top, hc.len]

end

end Cuti

end WasmBase
