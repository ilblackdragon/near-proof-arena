import ZkFormal.NearV3.Render.UniqLocal

/-!
# ZkFormal.NearV3.Render.UniqRender — completeness of the `uniqV3` table

For honest entries `L` (`UOk L`) and any trace whose table `t` has the cells of
`UniqGen.cell L` (`Render/UniqGen.lean`):
* `uniq_render_local` (`Render/UniqLocal.lean`): `TableLocal Uniq.table`;
* `uniq_render_traffic`: its traffic is `uniqTraffic (uniqEntries L)` — active row
  `q = 32·t + i` receives `DIGS (eid_t, τ_t, i, bytes_t[i])`, and the first row of every
  segment with `eq = 1` sends `DUP (eid_t, peid_t)`; padding rows nothing;
* `uniqEntries_wf`: the view is well formed (`UniqWf`), i.e. the same view the soundness
  side (`UniqViewStmt`) extracts.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.Uniq (act sf sl ft eid peid tau st eq i bb cin cout dbit d diffE cmpG segConst)
open UniqGen UniqLocal

namespace UniqTraffic

theorem flatMap_opt {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.flatMap fun x => if p x then [f x] else []) = (l.filter p).map f
  | [] => rfl
  | x :: l => by
    simp only [List.flatMap_cons, List.filter_cons]
    rw [flatMap_opt p f l]
    cases p x <;> simp

section rows
variable {L : List UEnt} (ok : UOk L) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : 32 * L.length ≤ H)
  (hc : ∀ q col, q < H → col < 53 → tr.cell tt q col = Fp.ofNat (cell L H q col))
include ok hH hHS hc

def msgD (L : List UEnt) (q : Nat) : List Fp :=
  [Fp.ofNat (ent L (q / 32)).eid, Fp.ofNat (ent L (q / 32)).tau, Fp.ofNat (q % 32),
    Fp.ofNat ((ent L (q / 32)).bytes.getD (q % 32) 0)]

def msgU (L : List UEnt) (q : Nat) : List Fp := [Fp.ofNat (ent L (q / 32)).eid, Fp.ofNat (peidOf L (q / 32))]

theorem rowR {q : Nat} (hq : q < H) (b : Nat) :
    rowTraffic Uniq.interactions tr tt q pub b false =
      if b = B_DIGS ∧ q < 32 * L.length then [msgD L q] else [] := by
  simp only [rowTraffic, Uniq.interactions, recv, send, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ZkFormal.Near.Render.multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c,
    Bool.true_eq_false, and_false, if_false, List.append_nil, and_true]
  by_cases ha : q < 32 * L.length
  · have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
    simp only [cq, act, eid, tau, i, bb, Nat.reduceLT, actCell, ofNat1, if_true, List.replicate_one, ha,
      and_true, bbAt, msgD]
    by_cases hb : b = B_DIGS
    · simp [hb]
    · simp [hb, Ne.symm hb]
  · simp only [cP ok hH hHS hc hq ha (by decide : act < 21), ha, and_false, if_false, fp_zero_ne_one,
      List.replicate_zero]
    split <;> rfl

theorem rowS {q : Nat} (hq : q < H) (b : Nat) :
    rowTraffic Uniq.interactions tr tt q pub b true =
      if b = B_DUP ∧ q < 32 * L.length ∧ q % 32 = 0 ∧ eqOf L (q / 32) = 1 then [msgU L q] else [] := by
  simp only [rowTraffic, Uniq.interactions, recv, send, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ZkFormal.Near.Render.multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    Bool.false_eq_true, and_false, if_false, List.nil_append, and_true]
  by_cases ha : q < 32 * L.length
  · have cq := fun (x : Nat) (hx : x < 21) => cA ok hH hHS hc hq ha hx
    simp only [cq, sf, eq, eid, peid, Nat.reduceLT, actCell, ha, true_and, msgU]
    have hm : (Fp.ofNat (if q % 32 = 0 then 1 else 0) * Fp.ofNat (eqOf L (q / 32)) = 1) ↔
        (q % 32 = 0 ∧ eqOf L (q / 32) = 1) := by
      rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 (eq_le (L := L) (q / 32)) with h | h <;> rw [h] <;>
        split <;> rename_i hq0 <;> simp only [ofNat0, ofNat1, hq0, true_and, false_and] <;> grind
    simp only [hm]
    by_cases hb : b = B_DUP
    · subst hb; by_cases hk : q % 32 = 0 ∧ eqOf L (q / 32) = 1 <;> simp [hk, ofNat1]
    · have hb' : ¬ B_DUP = b := fun h => hb h.symm
      simp [hb, hb']
  · have h0 : ¬ ((0 : Fp) * tr.cell tt q eq = 1) := by grind
    simp only [cP ok hH hHS hc hq ha (by decide : sf < 21), ha, false_and, and_false, if_false, h0]
    split <;> simp

end rows

end UniqTraffic

open UniqTraffic in
/-- **The honest `uniqV3` table has the traffic of `uniqEntries L`.**  Same hypotheses on the
trace as `uniq_render_local`. -/
theorem uniq_render_traffic (L : List UEnt) (hok : UOk L) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (32 * L.length))
    (hcell : ∀ r x, r < tr.height t → x < Uniq.width →
      tr.cell t r x = Fp.ofNat (UniqGen.cell L (tr.height t) r x)) :
    TableTraffic Uniq.interactions tr t pub (uniqTraffic (uniqEntries L)) := by
  have hle : 32 * L.length ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hlen : (uniqEntries L).length = L.length := by simp [uniqEntries]
  have hget : ∀ q, q < 32 * L.length → (uniqEntries L).getD (q / 32) default =
      { eid := (ent L (q / 32)).eid, peid := peidOf L (q / 32), tau := (ent L (q / 32)).tau,
        st := stOf L (q / 32), eq := eqOf L (q / 32), bytes := (ent L (q / 32)).bytes } := by
    intro q hq
    simp [uniqEntries, List.getD_eq_getElem?_getD, show q / 32 < L.length by omega]
  apply traffic_of
  · intro b
    rw [range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        rw [rowS hok rfl hle hcell (by have := List.mem_range.1 hq'; omega)]
        rw [if_neg (fun h => by omega)]),
      List.append_nil, range_flatMap_chunks 32]
    simp only [uniqTraffic, uniqSends]
    by_cases hb : b = B_DUP
    · subst hb
      simp only [if_true]
      rw [flatMap_congr' (g := fun t => if eqOf L t == 1 then [msgU L (32 * t)] else []) (fun t ht => by
        have ht := List.mem_range.1 ht
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
        rw [rowS hok rfl hle hcell (by omega)]
        rw [flatMap_nil' (fun j hj => by
          have := List.mem_range.1 hj
          rw [rowS hok rfl hle hcell (by omega)]
          rw [if_neg (by omega)])]
        simp only [true_and, Nat.add_zero, show 32 * t < 32 * L.length by omega,
          show 32 * t % 32 = 0 by omega, show 32 * t / 32 = t by omega, List.append_nil]
        by_cases he : eqOf L t = 1 <;> simp [he])]
      rw [flatMap_opt, uniqEntries, List.filter_map, List.map_map, List.map_map]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro x _
      simp [msgU, Msg.toFp, show 32 * x / 32 = x by omega]
    · rw [flatMap_nil' (fun t ht => flatMap_nil' (fun j hj => by
        have := List.mem_range.1 ht; have := List.mem_range.1 hj
        rw [rowS hok rfl hle hcell (by omega)]; simp [hb]))]
      simp [hb]
  · intro b
    rw [range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        rw [rowR hok rfl hle hcell (by have := List.mem_range.1 hq'; omega)]
        simp)]
    simp only [uniqTraffic, uniqRecvs, List.append_nil]
    by_cases hb : b = B_DIGS
    · subst hb
      rw [flatMap_single (g := msgD L) (fun q hq => by
        rw [rowR hok rfl hle hcell (by have := List.mem_range.1 hq; omega)]
        simp [List.mem_range.1 hq])]
      simp only [if_true]
      rw [show (fun (e : UniqE) => (List.range 32).map fun j => [e.eid, e.tau, j, e.bytes.getD j 0]) =
          (fun e => (List.range 32).map ((fun (e : UniqE) j => [e.eid, e.tau, j, e.bytes.getD j 0]) e)) from rfl,
        flatMap_chunks 32 (by decide) default, hlen, List.map_map]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro q hq
      have hq := List.mem_range.1 hq
      simp only [Function.comp_apply, hget q hq]
      simp [msgD, Msg.toFp]
    · rw [flatMap_nil' (fun q hq => by
        rw [rowR hok rfl hle hcell (by have := List.mem_range.1 hq; omega)]; simp [hb])]
      simp [hb]

/-! ## The view is well formed -/

theorem uniqEntries_wf (L : List UEnt) (hok : UOk L) : UniqWf (uniqEntries L) := by
  have hget : ∀ t (ht : t < (uniqEntries L).length), (uniqEntries L)[t] =
      { eid := (ent L t).eid, peid := peidOf L t, tau := (ent L t).tau,
        st := stOf L t, eq := eqOf L t, bytes := (ent L t).bytes } := by
    intro t ht; simp [uniqEntries]
  have hlen : (uniqEntries L).length = L.length := by simp [uniqEntries]
  have hmem : ∀ e ∈ uniqEntries L, ∃ t, t < L.length ∧ e =
      { eid := (ent L t).eid, peid := peidOf L t, tau := (ent L t).tau,
        st := stOf L t, eq := eqOf L t, bytes := (ent L t).bytes } := by
    intro e he
    simp only [uniqEntries, List.mem_map, List.mem_range] at he
    obtain ⟨t, ht, rfl⟩ := he
    exact ⟨t, ht, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨t, ht, rfl⟩ := hmem e he
    exact (ent_ok hok ht).1
  · intro e he
    obtain ⟨t, ht, rfl⟩ := hmem e he
    have h := ent_ok hok ht
    refine ⟨h.2.2.1, ?_, by dsimp only; omega, st_le _, eq_le _, fun y hy => ?_⟩
    · simp only [peidOf]; split
      · exact Nat.lt_of_le_of_lt (Nat.zero_le _) h.2.2.1
      · exact (ent_ok hok (show t - 1 < L.length by omega)).2.2.1
    · have := h.2.1 y hy
      have : (256 : Nat) < ZkFormal.Algebra.P := by decide
      omega
  · intro e he
    cases hL : L with
    | nil => simp [uniqEntries, hL] at he
    | cons x xs =>
      simp only [uniqEntries, hL, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.head?_cons, Option.some.injEq] at he
      rw [← he]; exact eq0 (L := x :: xs)
  · intro t ht
    have ht' : t + 1 < L.length := by omega
    rw [hget (t + 1) ht, hget t (by omega)]
    simp only
    have hts := tau_step hok ht'
    have htP := (ent_ok hok ht').2.2.2
    refine ⟨by simp [peidOf], ?_, fun he => ?_, fun he hs hb => ?_⟩
    · rw [hts, Nat.mod_eq_of_lt (by omega)]
    · have hst : stOf L (t + 1) = 0 := by have := eq_st (L := L) (t + 1); rw [he] at this; omega
      refine ⟨hst, fun _ => ?_⟩
      simp only [eqOf] at he; split at he
      · rename_i h; simpa using h.2
      · omega
    · have hs' : same L (t + 1) = true := (same_iff _).2 ⟨by omega, hs⟩
      have h1 := adj hok ht' hs'
      simp only [he, prevOf, curOf, Nat.add_sub_cancel] at h1
      omega

end ZkFormal.NearV3.Render
