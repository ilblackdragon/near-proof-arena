import WasmBase.Main.SegLinkage
import WasmBase.Main.SegS.SegHalt
/-!
# WasmBase.Main.SegS.SegLinkage — `SegLinkage`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegLinkage.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **Row times are injective** on the action list of a segment trace: the STATE chain visits every
row once, at time `t_in + 1 + k` for its position `k`. -/
theorem seg_lvl_injS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ ρ ∈ actListM2 tr pub, ∀ ρ' ∈ actListM2 tr pub, lvl (rowInM tr pub ρ) = lvl (rowInM tr pub ρ') → ρ = ρ' := by
  have hP := P_val
  let act := actListM2 tr pub
  let g : Nat × Nat → List F × List F := fun r => (rowInM tr pub r, rowOutM tr pub r)
  have hE1 : (act.map g).map Prod.snd = act.map (rowOutM tr pub) := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map (rowInM tr pub) := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact hts r hr
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (segM0 tr pub) (segMF tr pub) lvl
    (by rw [hE1, hE2]; exact seg_hstS H) hstepE (by simp [act]; omega)
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hal : act.length = (actListM2 tr pub).length := rfl
  obtain ⟨lk, -⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  simp only [List.length_map, List.getElem_map] at lk
  have e0 : lvl (segM0 tr pub) = (((pub.getD pubTIn 0).toNat + 1 : Nat) : F) := by
    rw [segM0_eq, Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]; rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (rowInM tr pub rs[k]) =
      (((pub.getD pubTIn 0).toNat + 1 + k : Nat) : F) := by
    intro k hk
    rw [show rowInM tr pub rs[k] = (g rs[k]).1 from rfl, lk k hk, e0, ← Lean.Grind.Semiring.natCast_add]
  intro ρ hρ ρ' hρ' hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hrs.symm.subset hρ)
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem (hrs.symm.subset hρ')
  rw [lvlk k hk, lvlk k' hk'] at hl
  have := congrArg Fp.toNat hl
  rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)] at this
  have : k = k' := by omega
  subst this; rfl

/-- **`HostBLinked.unique` from the STATE chain**: two active HOST rows with the same `ts` are the
same row (the `hid` equality is not even needed). -/
theorem hostB_uniqueS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ r r', r < tr.height 22 → rowAct Host.table tr pub 22 r →
      r' < tr.height 22 → rowAct Host.table tr pub 22 r' →
      rowNat tr 22 r cTs = rowNat tr 22 r' cTs → rowNat tr 22 r Host.hid = rowNat tr 22 r' Host.hid →
      r = r' := by
  intro r r' hr ha hr' ha' hts' _
  have := seg_lvl_injS H hts hsz _ (host_mem_actListM2 hr ha) _ (host_mem_actListM2 hr' ha')
    (by rw [host_lvl, host_lvl, hts'])
  simpa using this

/-- **`HostBLinked` from its `linked` half** on a segment trace. -/
theorem hostBLinked_ofS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P)
    (hL : HostBLinkedL tr pub) : HostBLinked tr pub :=
  ⟨hL, hostB_uniqueS H hts hsz⟩

end WasmBase
