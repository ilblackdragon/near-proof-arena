import ZkFormal.V2.PG.NpPrefix
import ZkFormal.V2.PG.NpQ
import ZkFormal.Udr.Np.QueryFacts

/-!
# ZkFormal.V2.PG.NpHon (P2 copy of `Prover.NpHon` at `dp = pg g`) — the honest complete transcript `honT cs`

Header, challenges (`= cs`), clear-text parts (`[finals, ood, final polynomial]`) and
oracles (`[main, aux, quot] ++ FRI layers in chain order`).
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem nMsg_eq : nMsg A tr = 4 + nB A tr + (kinds A tr).length := by
  have := nB_pos A tr
  simp [nMsg, slotPairs]; omega

/-- The honest messages in order. -/
theorem msgs_eq (cs : List Fp8) :
    (List.range (nMsg A tr + 1)).map (npMsg A cb tr cs) =
      [npMsg A cb tr cs 0, npMsg A cb tr cs 1, npMsg A cb tr cs 2, npMsg A cb tr cs 3,
        npMsg A cb tr cs 4] ++ List.replicate (nB A tr - 1) [] ++
      (kinds A tr).map (kindMsg A cb tr cs) ++ [[.elems (finalPoly A cb tr cs)]] := by
  have hb := nB_pos A tr
  rw [nMsg_eq, show 4 + nB A tr + (kinds A tr).length + 1 =
      5 + ((nB A tr - 1) + ((kinds A tr).length + 1)) by omega,
    List.range_add, List.range_add, List.range_add]
  simp only [List.map_append, List.map_map, List.append_assoc]
  have app : ∀ {a b c d : List (List (PartV Fp8 (Oracle Fp)))}, a = b → c = d → a ++ c = b ++ d :=
    fun h1 h2 => h1 ▸ h2 ▸ rfl
  refine app rfl (app ?_ (app ?_ ?_))
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
    unfold npMsg
    simp only [show 5 + i ≠ 0 by omega, show 5 + i ≠ 1 by omega, show 5 + i ≠ 2 by omega,
      show 5 + i ≠ 3 by omega, show 5 + i ≠ 4 by omega, show 5 + i < 4 + nB A tr by omega, ite_false,
      ite_true]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    unfold npMsg
    simp only [show 5 + (nB A tr - 1 + i) ≠ 0 by omega, show 5 + (nB A tr - 1 + i) ≠ 1 by omega,
      show 5 + (nB A tr - 1 + i) ≠ 2 by omega, show 5 + (nB A tr - 1 + i) ≠ 3 by omega,
      show 5 + (nB A tr - 1 + i) ≠ 4 by omega, show ¬ 5 + (nB A tr - 1 + i) < 4 + nB A tr by omega,
      ite_false, show 5 + (nB A tr - 1 + i) - (4 + nB A tr) = i by omega,
      List.getElem?_eq_getElem h1]
  · simp only [List.range_one, List.map_cons, List.map_nil, Function.comp]
    unfold npMsg
    have hk : (kinds A tr)[5 + (nB A tr - 1 + ((kinds A tr).length + 0)) - (4 + nB A tr)]? = none := by
      rw [show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) - (4 + nB A tr) = (kinds A tr).length by omega]
      simp
    simp only [show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) ≠ 0 by omega,
      show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) ≠ 1 by omega,
      show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) ≠ 2 by omega,
      show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) ≠ 3 by omega,
      show 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) ≠ 4 by omega,
      show ¬ 5 + (nB A tr - 1 + ((kinds A tr).length + 0)) < 4 + nB A tr by omega, ite_false, hk]

/-- Entries of the honest transcript, read through a per-entry extraction. -/
theorem fullEntries_flatMap {β : Type} (cs : List Fp8) (f : Entry Fp8 (Oracle Fp) → List β)
    (hc : ∀ c, f (.chal c) = []) :
    (fullEntries A cb tr cs).flatMap f =
      ((List.range (nMsg A tr + 1)).map (npMsg A cb tr cs)).flatMap fun m => f (.msg m) := by
  unfold fullEntries
  rw [List.flatMap_append, List.flatMap_assoc, List.range_succ, List.map_append, List.flatMap_append]
  congr 1
  rw [List.flatMap_map]; congr 1; funext j
  simp [hc]

theorem honT_header (cs : List Fp8) : (honT A cb tr cs).header? = some (hdr A tr) := by
  have hn : nMsg A tr = (nMsg A tr - 1) + 1 := by rw [nMsg_eq]; omega
  unfold honT fullEntries PT.header?
  rw [hn, List.range_succ_eq_map]
  simp [npMsg]

theorem flatMap_single {α β : Type} (g : α → β) : ∀ l : List α, (l.flatMap fun a => [g a]) = l.map g
  | [] => rfl
  | a :: l => by simp [flatMap_single g l]

theorem honT_chals (cs : List Fp8) (hl : cs.length = nMsg A tr) : (honT A cb tr cs).chals = cs := by
  unfold honT PT.chals fullEntries
  rw [List.filterMap_append, List.filterMap_flatMap]
  simp only [List.filterMap_cons, List.filterMap_nil, Option.some.injEq, List.append_nil]
  rw [flatMap_single]
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem npMsg_0 (cs : List Fp8) : npMsg A cb tr cs 0 = [.header (hdr A tr), .oracle (mainO A tr)] := by
  simp [npMsg]
theorem npMsg_1 (cs : List Fp8) : npMsg A cb tr cs 1 = [] := by simp [npMsg]
theorem npMsg_2 (cs : List Fp8) :
    npMsg A cb tr cs 2 = [.oracle (auxOc A cb tr cs), .elems (finalsC A cb tr cs)] := by simp [npMsg]
theorem npMsg_3 (cs : List Fp8) : npMsg A cb tr cs 3 = [.oracle (quotOc A cb tr cs)] := by simp [npMsg]
theorem npMsg_4 (cs : List Fp8) : npMsg A cb tr cs 4 = [.elems (oodC A cb tr cs)] := by simp [npMsg]

theorem flatMap_rep_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (n : Nat) :
    (List.replicate n []).flatMap f = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatMap_cons, ih, hf]; rfl

theorem flatMap_map_nil {α β γ : Type} (f : β → List γ) (g : α → β) (l : List α)
    (h : ∀ a ∈ l, f (g a) = []) : (l.map g).flatMap f = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro m hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  exact h k hk

theorem honT_elems (cs : List Fp8) :
    (honT A cb tr cs).elems = [finalsC A cb tr cs, oodC A cb tr cs, finalPoly A cb tr cs] := by
  unfold PT.elems honT
  rw [fullEntries_flatMap A cb tr cs _ (fun _ => rfl), msgs_eq, npMsg_0, npMsg_1, npMsg_2, npMsg_3,
    npMsg_4]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.filterMap_cons,
    List.filterMap_nil, List.append_nil, List.nil_append, List.cons_append]
  rw [flatMap_rep_nil _ rfl, flatMap_map_nil _ _ _ (fun k _ => ?_)]
  · rfl
  · unfold kindMsg
    split
    · rfl
    · split <;> rfl

theorem honT_oracles (cs : List Fp8) :
    (honT A cb tr cs).oracles = [mainO A tr, auxOc A cb tr cs, quotOc A cb tr cs] ++
      (commits A tr).map (fun p => [friMat A cb tr cs p.1 p.2]) := by
  unfold PT.oracles honT
  rw [fullEntries_flatMap A cb tr cs _ (fun _ => rfl), msgs_eq, npMsg_0, npMsg_1, npMsg_2, npMsg_3,
    npMsg_4, ← kinds_flatMap_fold A tr (fun c a => [friMat A cb tr cs c a])]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.filterMap_cons,
    List.filterMap_nil, List.append_nil, List.nil_append, List.cons_append]
  rw [flatMap_rep_nil _ rfl, List.flatMap_map]
  simp only [List.nil_append, List.cons_append, List.cons.injEq, true_and]
  congr 1; funext k
  unfold kindMsg
  split
  · simp [*]
  · split <;> rename_i h <;> simp [h]

end

end ZkFormal.V2.PG
