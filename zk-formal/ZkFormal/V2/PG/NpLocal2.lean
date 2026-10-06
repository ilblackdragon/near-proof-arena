import ZkFormal.V2.PG.NpLocal

/-!
# ZkFormal.V2.PG.NpLocal2 (P2 copy of `Prover.NpLocal2` at `dp = pg g`) — the verifier's and the prover's DEEP contexts agree
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

theorem chals_append (cb : Bytes) (es1 es2 : List (Entry Fp8 Unit)) :
    PT.chals (⟨cb, es1 ++ es2⟩ : PT Fp8 Unit) = PT.chals ⟨cb, es1⟩ ++ PT.chals ⟨cb, es2⟩ := by
  simp [PT.chals, List.filterMap_append]

theorem elems_append (cb : Bytes) (es1 es2 : List (Entry Fp8 Unit)) :
    PT.elems (⟨cb, es1 ++ es2⟩ : PT Fp8 Unit) = PT.elems ⟨cb, es1⟩ ++ PT.elems ⟨cb, es2⟩ := by
  simp [PT.elems, List.flatMap_append]

theorem chals_map_chal (cb : Bytes) : ∀ l : List Fp8, PT.chals (⟨cb, l.map Entry.chal⟩ : PT Fp8 Unit) = l
  | [] => rfl
  | a :: l => (show PT.chals (⟨cb, Entry.chal a :: l.map Entry.chal⟩ : PT Fp8 Unit) =
      a :: PT.chals ⟨cb, l.map Entry.chal⟩ from rfl).trans (by rw [chals_map_chal cb l])

theorem elems_map_chal (cb : Bytes) : ∀ l : List Fp8, PT.elems (⟨cb, l.map Entry.chal⟩ : PT Fp8 Unit) = []
  | [] => rfl
  | a :: l => (show PT.elems (⟨cb, Entry.chal a :: l.map Entry.chal⟩ : PT Fp8 Unit) =
      PT.elems ⟨cb, l.map Entry.chal⟩ from rfl).trans (elems_map_chal cb l)

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

theorem prep_honT_eq (hlen : cs.length = nMsg A tr) :
    (Vd A).prep (honT A cb tr cs).erase = prepCore A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs)
      (cs.drop 4) (finalsC A cb tr cs) (oodC A cb tr cs) (finalPoly A cb tr cs) := prep_hon A cb tr cs hlen

theorem ctx0_eq (hlen : cs.length = nMsg A tr) :
    ctx0 A cb tr cs = prepCore A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs)
      ((cs.take (4 + nB A tr) ++ List.replicate (kinds A tr).length 0).drop 4)
      (finalsC A cb tr cs) (oodC A cb tr cs) [0, 0] := by
  have h4 : 4 ≤ cs.length := by rw [hlen, nMsg_eq]; omega
  unfold ctx0
  rw [prep_eq A (standin A cb tr cs) (hdr := hdr A tr) (αfp := cAfp cs) (γ := cGam cs) (αc := cAc cs)
    (z := cZ cs) (rest := (cs.take (4 + nB A tr) ++ List.replicate (kinds A tr).length 0).drop 4)
    (finals := finalsC A cb tr cs) (ood := oodC A cb tr cs) (fp := [0, 0])]
  · rfl
  · rfl
  · unfold standin
    rw [chals_append, chals_append, chals_map_chal]
    show [] ++ _ ++ [] = _
    rw [List.nil_append, List.append_nil]
    match cs, h4 with
    | a :: b :: c :: d :: rest, _ => rw [show 4 + nB A tr = nB A tr + 4 by omega]; rfl
  · unfold standin
    rw [elems_append, elems_append, elems_map_chal]
    rfl

theorem honCtx_prep (hlen : cs.length = nMsg A tr) :
    HonCtx A cb tr cs ((Vd A).prep (honT A cb tr cs).erase) := by
  rw [prep_honT_eq A cb tr cs hlen]
  obtain ⟨hd, hz, hl⟩ := prepCore_deep A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs) (cs.drop 4)
    (finalsC A cb tr cs) (oodC A cb tr cs) (finalPoly A cb tr cs) _ _ (splitOod_hon A cb tr _ _ _ _)
  exact ⟨hl, hz, _, hd⟩

theorem honCtx_ctx0 (hlen : cs.length = nMsg A tr) : HonCtx A cb tr cs (ctx0 A cb tr cs) := by
  rw [ctx0_eq A cb tr cs hlen]
  obtain ⟨hd, hz, hl⟩ := prepCore_deep A cb (hdr A tr) (cAfp cs) (cGam cs) (cAc cs) (cZ cs) _
    (finalsC A cb tr cs) (oodC A cb tr cs) [0, 0] _ _ (splitOod_hon A cb tr _ _ _ _)
  exact ⟨hl, hz, _, hd⟩

/-- Both contexts have the same DEEP entries. -/
theorem deep_same (hlen : cs.length = nMsg A tr) :
    ((Vd A).prep (honT A cb tr cs).erase).deep = (ctx0 A cb tr cs).deep := by
  rw [prep_honT_eq A cb tr cs hlen, ctx0_eq A cb tr cs hlen]
  unfold oodC
  rw [
    (prepCore_deep A cb (hdr A tr) _ _ _ _ _ _ _ _ _ _ (splitOod_hon A cb tr _ _ _ _)).1,
    (prepCore_deep A cb (hdr A tr) _ _ _ _ _ _ _ _ _ _ (splitOod_hon A cb tr _ _ _ _)).1]
  have h4 : 4 + nB A tr ≤ cs.length := by rw [hlen, nMsg_eq]; omega
  have hb : nB A tr = batchRounds (layout A dp (hdr A tr)) := rfl
  rw [← hb]
  congr 4
  rw [List.drop_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega),
    List.drop_take, List.take_take]
  congr 1; simp

theorem deepH_same (hlen : cs.length = nMsg A tr) (m : Nat) (ξ : Fp8) :
    deepH A cb tr cs ((Vd A).prep (honT A cb tr cs).erase) m ξ = deepH A cb tr cs (ctx0 A cb tr cs) m ξ := by
  unfold deepH
  apply deepZ_ctx
  · rw [(honCtx_prep A cb tr cs hlen).1, (honCtx_ctx0 A cb tr cs hlen).1]
  · exact deep_same A cb tr cs hlen
  · rw [(honCtx_prep A cb tr cs hlen).2.1, (honCtx_ctx0 A cb tr cs hlen).2.1]

theorem ctx0_n0 (hlen : cs.length = nMsg A tr) : (ctx0 A cb tr cs).n0 = n0 A tr := by
  rw [ctx0_eq A cb tr cs hlen]; unfold prepCore; dsimp only
  rfl

/-- The prover's DEEP word. -/
theorem Bw_eq (hlen : cs.length = nMsg A tr) (m p : Nat) :
    Bw A cb tr cs m p = deepH A cb tr cs (ctx0 A cb tr cs) m (pt (n0 A tr) m p) := by
  unfold Bw
  rw [deepAt_hon A cb tr cs (honCtx_ctx0 A cb tr cs hlen) (ctx0_n0 A cb tr cs hlen)
    (ops := opAt A cb tr cs (p <<< (n0 A tr - m))) (y := p <<< (n0 A tr - m)) (fun k hk => rfl) m,
    Nat.shiftLeft_shiftRight]

end

end ZkFormal.Prover.Np.G
