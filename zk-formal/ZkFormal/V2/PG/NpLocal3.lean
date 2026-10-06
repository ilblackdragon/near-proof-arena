import ZkFormal.V2.PG.NpFold

/-!
# ZkFormal.V2.PG.NpLocal3 (P2 copy of `Prover.NpLocal3` at `dp = pg g`) — the verifier's context fields on the honest transcript
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

structure CtxFacts (c : Ctx Fp8) : Prop where
  n0 : c.n0 = n0 A tr
  ell : c.ℓ = ell A tr
  commits : c.commits = commits A tr
  betas : c.betas = betaL A tr cs
  gammas : c.gammas = gammaL A tr cs
  fp : c.finalPoly = finalPoly A cb tr cs
  ok : c.ok = true

theorem ctxFacts (hlen : cs.length = nMsg A tr) : CtxFacts A cb tr cs ((Vd A).prep (honT A cb tr cs).erase) := by
  rw [prep_hon A cb tr cs hlen]
  have hn := nMsg_eq A tr
  have hdrop : (cs.drop 4).drop (batchRounds (layout A dp (hdr A tr))) = cs.drop (4 + nB A tr) := by
    rw [List.drop_drop]; rfl
  unfold prepCore
  dsimp only
  rw [show oodC A cb tr cs = oodAll A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs) from rfl, splitOod_hon]
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · rw [hdrop]; rfl
  · rw [hdrop]; rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by simp [hlen, hn, nB, kinds]; omega, rfl⟩, finalsAll_length A cb tr _ _⟩,
      oodAll_length A cb tr _ _ _ _⟩

theorem gammaL_none {i : Nat} (h : rollInAt A dp (hdr A tr) i = false) : (gammaL A tr cs).lookup i = none := by
  apply lookup_none_of_not_mem
  intro hm
  unfold gammaL friCs at hm
  simp only [List.map_map, List.mem_map, List.mem_filter, Function.comp] at hm
  obtain ⟨⟨⟨b, k⟩, v⟩, ⟨hz, hb⟩, he⟩ := hm
  simp only at hb he
  subst hb; subst he
  have := roll_of_mem_kinds A tr (List.of_mem_zip hz).1
  rw [h] at this; cases this

theorem rollIn_word {c : Ctx Fp8} (hf : CtxFacts A cb tr cs c) (op : List (List (List Fp))) (x : Nat)
    (deep : ∀ m, deepAt (F := Fp) c op m x = Bw A cb tr cs m (x >>> (n0 A tr - m)))
    (i : Nat) (hi : i + 1 ≤ n0 A tr) :
    (match c.gammas.lookup (i + 1) with
      | some γ => preW A cb tr cs i (x >>> (i + 1)) + γ * deepAt (F := Fp) c op (c.n0 - (i + 1)) x
      | none => preW A cb tr cs i (x >>> (i + 1))) = word A cb tr cs (i + 1) (x >>> (i + 1)) := by
  rw [word_succ, hf.gammas, hf.n0, deep, show n0 A tr - (n0 A tr - (i + 1)) = i + 1 by omega]
  cases (gammaL A tr cs).lookup (i + 1) <;> rfl

end

end ZkFormal.V2.PG
