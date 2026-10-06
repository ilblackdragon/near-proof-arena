import NearSpecV3.ChunkValidationD2
import ReexecV3D3.CF
import ReexecV3D3.Size
import ReexecV3D3.CanonDefs

/-!
# Parser facts for the fixed ignored fields, and witness files

Concrete parses of the normal-form header fields (`zeros8`, `sig0`), header decomposition,
`trTail` (the part of `pTransition` after the block hash), `wrapW` (the witness file of a
state witness with no contract code) and the decoded witness of an accepting run.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3

theorem check_true (m : String) : NearSpecV3.check true m = .ok () := rfl

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-! ## Concrete facts, transported by context-freeness -/

theorem cfk {α : Type} {p : P α} (hp : CF p) {bs : Bytes} {v : α} {r : Bytes}
    (h : p bs = .ok (v, r)) : ∃ pre, bs = pre ++ r ∧ ∀ x, p (pre ++ x) = .ok (v, x) :=
  hp bs v r h

theorem pU64_zeros8 (w : String) (x : Bytes) : pU64 w (zeros8 ++ x) = .ok (0, x) := by
  have h : pU64 w (zeros8 ++ []) = .ok (0, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pU64 w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pTake8_zeros8 (w : String) (x : Bytes) : pTake 8 w (zeros8 ++ x) = .ok (zeros8, x) := by
  have h : pTake 8 w (zeros8 ++ []) = .ok (zeros8, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pTake 8 w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pSignature_sig0 (w : String) (x : Bytes) : pSignature w (sig0 ++ x) = .ok (sig0, x) := by
  have h : pSignature w (sig0 ++ []) = .ok (sig0, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pSignature w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pHash_any (w : String) (h x : Bytes) (hl : h.length = 32) : pHash w (h ++ x) = .ok (h, x) := by
  unfold pHash lift readHash
  rw [← hl, takeN_append]

theorem lift_readLE_length {n : Nat} {w : String} {bs r : Bytes} {v : Nat}
    (h : lift w (readLE n) bs = .ok (v, r)) : bs.length = n + r.length := by
  unfold lift at h
  split at h
  · rename_i r0 hr
    cases h
    simp only [readLE, Option.map_eq_some_iff] at hr
    obtain ⟨⟨h', t'⟩, e', he⟩ := hr
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact takeN_length e'
  · cases h

theorem pU64_split {w : String} {bs r : Bytes} {v : Nat} (h : pU64 w bs = .ok (v, r)) :
    ∃ H, bs = H ++ r ∧ H.length = 8 := by
  obtain ⟨H, hH, -⟩ := cfk (cf_pU64 w) h
  have := lift_readLE_length (n := 8) h
  refine ⟨H, hH, ?_⟩
  rw [hH, List.length_append] at this; omega

theorem pTake_split {n : Nat} {w : String} {bs v r : Bytes} (h : pTake n w bs = .ok (v, r)) :
    bs = v ++ r ∧ v.length = n := by
  unfold pTake lift at h
  split at h
  · rename_i r0 hr
    cases h
    obtain ⟨pre, h1, h2, h3⟩ := takeAcc_split hr
    simp at h3; subst h3; exact ⟨h1, h2⟩
  · cases h

theorem pSignature_split {w : String} {bs v r : Bytes} (h : pSignature w bs = .ok (v, r)) :
    ∃ S, bs = S ++ r ∧ 65 ≤ S.length := by
  obtain ⟨S, hS, -⟩ := cfk (cf_pSignature w) h
  refine ⟨S, hS, ?_⟩
  unfold pSignature at h
  obtain ⟨⟨t, m⟩, h1, h⟩ := bind_ok' h
  obtain ⟨T, hT, -⟩ := cfk (cf_pU8 _) h1
  have hT1 : T.length = 1 := by
    have := lift_readLE_length (n := 1) h1
    rw [hT, List.length_append] at this; omega
  dsimp only at h
  have hlen : ∀ n, n ≥ 64 → ∀ d m2, pTake n w m = .ok (d, m2) → m2 = r → 65 ≤ S.length := by
    intro n hn d m2 hd hm2
    obtain ⟨e1, e2⟩ := pTake_split hd
    subst hm2
    have hb : bs = T ++ (d ++ m2) := by rw [hT, e1]
    rw [hS, ← List.append_assoc] at hb
    have := List.append_cancel_right hb
    rw [this, List.length_append, hT1, e2]; omega
  rcases t with _ | _ | _ | t
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    dsimp only at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact hlen 64 (by omega) d m2 h2 h.2
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact hlen 65 (by omega) d m2 h2 h.2
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact hlen 3309 (by omega) d m2 h2 h.2
  · cases h

/-- Header decomposition: `bs = T ‖ I ‖ H ‖ S ‖ r` (tag, inner, `height_included`,
signature), and the canonical header `T ‖ I ‖ 0⁸ ‖ sig0` parses to the same value. -/
theorem hdr_split {bs ib r : Bytes} {ci : ChunkInner}
    (h : pChunkHeader bs = .ok ((ib, ci), r)) :
    ∃ T I H S, bs = T ++ (I ++ (H ++ (S ++ r))) ∧ H.length = 8 ∧ 65 ≤ S.length ∧
      (∀ x, pU8 "ShardChunkHeader tag" (T ++ x) = .ok (2, x)) ∧
      (∀ x, pChunkInner (I ++ x) = .ok (ci, x)) ∧
      (∀ x, pChunkHeader (T ++ (I ++ (zeros8 ++ (sig0 ++ x)))) = .ok ((ib, ci), x)) := by
  unfold pChunkHeader at h
  obtain ⟨⟨t, m1⟩, h1, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  · cases h
  · rename_i ht
    have ht2 : t = 2 := by simpa using ht
    subst ht2
    obtain ⟨⟨ci', m2⟩, h2, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨hv, m3⟩, h3, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨sg, m4⟩, h4, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hib, hci⟩, hr⟩ := h
    subst hci; subst hr
    obtain ⟨T, hT, kT⟩ := cfk (cf_pU8 _) h1
    obtain ⟨I, hI, kI⟩ := cfk cf_pChunkInner h2
    obtain ⟨H, hH, hH8⟩ := pU64_split h3
    obtain ⟨S, hS, hS65⟩ := pSignature_split h4
    have hib' : ib = I := by rw [← hib, hI, consumed_app]
    refine ⟨T, I, H, S, by rw [hT, hI, hH, hS], hH8, hS65, kT, kI, fun x => ?_⟩
    unfold pChunkHeader
    rw [kT]
    simp only [ok_bind]
    show (if ((2 : Nat) != 2) = true then _ else _) = _
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [kI]
    simp only [ok_bind]
    rw [consumed_app, pU64_zeros8, ok_bind, pSignature_sig0, ok_bind, hib']
    rfl

/-- The part of `pTransition` after the block hash, for a given block hash. -/
def trTail (bh : Bytes) : P Transition := fun bs => do
  let (t, bs) ← pU8 "PartialState tag" bs
  if t != 0 then throw "decode: PartialState tag"
  let (vals, bs) ← pVec "trie values" (pBytes "trie value") bs
  let (post, bs) ← pHash "post_state_root" bs
  pure (⟨bh, vals, post⟩, bs)

theorem cf_trTail (bh : Bytes) : CF (trTail bh) := by
  unfold trTail; have := cf_pVec "trie values" (cf_pBytes "trie value"); cf_auto

theorem pTransition_eq (bs : Bytes) :
    pTransition bs = (pHash "transition block_hash" bs >>= fun x => trTail x.1 x.2) := by
  unfold pTransition trTail
  rfl

/-! ## Witness files -/


end ReexecV3D3
