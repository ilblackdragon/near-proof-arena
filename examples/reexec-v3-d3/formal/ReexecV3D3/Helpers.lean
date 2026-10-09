import ReexecV3D3.TrieQ
import ReexecV3D3.Parse

/-!
# Shared lemmas: sums of lengths, and the lockstep tactics (from the D2 normal-form handoff,
`examples/reexec-v3-d2/formal/ReexecV3D2/Normal.lean`)
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

set_option hygiene false in
/-- One lockstep step of `h` (the accepting run of `checkD2`), `hk` (the run of its
verbatim copy `keysD2`, whose auxiliary matchers are different constants, so results are
matched by definitional unification) and the goal (`checkD2` on the normal form). -/
macro "lstep3" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _;
     obtain ⟨_, ha, h⟩ := bind_ok h; obtain ⟨_, hb, hk⟩ := bind_ok hk;
     cases (ha.symm.trans hb); rw [ha, ok_bind];
     (try dsimp only at h); (try dsimp only at hk); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _));
     split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (rename_i heq; split at hk <;> (rename_i heq2; first
          | (cases (heq.symm.trans heq2); done)
          | (cases (heq.symm.trans heq2);
             (try dsimp only at h); (try dsimp only at hk); (try dsimp only))))))

set_option hygiene false in
/-- Lockstep of `h` and the goal only. -/
macro "lstep2" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h; rw [ha, ok_bind];
     (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _)); split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (obtain ⟨_, ht, _⟩ := bind_ok h;
         simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at ht; done)
      | (cases h; done)
      | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
      | (guard_hyp h :~ (bind (m := Except String) _ _) = _; (try dsimp only at h); (try dsimp only))))

set_option hygiene false in
/-- Lockstep of `h` and the goal when their auxiliary matchers differ (or coincide). -/
macro "lstep2m" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h;
     rw [ha, ok_bind]; (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _));
     split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (rename_i heq; split <;> (rename_i heq2; first
          | (cases (heq.symm.trans heq2); done)
          | (cases (heq.symm.trans heq2); (try dsimp only at h); (try dsimp only))))))

theorem foldl_add_shift (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

theorem sum_le_of_nodup_subset : ∀ (l m : List Bytes), l.Nodup → (∀ x ∈ l, x ∈ m) →
    (l.map List.length).foldl (· + ·) 0 ≤ (m.map List.length).foldl (· + ·) 0
  | [], m, _, _ => by simp
  | a :: l, m, hn, hs => by
    rw [List.nodup_cons] at hn
    have ham : a ∈ m := hs a List.mem_cons_self
    have hp := List.perm_cons_erase ham
    have hsub : ∀ x ∈ l, x ∈ m.erase a := by
      intro x hx
      have hxm := hs x (List.mem_cons_of_mem _ hx)
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr hxm
    have ih := sum_le_of_nodup_subset l (m.erase a) hn.2 hsub
    have hm : (m.map List.length).foldl (· + ·) 0 = a.length + ((m.erase a).map List.length).foldl (· + ·) 0 := by
      rw [(hp.map List.length).foldl_eq' (fun _ _ _ _ _ => by omega) 0]
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_add_shift _ (0 + a.length)]; omega
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_shift _ (0 + a.length), hm]; omega

theorem sum_normValsH_le (vals q : List Bytes) :
    ((normValsH vals q).map List.length).foldl (· + ·) 0 ≤ (vals.map List.length).foldl (· + ·) 0 :=
  sum_le_of_nodup_subset _ _ (normValsH_nodup vals q) (fun _ hx => mem_normValsH hx)

end ReexecV3D3
