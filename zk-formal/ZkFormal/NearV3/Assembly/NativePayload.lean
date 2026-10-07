import ZkFormal.NearV3.Assembly.NativeWitnessSize

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

private theorem weight_erase (weight : Bytes → Nat) {x : Bytes} :
    ∀ {ws : List Bytes}, x ∈ ws →
      (ws.map weight).sum = weight x + ((ws.erase x).map weight).sum
  | [], h => by simp at h
  | y :: ys, h => by
    by_cases e : y = x
    · subst e; simp
    · have hx : x ∈ ys := by simpa [List.mem_cons, Ne.symm e] using h
      simp only [List.map_cons,List.sum_cons,List.erase_cons,beq_iff_eq,e,↓reduceIte]
      rw [weight_erase weight hx]; omega

theorem weighted_nodup_subset (weight : Bytes → Nat) : ∀ (xs ws : List Bytes), xs.Nodup →
    (∀ b ∈ xs, b ∈ ws) → (xs.map weight).sum ≤ (ws.map weight).sum
  | [], ws, _, _ => by simp
  | x :: xs, ws, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ ws := hs x (by simp)
    have ih := weighted_nodup_subset weight xs (ws.erase x) hn.2 (fun y hy => by
      have hyx : y ≠ x := fun e => hn.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hyx).2 (hs y (by simp [hy])))
    rw [weight_erase weight hx]
    simp only [List.map_cons,List.sum_cons]
    omega

theorem normalStore_payload {ws : List Bytes} {t : PTrie}
    (ht : Stored (mkStore ws) t) :
    ((normalStore t).map List.length).sum ≤ (ws.map List.length).sum := by
  apply weighted_nodup_subset List.length _ _ (eraseDups_nodup _)
  intro b hb
  exact (storeGet_some (normalStore_found ht b hb)).2

theorem nativeExecutionViews_main_payload {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3}
    (hm : m.NativeValid k w)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    (((nativeExecutionViews k w m steps).store 0).map List.length).foldl (· + ·) 0 ≤ 3000000 := by
  have hs : (nativeExecutionViews k w m steps).store 0 = normalStore m.pre := by
    change (traceStoreViews (runtimePairs m steps)).store 0 = _
    rw [traceStoreViews_store,runtimePairs_pre]
    exact forestStoreViews_store hf hc rfl
  rw [hs,hm.pre]
  have h := normalStore_payload (built_spec w.main.values trieFuel k.slotB2.prevStateRoot
    (mainKeys (appliedReceipts k w) m.bufferedShards) hm.root_length).2.2.1
  have hb := hm.storeBytes
  simpa only [foldl_add_sum,Nat.zero_add,partialTrie] using Nat.le_trans h (by
    simpa only [foldl_add_sum,Nat.zero_add] using hb)

end ZkFormal.NearV3.Assembly
