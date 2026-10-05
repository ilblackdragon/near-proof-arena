import ZkFormal.Udr.RS

/-!
# ZkFormal.Udr.Deep — DEEP quotients and multilinear batching (UDR)

* `deep_close`: if the interleaved DEEP word `(f_j − v_j)/(x − z_j)` is
  `e`-close to `RS[D']`, then `f` is `e`-close to `RS[D'+1]` through
  polynomials `P_j` with `P_j(z_j) = v_j` (same agreement set).
* `deep_value`: hence, if `f` is `e`-close to *any* RS codeword `p*`
  (`2e < n − D'`), the claimed values are right: `p*_j(z_j) = v_j`.
  Contrapositive (**DEEP farness**): a wrong claimed value makes the DEEP
  word far.
* `batch_close`: one multilinear batching round `W' = W_even + r·W_odd`
  (columns paired `2c, 2c+1`) preserves closeness *backwards* when `r`
  satisfies the strong line conclusion; `batch_chain` iterates it.
-/

namespace ZkFormal.Udr

open ArenaCore.Security Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- `v + (X − z)·g` as a polynomial of length `D' + 1`. -/
theorem deep_poly (D' : Nat) (g : Nat → K) (v z : K) :
    ∃ P : Nat → K, ∀ x, ev (D' + 1) P x = v + (x - z) * ev D' g x := by
  have h1 : IsPoly (D' + 1) (fun x => x * ev D' g x) := (IsPoly.of_ev D' g).mulX
  have h2 : IsPoly (D' + 1) (fun x => (-z) * ev D' g x) := ((IsPoly.of_ev D' g).smul (-z)).mono (by omega)
  have h3 : IsPoly (D' + 1) (fun _ => v) := (IsPoly.const v).mono (by omega)
  obtain ⟨P, hP⟩ := (h3.add (h1.add h2))
  exact ⟨P, fun x => by rw [← hP x]; grind⟩

/-- The interleaved DEEP word. -/
def deepW {J : Type} (xs : Nat → K) (f : Word J K) (z v : J → K) : Word J K :=
  fun i j => (f i j - v j) * (xs i - z j)⁻¹

/-- **DEEP closeness transfer.** -/
theorem deep_close {J : Type} {xs : Nat → K} {n D' e : Nat} (hD : D' ≤ n) (hD1 : D' + 1 ≤ n)
    (hxs : Distinct xs n) (f : Word J K) (z v : J → K) (hz : ∀ j i, i < n → xs i ≠ z j)
    (hq : Good (rsInterleaved xs n D' hD hxs J) e (deepW xs f z v) (fun _ _ => 0) 0) :
    ∃ P : J → Nat → K, (∀ j, ev (D' + 1) (P j) (z j) = v j) ∧
      dist n f (fun i j => ev (D' + 1) (P j) (xs i)) ≤ e := by
  classical
  obtain ⟨w, hw, hd⟩ := hq
  have hg : ∀ j, ∃ g : Nat → K, ∀ i, i < n → w i j = ev D' g (xs i) := fun j => by
    obtain ⟨g, hg⟩ := hw j; exact ⟨g, fun i hi => hg i hi⟩
  let g : J → Nat → K := fun j => Classical.choose (hg j)
  have hgs : ∀ j i, i < n → w i j = ev D' (g j) (xs i) := fun j => Classical.choose_spec (hg j)
  have hP : ∀ j, ∃ P : Nat → K, ∀ x, ev (D' + 1) P x = v j + (x - z j) * ev D' (g j) x :=
    fun j => deep_poly D' (g j) (v j) (z j)
  let P : J → Nat → K := fun j => Classical.choose (hP j)
  have hPs : ∀ j x, ev (D' + 1) (P j) x = v j + (x - z j) * ev D' (g j) x :=
    fun j => Classical.choose_spec (hP j)
  refine ⟨P, fun j => by rw [hPs]; grind, Nat.le_trans (dist_mono ?_) hd⟩
  intro i hi hne heq
  apply hne
  funext j
  have e1 := congrFun heq j
  simp only [line, deepW] at e1
  rw [hPs, ← hgs j i hi]
  have hzi : xs i - z j ≠ 0 := fun h => hz j i hi (by grind)
  have hinv := Field.mul_inv_cancel hzi
  have : (f i j - v j) * (xs i - z j)⁻¹ = w i j := by rw [← e1]; grind
  rw [← this]
  grind

/-- **Claimed values are right** if the DEEP word is close and `f` is close to
some RS codeword (unique decoding). -/
theorem deep_value {J : Type} {xs : Nat → K} {n D' e : Nat} (hD : D' ≤ n) (hD1 : D' + 1 ≤ n)
    (hxs : Distinct xs n) (he : 2 * e < n - D') (f : Word J K) (z v : J → K)
    (hz : ∀ j i, i < n → xs i ≠ z j)
    (hq : Good (rsInterleaved xs n D' hD hxs J) e (deepW xs f z v) (fun _ _ => 0) 0)
    (p : J → Nat → K) (hp : dist n f (fun i j => ev (D' + 1) (p j) (xs i)) ≤ e) :
    ∀ j, ev (D' + 1) (p j) (z j) = v j := by
  obtain ⟨P, hPz, hPd⟩ := deep_close hD hD1 hxs f z v hz hq
  let C := rsInterleaved xs n (D' + 1) hD1 hxs J
  have hmem : ∀ q : J → Nat → K, C.mem (fun i j => ev (D' + 1) (q j) (xs i)) :=
    fun q j => ⟨q j, fun _ _ => rfl⟩
  have hu := C.unique (e := e) (by omega) (hmem P) (hmem p) hPd hp
  intro j
  rw [← hPz j]
  refine (ev_eq_of_agree hxs (p j) (P j) (fun _ => True) ?_ (fun i hi _ => ?_) (z j))
  · have := count_add_count_not (List.range n) (fun _ : Nat => True)
    rw [List.length_range] at this
    have h0 : count (List.range n) (fun _ : Nat => ¬ True) = 0 := by
      rw [show (fun _ : Nat => ¬ True) = fun _ => False from
        funext fun _ => propext ⟨fun h => h trivial, False.elim⟩, count_const]
      simp
    omega
  · exact (congrFun (hu i hi) j).symm

/-! ## Multilinear batching -/

/-- Even / odd column halves (columns indexed by `Nat`). -/
def evenCols (W : Word Nat K) : Word Nat K := fun i c => W i (2 * c)
def oddCols (W : Word Nat K) : Word Nat K := fun i c => W i (2 * c + 1)

/-- One batching round. -/
def batchStep (W : Word Nat K) (r : K) : Word Nat K := line (evenCols W) (oddCols W) r

/-- **One round backwards**: if the batched word is `e`-close and `r` satisfies
the strong line conclusion, the input word is `e`-close. -/
theorem batch_close {xs : Nat → K} {n D e : Nat} (hD : D ≤ n) (hxs : Distinct xs n)
    (W : Word Nat K) (r : K)
    (hs : Strong (rsInterleaved xs n D hD hxs Nat) e (evenCols W) (oddCols W) r)
    (hc : Good (rsInterleaved xs n D hD hxs Nat) e (batchStep W r) (fun _ _ => 0) 0) :
    Good (rsInterleaved xs n D hD hxs Nat) e W (fun _ _ => 0) 0 := by
  classical
  obtain ⟨w, hw, hd⟩ := hc
  have hd' : dist n (line (evenCols W) (oddCols W) r) w ≤ e := by
    refine Nat.le_trans (dist_mono fun i _ h e' => h ?_) hd
    rw [← e']; funext c; simp only [line, batchStep]; grind
  obtain ⟨v0, v1, hv0, hv1, hagree⟩ := hs w hw hd'
  let V : Word Nat K := fun i c => if c % 2 = 0 then v0 i (c / 2) else v1 i (c / 2)
  refine ⟨V, fun c => ?_, Nat.le_trans (dist_mono fun i hi hne heq => hne ?_) hd⟩
  · by_cases hc : c % 2 = 0
    · obtain ⟨p, hp⟩ := hv0 (c / 2)
      exact ⟨p, fun i hi => by simp only [V, hc, ite_true]; exact hp i hi⟩
    · obtain ⟨p, hp⟩ := hv1 (c / 2)
      exact ⟨p, fun i hi => by simp only [V, hc, ite_false]; exact hp i hi⟩
  · have hl : line (evenCols W) (oddCols W) r i = w i := by
      rw [← heq]; funext c; simp only [line, batchStep]; grind
    obtain ⟨h0, h1⟩ := hagree i hi hl
    funext c
    simp only [line]
    have hW : W i c = V i c := by
      by_cases hc : c % 2 = 0
      · have := congrFun h0 (c / 2)
        simp only [evenCols] at this
        simp only [V, hc, ite_true]
        rw [← this]; congr 1; omega
      · have := congrFun h1 (c / 2)
        simp only [oddCols] at this
        simp only [V, hc, ite_false]
        rw [← this]; congr 1; omega
    rw [hW]; grind

/-- Iterated batching: `W_k = batchStep^k W` with challenges `rs`. -/
def batchAll : List K → Word Nat K → Word Nat K
  | [], W => W
  | r :: rs, W => batchAll rs (batchStep W r)

/-- All rounds good, final word close ⇒ input word close. -/
theorem batch_chain {xs : Nat → K} {n D e : Nat} (hD : D ≤ n) (hxs : Distinct xs n) :
    ∀ (rs : List K) (W : Word Nat K),
      (∀ k (hk : k < rs.length),
        Strong (rsInterleaved xs n D hD hxs Nat) e (evenCols (batchAll (rs.take k) W))
          (oddCols (batchAll (rs.take k) W)) rs[k]) →
      Good (rsInterleaved xs n D hD hxs Nat) e (batchAll rs W) (fun _ _ => 0) 0 →
      Good (rsInterleaved xs n D hD hxs Nat) e W (fun _ _ => 0) 0
  | [], _, _, h => h
  | r :: rs, W, hs, h => by
    have ih := batch_chain hD hxs rs (batchStep W r) (fun k hk => by
      have := hs (k + 1) (by simp; omega)
      simpa [batchAll] using this) h
    exact batch_close hD hxs W r (hs 0 (by simp)) ih

end ZkFormal.Udr
