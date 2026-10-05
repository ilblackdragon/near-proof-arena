import ZkFormal.Udr.Np.Shape

/-!
# ZkFormal.Udr.Np.Frame — frame lemmas for the early rounds

The semantic objects of `Sem`/`Stage` read a transcript only through its
claim bytes, header, committed oracles, clear-text elements and challenges.
`OAgree k τ τ'`: same claim, same header, same first `k` oracles.  Under it,
every object built from the first `k` oracle kinds agrees.  Extensions
`τ.push m` / `τ.pushChal c` of a non-empty transcript agree with `τ` on all
earlier data.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- Same claim, header and first `k` oracles. -/
def OAgree (k : Nat) (τ τ' : PTn) : Prop :=
  τ.cb = τ'.cb ∧ τ.header? = τ'.header? ∧ ∀ i, i < k → oracleOf τ i = oracleOf τ' i

theorem OAgree.mono {k k' : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : k' ≤ k) : OAgree k' τ τ' :=
  ⟨h.1, h.2.1, fun i hi => h.2.2 i (by omega)⟩

section
variable (A : Air) (prm : Params)

theorem hdrOf_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) : hdrOf τ = hdrOf τ' := by
  unfold hdrOf; rw [h]

theorem layOf_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) : layOf A prm τ = layOf A prm τ' := by
  unfold layOf; rw [hdrOf_congr h]

theorem n0Of_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) : n0Of A prm τ = n0Of A prm τ' := by
  unfold n0Of; rw [hdrOf_congr h]

theorem tl_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) (t : Nat) :
    tl A prm τ t = tl A prm τ' t := by
  unfold tl; rw [layOf_congr A prm h]

variable {A prm}

theorem colVal_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') {d : Col} (hd : d.kind < k) :
    colVal τ d = colVal τ' d := by
  funext p; unfold colVal; rw [h.2.2 _ hd]

theorem colP_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') {d : Col} (hd : d.kind < k) :
    colP A prm τ d = colP A prm τ' d := by
  unfold colP
  rw [tl_congr A prm h.2.1, n0Of_congr A prm h.2.1, colVal_congr h hd]

theorem colAt_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') {d : Col} (hd : d.kind < k) :
    colAt A prm τ d = colAt A prm τ' d := by
  funext x; unfold colAt; rw [tl_congr A prm h.2.1, colP_congr h hd]

theorem mem_tableCols {L : TLayout} {t k : Nat} {d : Col} (hd : d ∈ tableCols L t k) :
    d.kind < max k 1 := by
  unfold tableCols at hd
  simp only [List.mem_append, List.mem_map, List.mem_range] at hd
  rcases hd with (⟨c, _, rfl⟩ | hd) | hd
  · show 0 < max k 1; omega
  · split at hd
    · simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨c, _, rfl⟩ := hd; show 1 < max k 1; omega
    · simp at hd
  · split at hd
    · simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨c, _, rfl⟩ := hd; show 2 < max k 1; omega
    · simp at hd

theorem mem_classCols {lay : List TLayout} {m k : Nat} {d : Col} (hd : d ∈ classCols lay m k) :
    d.kind < max k 1 := by
  unfold classCols at hd
  obtain ⟨⟨L, t⟩, _, hd⟩ := List.mem_flatMap.mp hd
  exact mem_tableCols hd

theorem classWord_congr {k k' : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : max k' 1 ≤ k) (m : Nat) :
    classWord A prm τ m k' = classWord A prm τ' m k' := by
  funext p j
  unfold classWord
  rw [layOf_congr A prm h.2.1]
  split
  · next d hd =>
    have := mem_classCols (List.mem_of_getElem? hd)
    rw [colVal_congr h (by omega)]
  · rfl

theorem allClose_congr {k k' : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : max k' 1 ≤ k) :
    AllClose A prm τ k' ↔ AllClose A prm τ' k' := by
  unfold AllClose
  rw [layOf_congr A prm h.2.1, n0Of_congr A prm h.2.1]
  simp only [classWord_congr h hk]

theorem decTrace_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) :
    decTrace A prm τ = decTrace A prm τ' := by
  have e : ∀ t c, colAt A prm τ ⟨t, 0, c⟩ = colAt A prm τ' ⟨t, 0, c⟩ := fun t c =>
    colAt_congr h (by show 0 < k; omega)
  simp only [decTrace, hdrOf_congr h.2.1, e]

theorem pubOf_congr {τ τ' : PTn} (h : τ.cb = τ'.cb) : pubOf Fp τ.cb = pubOf Fp τ'.cb := by rw [h]

theorem localFail_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) :
    LocalFail A prm τ ↔ LocalFail A prm τ' := by
  unfold LocalFail; rw [decTrace_congr h hk, h.1]

theorem busMsgs_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (s : Bool) :
    busMsgs A prm τ s = busMsgs A prm τ' s := by
  unfold busMsgs; rw [decTrace_congr h hk, h.1]

theorem fpDiffer_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (α : Fp8) :
    FpDiffer A prm τ α ↔ FpDiffer A prm τ' α := by
  unfold FpDiffer; rw [busMsgs_congr h hk, busMsgs_congr h hk]

theorem gpDiffer_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (α γ : Fp8) :
    GpDiffer A prm τ α γ ↔ GpDiffer A prm τ' α γ := by
  unfold GpDiffer; rw [busMsgs_congr h hk, busMsgs_congr h hk]

theorem polyEnv_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (t : Nat) (x : Fp8) :
    polyEnv A prm τ t x = polyEnv A prm τ' t x := by
  have e : ∀ c, colAt A prm τ ⟨t, 0, c⟩ = colAt A prm τ' ⟨t, 0, c⟩ := fun c =>
    colAt_congr h (by show 0 < k; omega)
  simp only [polyEnv, tl_congr A prm h.2.1, h.1, e]

theorem finsOf_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) (hf : finalsOf τ = finalsOf τ')
    (t : Nat) : finsOf A prm τ t = finsOf A prm τ' t := by
  unfold finsOf; rw [layOf_congr A prm h, tl_congr A prm h, hf]

theorem csAt_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 2 ≤ k)
    (hf : finalsOf τ = finalsOf τ') (t : Nat) (αfp γ x : Fp8) :
    csAt A prm τ t αfp γ x = csAt A prm τ' t αfp γ x := by
  unfold csAt
  rw [tl_congr A prm h.2.1, polyEnv_congr h (by omega), finsOf_congr h.2.1 hf]
  have e : ∀ a, colAt A prm τ ⟨t, 1, a⟩ = colAt A prm τ' ⟨t, 1, a⟩ := fun a =>
    colAt_congr h (by show 1 < k; omega)
  simp only [e]

theorem Ct_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 2 ≤ k)
    (hf : finalsOf τ = finalsOf τ') (t : Nat) (αfp γ αc x : Fp8) :
    Ct A prm τ t αfp γ αc x = Ct A prm τ' t αfp γ αc x := by
  unfold Ct; rw [csAt_congr h hk hf]

theorem Qt_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 3 ≤ k) (t : Nat) (x : Fp8) :
    Qt A prm τ t x = Qt A prm τ' t x := by
  unfold Qt
  rw [tl_congr A prm h.2.1]
  have e : ∀ a, colAt A prm τ ⟨t, 2, a⟩ = colAt A prm τ' ⟨t, 2, a⟩ := fun a =>
    colAt_congr h (by show 2 < k; omega)
  simp only [e]

theorem csFailH_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 2 ≤ k)
    (hf : finalsOf τ = finalsOf τ') (αfp γ : Fp8) :
    CsFailH A prm τ αfp γ ↔ CsFailH A prm τ' αfp γ := by
  unfold CsFailH
  simp only [tl_congr A prm h.2.1, csAt_congr h hk hf]

theorem busFinalsFail_congr {τ τ' : PTn} (h : τ.header? = τ'.header?)
    (hf : finalsOf τ = finalsOf τ') : BusFinalsFail A prm τ ↔ BusFinalsFail A prm τ' := by
  unfold BusFinalsFail; rw [layOf_congr A prm h, hf]

end

/-! ## Extensions -/

theorem oracles_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) :
    ∃ l, (τ.push m).oracles = τ.oracles ++ l :=
  ⟨_, by simp only [PT.push, PT.oracles, List.flatMap_append, List.flatMap_singleton]; rfl⟩

theorem oracles_pushChal (τ : PTn) (c : Fp8) : (τ.pushChal c).oracles = τ.oracles := by
  simp [PT.pushChal, PT.oracles, List.flatMap_append]

theorem chals_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) : (τ.push m).chals = τ.chals := by
  simp [PT.push, PT.chals, List.filterMap_append]

theorem chals_pushChal (τ : PTn) (c : Fp8) : (τ.pushChal c).chals = τ.chals ++ [c] := by
  simp [PT.pushChal, PT.chals, List.filterMap_append]

theorem elems_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) :
    ∃ l, (τ.push m).elems = τ.elems ++ l :=
  ⟨_, by simp only [PT.push, PT.elems, List.flatMap_append, List.flatMap_singleton]; rfl⟩

theorem elems_pushChal (τ : PTn) (c : Fp8) : (τ.pushChal c).elems = τ.elems := by
  simp [PT.pushChal, PT.elems, List.flatMap_append]

theorem oAgree_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) (h : τ.entries ≠ []) :
    OAgree τ.oracles.length (τ.push m) τ := by
  refine ⟨rfl, header?_push τ m h, fun i hi => ?_⟩
  unfold oracleOf
  obtain ⟨l, hl⟩ := oracles_push τ m
  rw [hl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

theorem oAgree_pushChal (τ : PTn) (c : Fp8) (h : τ.entries ≠ []) (k : Nat) :
    OAgree k (τ.pushChal c) τ := by
  refine ⟨rfl, header?_pushChal τ c h, fun i _ => ?_⟩
  unfold oracleOf; rw [oracles_pushChal]

theorem chals_getD_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) (k : Nat) :
    (τ.push m).chals.getD k 0 = τ.chals.getD k 0 := by rw [chals_push]

theorem chals_getD_pushChal (τ : PTn) (c : Fp8) (k : Nat) (hk : k < τ.chals.length) :
    (τ.pushChal c).chals.getD k 0 = τ.chals.getD k 0 := by
  rw [chals_pushChal, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hk]

theorem chals_getD_pushChal_last (τ : PTn) (c : Fp8) :
    (τ.pushChal c).chals.getD τ.chals.length 0 = c := by
  rw [chals_pushChal, List.getD_eq_getElem?_getD]; simp

theorem finalsOf_pushChal (τ : PTn) (c : Fp8) : finalsOf (τ.pushChal c) = finalsOf τ := by
  unfold finalsOf; rw [elems_pushChal]

theorem finalsOf_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) (h : τ.elems ≠ []) :
    finalsOf (τ.push m) = finalsOf τ := by
  unfold finalsOf
  obtain ⟨l, hl⟩ := elems_push τ m
  rw [hl]
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil h
  rw [he]; rfl

end ZkFormal.Udr.Np
