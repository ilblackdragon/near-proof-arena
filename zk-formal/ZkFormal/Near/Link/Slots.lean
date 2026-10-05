import ZkFormal.Near.Link.ListAux

/-!
# ZkFormal.Near.Link.Slots — node count bound and the `VSLOT` bijection

* `vs_length_le` — at most `3·10^6` node segments (each serializes to ≥ 1 byte);
* `vslot` — the `acct` slots are distinct and are exactly the touched nodes;
* `acctOf_eq` — hence `acctOf as a.k = some a`.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem ser_length_pos (v : NodeV) (post : Bool) : 1 ≤ (v.ser post).length := by
  cases v with
  | leaf => simp [NodeV.ser]
  | ext => simp [NodeV.ser]
  | branch v => cases v <;> simp [NodeV.ser]

theorem vs_length_le {vs : List NodeS} (hN : NodeWf vs) : vs.length ≤ 3000000 :=
  Nat.le_trans (length_le_sum _ vs (fun s _ => Nat.le_trans (ser_length_pos s.v false)
    (Nat.le_add_right _ _))) hN.size

theorem vs_length_lt {vs : List NodeS} (hN : NodeWf vs) : 16 * vs.length + 16 < P := by
  have := vs_length_le hN; unfold P; omega

theorem acctOf_eq {as : List AcctV} (hnd : (as.map (·.k)).Nodup) {a : AcctV} (ha : a ∈ as) :
    acctOf as a.k = some a := by
  induction as with
  | nil => cases ha
  | cons b as ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [acctOf, List.find?_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · have hne : b.k ≠ a.k := fun he => hnd.1 ⟨a, ha, he.symm⟩
      have : (b.k == a.k) = false := by simpa using hne
      rw [this]; exact ih hnd.2 ha

theorem mem_vslot_recvs {vs : List NodeS} {pub : List Fp} {m : Msg} :
    m ∈ nodeRecvs vs pub B_VSLOT ↔ ∃ n, ∃ h : n < vs.length, vs[n].v.touched = true ∧ m = [n] := by
  simp only [nodeRecvs, B_VSLOT, B_DIGEST, B_PARENT]
  simp only [show (3:Nat) ≠ 1 from by decide, show (3:Nat) ≠ 2 from by decide, if_false,
    if_true, List.mem_filterMap]
  constructor
  · rintro ⟨⟨s, n⟩, hm, he⟩
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hm
    by_cases ht : vs[n].v.touched = true
    · simp [ht] at he; exact ⟨n, hn, ht, he.symm⟩
    · simp [ht] at he
  · rintro ⟨n, hn, ht, rfl⟩
    exact ⟨(vs[n], n), mem_zip_range.mpr ⟨hn, rfl⟩, by simp [ht]⟩

theorem nodup_vslot_recvs {vs : List NodeS} {pub : List Fp} : (nodeRecvs vs pub B_VSLOT).Nodup := by
  have : nodeRecvs vs pub B_VSLOT =
      (((vs.zip (List.range vs.length)).filter (fun x => x.1.v.touched)).map Prod.snd).map
        (fun n => [n]) := by
    simp only [nodeRecvs, B_VSLOT, B_DIGEST, B_PARENT]
    simp only [show (3:Nat) ≠ 1 from by decide, show (3:Nat) ≠ 2 from by decide, if_false,
      if_true, List.map_map]
    exact filterMap_ite (fun x : NodeS × Nat => x.1.v.touched) (fun x => [x.2]) _
  rw [this]
  exact nodup_map_of_inj_on (fun a _ b _ h => by simpa using h) (nodup_filter_zip_range _ _)

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

omit h in
theorem acctSends_vslot : acctSends as B_VSLOT = as.map fun a => [a.k] := by
  simp [acctSends, B_VSLOT, B_BYTES, B_MEM]

/-- **`VSLOT`**: the `acct` slots are distinct and are exactly the touched nodes. -/
theorem vslot :
    (as.map (·.k)).Nodup ∧ (∀ a ∈ as, ∃ hk : a.k < vs.length, vs[a.k].v.touched = true) ∧
    (∀ n (hn : n < vs.length), vs[n].v.touched = true → ∃ a ∈ as, a.k = n) := by
  have hp := perm h (b := B_VSLOT) (by decide) (by decide)
  rw [nearSends_vslot, nearRecvs_vslot, acctSends_vslot] at hp
  have hlt := vs_length_lt h.node
  have hR : ∀ y ∈ nodeRecvs vs (publicOf c) B_VSLOT, Canon y := by
    intro y hy; obtain ⟨n, hn, -, rfl⟩ := mem_vslot_recvs.mp hy
    intro x hx; simp at hx; omega
  have hS : ∀ a ∈ as, Canon [a.k] := by
    intro a ha x hx; simp at hx; subst hx; exact (h.acct.len a ha).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ((nodeRecvs vs (publicOf c) B_VSLOT).map Msg.toFp).Nodup :=
      nodup_map_of_inj_on (fun a ha b hb he => toFp_inj (hR a ha) (hR b hb) he) nodup_vslot_recvs
    have h2 := hp.nodup_iff.mpr h1
    rw [List.map_map] at h2
    exact nodup_of_map (f := fun k => Msg.toFp [k]) (by rw [List.map_map]; exact h2)
  · intro a ha
    have : Msg.toFp [a.k] ∈ (as.map fun a => [a.k]).map Msg.toFp :=
      List.mem_map.mpr ⟨[a.k], List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := List.mem_map.mp (hp.mem_iff.mp this)
    obtain ⟨n, hn, ht, rfl⟩ := mem_vslot_recvs.mp hy
    have := toFp_inj (hR _ hy) (hS a ha) he
    simp only [List.cons.injEq, and_true] at this; subst this
    exact ⟨hn, ht⟩
  · intro n hn ht
    have hy : [n] ∈ nodeRecvs vs (publicOf c) B_VSLOT := mem_vslot_recvs.mpr ⟨n, hn, ht, rfl⟩
    obtain ⟨y, hy', he⟩ := List.mem_map.mp (hp.mem_iff.mpr (List.mem_map.mpr ⟨_, hy, rfl⟩))
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy'
    have := toFp_inj (hS a ha) (hR _ hy) he
    simp only [List.cons.injEq, and_true] at this
    exact ⟨a, ha, this⟩

end Hyp

end Link

end ZkFormal.Near
