import ZkFormal.Near.Render.Proof.NodeTraffic2

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic3 — node traffic: DIGEST receives, PARENT sends

Both come from the hash windows only (first row of a `VH`/`CH` field), so the
rows' traffic is a function of the fields (`lay_flat`); the branch windows
are the present children (`branchWins_flat`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeTr
open NodeCells NodeGen NodeInfo

/-! ## Generic: rows → fields → children -/

theorem lay_flat {β : Type} (fs : List F) (hplen : Nat) (G : F → List β)
    (h : ∀ f ∈ fs, 1 ≤ f.len hplen ∨ G f = []) :
    (layout fs hplen).flatMap (fun fi => if fi.2 = 0 then G fi.1 else []) = fs.flatMap G := by
  unfold layout
  rw [List.flatMap_assoc]
  apply flatMap_congr'; intro f hf
  rw [List.flatMap_map]
  rcases h f hf with h1 | h1
  · rw [flatMap_first _ h1 _ (fun p hp => by simp [hp])]; simp
  · rw [flatMap_nil' (fun p _ => by split <;> simp [h1])]; exact h1.symm

theorem branchWins_flat {β : Type} (I : Info) (g : F → List β)
    (hg : ∀ k w l j w' l' j', g (.ch (kidWin I k w l j)) = g (.ch (kidWin I k w' l' j')))
    (kids : List Kid) :
    (branchWins I kids).flatMap g =
      (kids.filter (· ≠ .none)).flatMap (fun k => g (.ch (kidWin I k 0 false none))) := by
  unfold branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ∀ (Q : List (Kid × Nat)) (L : List Nat), Q.length ≤ L.length →
      ((Q.zip L).map fun x => F.ch (kidWin I x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2))).flatMap g =
        Q.flatMap fun x => g (.ch (kidWin I x.1 0 false none)) := by
    intro Q
    induction Q with
    | nil => intro L _; simp
    | cons q Q ih =>
      intro L hL
      cases L with
      | nil => simp at hL
      | cons l L =>
        simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons]
        rw [ih L (by simpa using hL), hg]
  rw [h1 P _ (by simp), ← hP]
  have h2 : ∀ (Q : List Kid) (L : List Nat), Q.length ≤ L.length →
      ((Q.zip L).filter (fun x => x.1 ≠ .none)).flatMap (fun x => g (.ch (kidWin I x.1 0 false none))) =
        (Q.filter (· ≠ .none)).flatMap (fun k => g (.ch (kidWin I k 0 false none))) := by
    intro Q
    induction Q with
    | nil => intro L _; simp
    | cons q Q ih =>
      intro L hL
      cases L with
      | nil => simp at hL
      | cons l L =>
        simp only [List.zip_cons_cons, List.filter_cons]
        split <;> simp_all
  exact h2 kids _ (by simp)

theorem kids_filter_flat {β : Type} (G : Kid → List β) (h0 : G .none = []) (kids : List Kid) :
    (kids.filter (· ≠ .none)).flatMap G = kids.flatMap G := by
  induction kids with
  | nil => rfl
  | cons k kids ih =>
    by_cases hk : k = .none
    · subst hk; simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
        List.flatMap_cons, h0, List.nil_append]; exact ih
    · simp only [List.filter_cons, ne_eq, hk, not_false_eq_true, decide_true, if_true, List.flatMap_cons]; rw [ih]

theorem kidIds_flat {β : Type} (G : Nat → List β) (kids : List Kid) :
    kids.flatMap (fun k => match k with | .node c => G c | _ => []) =
      (kids.filterMap fun k => match k with | .node c => some c | _ => none).flatMap G := by
  induction kids with
  | nil => rfl
  | cons k kids ih => cases k <;> simp [ih]

theorem range32 (l : List Nat) (h : l.length = 32) (k : Nat) :
    ((List.range 32).map fun i => Fp.ofNat (l.getD (k * 0 + i) 0)) = l.map Fp.ofNat := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp at h1; simp [List.getD_eq_getElem?_getD, h, h1]

theorem range32b (l : List Nat) (h : l.length = 32) :
    ((List.range 32).map fun a => Fp.ofNat (l[a]?.getD 0)) = l.map Fp.ofNat := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp at h1; simp [h, h1]

/-! ## DIGEST -/

def digSem (n : Nat) : F → List (List Nat)
  | .ch w => if w.look then [digMsg (msgId K_NPRE w.cid) w.clen w.pre, digMsg (msgId K_NPOST w.cid) w.clen w.post]
    else []
  | .vh w => if w.look then [digMsg (msgId K_VPRE n) 72 w.pre, digMsg (msgId K_VPOST n) 72 w.post] else []
  | _ => []

/-- Windows that are looked up are 32 bytes. -/
def WinOk (f : F) : Prop := ∀ w, f.win = some w → w.look = true → w.pre.length = 32 ∧ w.post.length = 32

theorem RT_digest_sem (I : Info) (u : Std.HashMap Edge Nat) (pub : List Fp) (r : NRec) (hw : WinOk r.f) :
    RT I u pub r B_DIGEST false =
      (if r.idx = 0 then (digSem r.n r.f).map Msg.toFp else []) ++
      (if r.n = 0 ∧ r.pos = 0 then [((K_NPRE : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_PRE + i) 0,
        ((K_NPOST : Nat) : Fp) :: V I u r 6 :: (List.range 32).map fun i => pub.getD (PV_POST + i) 0] else []) := by
  rw [RT_digest]
  congr 1
  have hreg : ∀ i, i ∈ List.range 32 → V I u r (72 + i) = Fp.ofNat ((match r.f.win with
      | some w => w.pre.getD (r.idx + i) 0 | none => 0)) := fun i hi => by
    simp only [V]; rw [rc_reg _ _ _ i (List.mem_range.1 hi)]; generalize r.f.win = x; cases x <;> rfl
  have hpreg : ∀ i, i ∈ List.range 32 → V I u r (104 + i) = Fp.ofNat ((match r.f.win with
      | some w => w.post.getD (r.idx + i) 0 | none => 0)) := fun i hi => by
    simp only [V]; rw [rc_preg _ _ _ i (List.mem_range.1 hi)]; generalize r.f.win = x; cases x <;> rfl
  rw [List.map_congr_left hreg, List.map_congr_left hpreg]
  obtain ⟨n, pos, f, idx, b, pb⟩ := r
  simp only at hw ⊢
  cases f with
  | ch w =>
    by_cases h : idx = 0 ∧ w.look = true
    · obtain ⟨rfl, hl⟩ := h
      obtain ⟨h1, h2⟩ := hw w rfl hl
      simp only [V, rc_gD, rc_dI, rc_dL, digOf, F.win, hl, and_self, if_true, digSem, ofNat1']
      simp [Msg.toFp, digMsg]
      refine ⟨range32b _ h1, ?_, range32b _ h2⟩
      rw [show msgId K_NPRE w.cid + 1 = msgId K_NPOST w.cid by simp only [msgId, K_NPRE, K_NPOST]; omega]
    · have : digOf ⟨n, pos, .ch w, idx, b, pb⟩ = none := by simp [digOf, h]
      simp only [V, rc_gD, this, ofNat0', fp_zero_ne_one, if_false, List.append_nil]
      by_cases h0 : idx = 0
      · have hl : w.look = false := by simpa [h0] using h
        simp [h0, digSem, hl]
      · simp [h0]
  | vh w =>
    by_cases h : idx = 0 ∧ w.look = true
    · obtain ⟨rfl, hl⟩ := h
      obtain ⟨h1, h2⟩ := hw w rfl hl
      simp only [V, rc_gD, rc_dI, rc_dL, digOf, F.win, hl, and_self, if_true, digSem, ofNat1']
      simp [Msg.toFp, digMsg]
      refine ⟨range32b _ h1, ?_, range32b _ h2⟩
      rw [show msgId K_VPRE n + 1 = msgId K_VPOST n by simp only [msgId, K_VPRE, K_VPOST]; omega]
    · have : digOf ⟨n, pos, .vh w, idx, b, pb⟩ = none := by simp [digOf, h]
      simp only [V, rc_gD, this, ofNat0', fp_zero_ne_one, if_false, List.append_nil]
      by_cases h0 : idx = 0
      · have hl : w.look = false := by simpa [h0] using h
        simp [h0, digSem, hl]
      · simp [h0]
  | _ => simp [V, rc_gD, digOf, ofNat0', digSem]

end NodeTr

end ZkFormal.Near.Render
