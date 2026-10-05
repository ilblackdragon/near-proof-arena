import ZkFormal.Near.Link.WalkSpec
import ZkFormal.Near.Spec.CompleteAcct

/-!
# ZkFormal.Near.Link.Walks — `walks_ok : WalksStmt`

The walk of receipt `r` (`walk_of`) uses provided edges only
(`edge_provided`), each a spec step (`edge_walk`); chaining them gives the
spec walk of the receiver's account key to the receipt's slot.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem nibbles_toBytes : ∀ (v : List Nat), Bytes8 v →
    nibbles (toBytes v) = v.flatMap fun ch => [ch / 16, ch % 16]
  | [], _ => rfl
  | a :: v, hb => by
    have ha := hb a (by simp)
    simp only [toBytes, List.map_cons, nibbles, List.flatMap_cons]
    have e := toNat_ofNat_byte ha
    rw [e]
    have := nibbles_toBytes v (fun y hy => hb y (by simp [hy]))
    simp only [toBytes] at this
    rw [this]; rfl

theorem keySyms_eq (x : RcptV) (hb : Bytes8 x.v) :
    x.keySyms = accountKeyPath (toBytes x.v) ++ [SYM_END] := by
  simp only [RcptV.keySyms, accountKeyPath, nibbles]
  rw [nibbles_toBytes x.v hb]
  rfl

theorem edge_getD_of {e e' : Msg} (h5 : e.length = 5) (h5' : e'.length = 5) (h : e.drop 3 = e'.take 2) :
    e.getD 3 0 = e'.getD 0 0 ∧ e.getD 4 0 = e'.getD 1 0 := by
  match e, e', h5, h5' with
  | [a0, a1, a2, a3, a4], [b0, b1, b2, b3, b4], _, _ =>
    simp only [List.drop, List.take, List.cons.injEq] at h
    exact ⟨h.1, h.2.1⟩

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem walk_to {r : Nat} (hr : r < rs.length) :
    WalkTo (vs.map (·.v.toRec)) (accountKeyPath (toBytes rs[r].v)) rs[r].kslot := by
  obtain ⟨w, hw, -, hlen, hsym, hfin⟩ := walk_of h hr
  obtain ⟨_, _, _, wf⟩ := rcpt_wf_at h hr
  have hvb : Bytes8 rs[r].v := wf.ids.2.2.2.2.1
  have hks := keySyms_eq rs[r] hvb
  have hkplt := Prune.accountKeyPath_lt (toBytes rs[r].v)
  have hkpl : 2 ≤ (accountKeyPath (toBytes rs[r].v)).length := by
    rw [Prune.accountKeyPath_length]; omega
  generalize accountKeyPath (toBytes rs[r].v) = kp at hks hkplt hkpl ⊢
  have hK : rs[r].keySyms.length = kp.length + 1 := by rw [hks]; simp
  -- each edge of the walk is a spec edge
  have hok : ∀ t, t < w.steps.length → EdgeOk vs (w.edge t) ∧ (w.edge t).length = 5 := by
    intro t ht
    have hst : w.steps[t] ∈ w.steps := List.getElem_mem ht
    obtain ⟨n, hn, he⟩ := edge_provided h hw hst
    have he' : w.edge t = w.steps[t].1 := by
      simp [WalkV.edge, List.getD_eq_getElem?_getD, ht]
    rw [he']
    exact ⟨edge_walk h hn he, ((h.walk.steps w hw).2.1 _ hst).1⟩
  have hchain : ∀ t, t + 1 < w.steps.length →
      (w.edge t).getD 3 0 = (w.edge (t + 1)).getD 0 0 ∧ (w.edge t).getD 4 0 = (w.edge (t + 1)).getD 1 0 :=
    fun t ht => edge_getD_of (hok t (by omega)).2 (hok (t + 1) ht).2 (h.walk.chain w hw t ht)
  -- start edge
  have hstart := h.walk.start w hw
  have hs2 : (w.edge 0).getD 2 0 = SYM_START := by
    have h5 := (hok 0 (by omega)).2
    generalize w.edge 0 = e at hstart h5
    match e, h5 with
    | [a0, a1, a2, a3, a4], _ => simp only [List.take, List.cons.injEq] at hstart; exact hstart.2.2.1
  obtain ⟨h0, -, -, hr3, hr4⟩ := (hok 0 (by omega)).1.1 hs2
  -- the walk prefix
  have hpre : ∀ m, m ≤ kp.length → Walk (vs.map (·.v.toRec)) (0, 0) (kp.take m)
      ((w.edge (m + 1)).getD 0 0, (w.edge (m + 1)).getD 1 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨c1, c2⟩ := hchain 0 (by omega)
      rw [List.take_zero, ← c1, ← c2, hr3, hr4]
      exact eps_chain' h h0
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hsm : (w.edge (m + 1)).getD 2 0 = kp[m] := by
        rw [hsym m (by omega), hks, getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]
      have hx : kp[m] < 16 := hkplt _ (List.getElem_mem (by omega))
      have hstep := (hok (m + 1) (by omega)).1.2.1 (by rw [hsm]; exact hx)
      rw [hsm] at hstep
      obtain ⟨c1, c2⟩ := hchain (m + 1) (by omega)
      rw [c1, c2] at hstep
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
      exact walk_append ih' hstep
  have hall := hpre kp.length (Nat.le_refl _)
  rw [List.take_length] at hall
  -- the END edge
  have hsK : (w.edge (kp.length + 1)).getD 2 0 = SYM_END := by
    rw [hsym kp.length (by omega), hks, getD_eq_getElem _ _ (by simp),
      List.getElem_append_right (by simp)]
    simp
  obtain ⟨hz, hend⟩ := (hok (kp.length + 1) (by omega)).1.2.2 hsK
  have hf' : (w.edge (kp.length + 1)).getD 3 0 = rs[r].kslot := by
    rw [show kp.length + 1 = rs[r].keySyms.length from hK.symm]; exact hfin
  rw [hz, hf'] at hend
  exact ⟨_, hall, hend⟩

end Hyp

theorem walks_ok : WalksStmt := by
  intro c vs ws rs as mv ids shaS shaR h r hr
  have hlen : (linkExt vs as rs).rs.length = rs.length := by simp [linkExt]
  rw [hlen] at hr
  have := walk_to h hr
  rw [rc_eq hr]
  have hs : (linkExt vs as rs).slot r = rs[r].kslot := by
    simp [linkExt, List.getD_eq_getElem?_getD, hr]
  rw [hs]
  exact this

end Link

end ZkFormal.Near
