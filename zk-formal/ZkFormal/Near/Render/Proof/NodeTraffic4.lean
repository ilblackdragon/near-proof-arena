import ZkFormal.Near.Render.Proof.NodeTraffic3

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic4 — node traffic: DIGEST receives, PARENT sends (assembly)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeTr
open NodeCells NodeGen NodeInfo

theorem mem_layout {fs : List F} {hplen : Nat} {fi : F × Nat} (h : fi ∈ layout fs hplen) :
    fi.1 ∈ fs ∧ fi.2 < fi.1.len hplen := by
  simp only [layout, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨f, hf, i, hi, rfl⟩ := h
  exact ⟨hf, hi⟩

theorem lay_get_mem (I : Info) (n p : Nat) (hp : p < (NodeLay.layN I n).length) :
    ((NodeLay.layN I n).getD p default).1 ∈ fieldsOf I n (I.nodeAt n) ∧
      ((NodeLay.layN I n).getD p default).2 < ((NodeLay.layN I n).getD p default).1.len (hplenOf (I.nodeAt n)) := by
  apply mem_layout
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]; exact List.getElem_mem hp

theorem fields_len (I : Info) (n : Nat) (nr : NodeRec) :
    ∀ f ∈ fieldsOf I n nr, 1 ≤ f.len (hplenOf nr) ∨ f = .key := by
  intro f hf
  have hb : ∀ f ∈ branchWins I nr.kids, 1 ≤ f.len (hplenOf nr) := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; simp [F.len]
  cases nr with
  | leaf k v m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.len]
  | ext k kid m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.len]
  | branch v kids m =>
    cases v with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · simp [F.len]
      · simp [F.len]
      · exact .inl (hb f (by simpa [NodeRec.kids] using hf))
      · simp [F.len]
    | some sv =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · simp [F.len]
      · simp [F.len]
      · simp [F.len]
      · simp [F.len]
      · exact .inl (hb f (by simpa [NodeRec.kids] using hf))
      · simp [F.len]

theorem winOk_fields (I : Info) (n : Nat) (nr : NodeRec) : ∀ f ∈ fieldsOf I n nr, WinOk f := by
  have hk : ∀ k w l j, WinOk (.ch (kidWin I k w l j)) := by
    intro k w l j w' hw hl
    simp only [F.win, Option.some.injEq] at hw; subst hw
    cases k <;> simp_all [kidWin, Info.preDig, Info.postDig, shaN_len]
  have hv : ∀ v, WinOk (.vh (valWin I n v)) := by
    intro v w' hw hl
    simp only [F.win, Option.some.injEq] at hw; subst hw
    cases v <;> simp_all [valWin, shaN_len]
  have ho : ∀ f, f.win = none → WinOk f := fun f h w hw => by rw [h] at hw; cases hw
  intro f hf
  have hb : ∀ f ∈ branchWins I nr.kids, WinOk f := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; exact hk _ _ _ _
  cases nr with
  | leaf k v m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hv _ | exact ho _ rfl
  | ext k kid m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hk _ _ _ _ | exact ho _ rfl
  | branch v kids m =>
    cases v with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · exact ho _ rfl
      · exact ho _ rfl
      · exact hb f (by simpa [NodeRec.kids] using hf)
      · exact ho _ rfl
    | some sv =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · exact ho _ rfl
      · exact ho _ rfl
      · exact hv _
      · exact ho _ rfl
      · exact hb f (by simpa [NodeRec.kids] using hf)
      · exact ho _ rfl

/-- Rows of a node → its fields (traffic only on the first row of a field). -/
theorem rows_fields {β : Type} (I : Info) (n : Nat) (G : F → List β) (Rt : NRec → List β)
    (hRt : ∀ p, p < (NodeLay.layN I n).length → Rt (mkR I n p) =
      if ((NodeLay.layN I n).getD p default).2 = 0 then G ((NodeLay.layN I n).getD p default).1 else [])
    (hkey : G .key = []) :
    (nodeRecs I n).flatMap Rt = (fieldsOf I n (I.nodeAt n)).flatMap G := by
  rw [NodeLay.nodeRecs_eq, List.flatMap_map, flatMap_congr' (fun p hp => hRt p (List.mem_range.1 hp)),
    ← flatMap_getD default (NodeLay.layN I n) (fun fi => if fi.2 = 0 then G fi.1 else [])]
  exact lay_flat _ _ G (fun f hf => (fields_len I n _ f hf).imp_right fun h => by rw [h, hkey])

def tDig (n : Nat) (v : NodeV) : List (List Nat) :=
  match v.vwin with
  | some (pre, po) => [digMsg (msgId K_VPRE n) 72 pre, digMsg (msgId K_VPOST n) 72 po]
  | none => []

def kDig (x : Nat × Nat × Nat × List Nat × List Nat) : List (List Nat) :=
  [digMsg (msgId K_NPRE x.1) x.2.1 x.2.2.2.1, digMsg (msgId K_NPOST x.1) x.2.1 x.2.2.2.2]

theorem dig_node' (I : Info) (n : Nat) (nr : NodeRec) :
    ((fieldsOf I n nr).flatMap (digSem n)).Perm ((nodeVOf I n nr).revealed.flatMap kDig ++ tDig n (nodeVOf I n nr)) :=
  dig_node I n nr kDig (fun _ _ _ _ _ => rfl) (tDig n) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun v h => by simp [tDig, h])

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs

theorem tParentS : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_PARENT true).Perm
      ((nodeSends (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) B_PARENT).map Msg.toFp) := by
  simp only [nodeSends, B_BYTES, B_PARENT, Nat.reduceEqDiff, if_false, if_true, zipViews, info_N, List.flatMap_map,
    List.map_flatMap]
  apply List.Perm.of_eq
  apply flatMap_congr'; intro n hn
  rw [rows_fields (mkInfo c.1 e) n (fun f => (parSem ((mkInfo c.1 e).depth.getD n 0) f).map Msg.toFp) _
    (fun p hp => RT_parent_sem _ _ _ _) rfl, ← List.map_flatMap]
  simp only [Function.comp_apply, nodeViewOf]
  rw [par_node _ _ _ _ (fun x => [x.1, (mkInfo c.1 e).depth.getD n 0 + 1, x.2.1, x.2.2.1]) (fun _ _ _ _ _ => rfl),
    List.map_map]

theorem tDigest : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_DIGEST false).Perm
      ((nodeRecvs (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) (publicOf c) B_DIGEST).map Msg.toFp) := by
  have hN : 0 < e.ns.length := hg.shape.nonempty
  let roots : List (List Fp) :=
    [((K_NPRE : Nat) : Fp) :: Fp.ofNat ((mkInfo c.1 e).pre.getD 0 []).length ::
        (List.range 32).map fun i => (publicOf c).getD (PV_PRE + i) 0,
      ((K_NPOST : Nat) : Fp) :: Fp.ofNat ((mkInfo c.1 e).pre.getD 0 []).length ::
        (List.range 32).map fun i => (publicOf c).getD (PV_POST + i) 0]
  have hnode : ∀ n, n < e.ns.length → ((nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_DIGEST false).Perm
      (((fieldsOf (mkInfo c.1 e) n ((mkInfo c.1 e).nodeAt n)).flatMap (digSem n)).map Msg.toFp ++
        (if n = 0 then roots else [])) := by
    intro n hn
    have hrw : ∀ p, p < (NodeLay.layN (mkInfo c.1 e) n).length →
        RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) (mkR (mkInfo c.1 e) n p) B_DIGEST false =
        (if ((NodeLay.layN (mkInfo c.1 e) n).getD p default).2 = 0 then
          (digSem n ((NodeLay.layN (mkInfo c.1 e) n).getD p default).1).map Msg.toFp else []) ++
        (if p = 0 ∧ n = 0 then roots else []) := by
      intro p hp
      rw [RT_digest_sem _ _ _ _ (winOk_fields _ _ _ _ (lay_get_mem _ n p hp).1)]
      congr 1
      by_cases h : p = 0 ∧ n = 0
      · obtain ⟨rfl, rfl⟩ := h
        simp [roots, V, rc_len]
      · simp only [mkR]; rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h]
    have := rows_fields (mkInfo c.1 e) n (fun f => (digSem n f).map Msg.toFp)
      (fun r => if r.idx = 0 then (digSem r.n r.f).map Msg.toFp else []) (fun p hp => rfl) rfl
    rw [NodeLay.nodeRecs_eq, List.flatMap_map, flatMap_congr' (fun p hp => hrw p (List.mem_range.1 hp))]
    refine (perm_flatMap_append _ _ _).trans (List.Perm.append ?_ ?_)
    · rw [NodeLay.nodeRecs_eq, List.flatMap_map] at this
      rw [this, List.map_flatMap]
    · rw [flatMap_first _ (layN_pos _ n) _ (fun p hp => by simp [hp])]; simp
  refine (perm_flatMap_congr (fun n hn => hnode n (List.mem_range.1 hn))).trans ?_
  refine (perm_flatMap_append _ _ _).trans ?_
  have hroots : ((List.range e.ns.length).flatMap fun n => if n = 0 then roots else []) = roots := by
    obtain ⟨M, hM⟩ : ∃ M, e.ns.length = M + 1 := ⟨e.ns.length - 1, by omega⟩
    rw [hM, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]; simp
  rw [hroots]
  simp only [nodeRecvs, B_DIGEST, if_true, zipViews, info_N, List.flatMap_map, List.map_append]
  refine List.perm_append_comm.trans (List.Perm.append (List.Perm.of_eq ?_) ?_)
  · have h0 : (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))).headD default =
        nodeViewOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) 0 := by
      simp [nodeViewsOf, info_N]
      obtain ⟨M, hM⟩ : ∃ M, e.ns.length = M + 1 := ⟨e.ns.length - 1, by omega⟩
      rw [hM, List.range_succ_eq_map]; rfl
    rw [h0]
    simp only [nodeViewOf, info_nodeAt hN, view_pre hg hN (hs.keys _ (List.getElem_mem hN))]
    simp [roots, Msg.toFp, digMsg, pubNat, Fp.ofNat_toNat, natCast_eq, Function.comp_def]
  · rw [List.map_flatMap]
    apply perm_flatMap_congr; intro n hn
    refine ((dig_node' _ n _).map Msg.toFp).trans (List.Perm.of_eq ?_)
    simp only [Function.comp_apply, nodeViewOf, List.map_append]
    congr 2
    simp only [tDig]
    generalize nodeVOf (mkInfo c.1 e) n ((mkInfo c.1 e).nodeAt n) = v
    rcases v with ⟨k, sl, m⟩ | ⟨k, kd, m⟩ | ⟨sv, kids, m⟩
    · cases sl <;> rfl
    · rfl
    · rcases sv with _ | sl
      · rfl
      · cases sl <;> rfl

end

end NodeTr

end ZkFormal.Near.Render
