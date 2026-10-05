import ZkFormal.Near.Render.Proof.NodeViewFacts
import ZkFormal.Near.Render.Proof.BusParent
import ZkFormal.Near.Render.Proof.RcptBytes2

/-!
# ZkFormal.Near.Render.Proof.DigNode — the `node` table's `DIGEST` receives

The node views receive (`nodeRecvs … B_DIGEST`): the root's `NPRE/NPOST`
digests against the claim's state roots, each revealed child's `NPRE/NPOST`
digests, and each touched slot's `VPRE/VPOST` digests.  Every non-root node is
the child of exactly one slot (`BusParent.count_children`), so these are a
permutation of the digests of the `node` and `acct` SHA messages
(`node_digest`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusDigest

theorem perm_flatMap_append {α β : Type} (f g : α → List β) :
    ∀ l : List α, (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g)
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left (f a) ?_
    refine ((perm_flatMap_append f g l).append_left (g a)).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _

theorem flatMap_filter {α β : Type} (p : α → Bool) (H : α → List β) :
    ∀ l : List α, (l.filter p).flatMap H = l.flatMap fun x => if p x then H x else []
  | [] => rfl
  | x :: l => by
    by_cases h : p x <;> simp [h, flatMap_filter p H l]

/-- Digest messages of the node `NPRE/NPOST` of node `k`. -/
def nF (I : Info) (k : Nat) : List ZkFormal.Near.Msg :=
  [digestMsg ⟨msgId K_NPRE k, I.pre.getD k []⟩, digestMsg ⟨msgId K_NPOST k, I.post.getD k []⟩]

/-- Digest messages of the value windows of slot `k`. -/
def vH (I : Info) (k : Nat) : List ZkFormal.Near.Msg :=
  [digestMsg ⟨msgId K_VPRE k, I.vpre.getD k []⟩, digestMsg ⟨msgId K_VPOST k, I.vpost.getD k []⟩]

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hk : KeyBound e)
include hg hk

open NodeInfo

theorem pp_len {n : Nat} (hn : n < e.ns.length) :
    ((mkInfo c.1 e).post.getD n []).length = ((mkInfo c.1 e).pre.getD n []).length := by
  rw [← view_pre hg hn (hk _ (List.getElem_mem hn)), ← view_post hg hn (hk _ (List.getElem_mem hn))]
  exact Link.ser_length_post _ (view_wf _ _ (hg.nodes_wf _ (List.getElem_mem hn)))

omit hk in
theorem vH_eq {n : Nat} (hn : n < e.ns.length) (ht : e.ns[n].touched = true) :
    vH (mkInfo c.1 e) n = [digMsg (msgId K_VPRE n) 72 (shaN ((mkInfo c.1 e).vpre.getD n [])),
      digMsg (msgId K_VPOST n) 72 (shaN ((mkInfo c.1 e).vpost.getD n []))] := by
  have hm : n ∈ (mkInfo c.1 e).touched := mem_touched.2 ⟨e.ns[n], by simp [hn], ht⟩
  have h1 : ((mkInfo c.1 e).vpre.getD n []).length = 72 := by
    rw [vpre_eq hm, toNats_len]; exact hg.vals_len n e.ns[n] (by simp [hn]) ht
  have h2 := acct_post hg n hm
  simp only [vH, digestMsg, digMsg, h1, h2]

/-- The per-node receives. -/
theorem node_at {n : Nat} (uses : Std.HashMap Edge Nat) :
    ((nodeViewOf (mkInfo c.1 e) uses n).v.revealed.flatMap fun (x : Nat × Nat × Nat × List Nat × List Nat) =>
        [digMsg (msgId K_NPRE x.1) x.2.1 x.2.2.2.1, digMsg (msgId K_NPOST x.1) x.2.1 x.2.2.2.2]) =
      (kidIds ((mkInfo c.1 e).nodeAt n)).flatMap (nF (mkInfo c.1 e)) := by
  simp only [nodeViewOf, view_revealed, List.flatMap_map]
  apply flatMap_congr'
  intro k hkm
  have hch := kid_child (ns := e.ns) (n := n) hkm
  have hk' := (hg.shape.child_range n k hch).2
  simp only [revOf, nF, digestMsg, digMsg, Info.preDig, Info.postDig, pp_len hg hk hk']

/-- The root's receives: the claim's state roots are the root digests. -/
theorem root_eq (uses : Std.HashMap Edge Nat) :
    [digMsg K_NPRE (((nodeViewsOf (mkInfo c.1 e) uses).headD default).v.ser false).length
        ((List.range 32).map fun j => pubNat (pubOf c.1) (PV_PRE + j)),
      digMsg K_NPOST (((nodeViewsOf (mkInfo c.1 e) uses).headD default).v.ser false).length
        ((List.range 32).map fun j => pubNat (pubOf c.1) (PV_POST + j))] = nF (mkInfo c.1 e) 0 := by
  have h0 := hg.shape.nonempty
  have hhead : (nodeViewsOf (mkInfo c.1 e) uses).headD default = nodeViewOf (mkInfo c.1 e) uses 0 := by
    simp only [nodeViewsOf, info_N]
    obtain ⟨k, hk'⟩ : ∃ k, e.ns.length = k + 1 := ⟨e.ns.length - 1, by omega⟩
    rw [hk', List.range_succ_eq_map]; rfl
  have hv : (nodeViewOf (mkInfo c.1 e) uses 0).v.ser false = (mkInfo c.1 e).pre.getD 0 [] := by
    simp only [nodeViewOf, info_nodeAt h0]
    exact view_pre hg h0 (hk _ (List.getElem_mem h0))
  have hh : Link.Hdr c := ⟨hg.pv, hg.chain⟩
  have p1 : (List.range 32).map (fun j => pubNat (pubOf c.1) (PV_PRE + j)) = shaN ((mkInfo c.1 e).pre.getD 0 []) := by
    rw [show shaN ((mkInfo c.1 e).pre.getD 0 []) = (mkInfo c.1 e).preDig 0 from rfl, info_preDig hg.shape h0]
    rw [show (treeOf e.ns e.vals0 e.ns.length 0) = trieOf e.ns e.vals0 from rfl, hg.preRoot]
    exact Link.pub_pre hh
  have p2 : (List.range 32).map (fun j => pubNat (pubOf c.1) (PV_POST + j)) = shaN ((mkInfo c.1 e).post.getD 0 []) := by
    rw [show shaN ((mkInfo c.1 e).post.getD 0 []) = (mkInfo c.1 e).postDig 0 from rfl, info_postDig hg.shape h0]
    rw [show (treeOf e.ns (e.valsAt e.rs.length) e.ns.length 0) = trieOf e.ns (e.valsAt e.rs.length) from rfl,
      hg.postRoot]
    exact Link.pub_post hh
  rw [hhead, hv, p1, p2]
  simp only [nF, digestMsg, digMsg, pp_len hg hk h0]
  rfl

/-- **The node receives on `DIGEST`.** -/
theorem node_digest (uses : Std.HashMap Edge Nat) :
    (nodeRecvs (nodeViewsOf (mkInfo c.1 e) uses) (pubOf c.1) B_DIGEST).Perm
      ((nodeMsgs (mkInfo c.1 e)).map digestMsg ++ (acctMsgs (mkInfo c.1 e)).map digestMsg) := by
  have h0 := hg.shape.nonempty
  have hroot := root_eq hg hk uses
  simp only [nodeRecvs, B_DIGEST, ↓reduceIte] at hroot ⊢
  rw [hroot]
  simp only [nodeViewsOf, List.length_map, List.length_range, zip_range_map, List.flatMap_map, info_N]
  rw [flatMap_congr' (g := fun n => (kidIds ((mkInfo c.1 e).nodeAt n)).flatMap (nF (mkInfo c.1 e)) ++
      (if ((mkInfo c.1 e).nodeAt n).touched then vH (mkInfo c.1 e) n else [])) (fun n hn => ?_)]
  · refine (List.Perm.append_left _ (perm_flatMap_append _ _ _)).trans ?_
    rw [← List.append_assoc, ← List.flatMap_assoc]
    have hm1 : (nodeMsgs (mkInfo c.1 e)).map digestMsg = (List.range e.ns.length).flatMap (nF (mkInfo c.1 e)) := by
      simp only [nodeMsgs, List.map_flatMap, info_N]; rfl
    have hm2 : (acctMsgs (mkInfo c.1 e)).map digestMsg =
        (List.range e.ns.length).flatMap fun n =>
          if ((mkInfo c.1 e).nodeAt n).touched then vH (mkInfo c.1 e) n else [] := by
      simp only [acctMsgs, List.map_flatMap, mkInfo_touched]
      rw [flatMap_filter]; rfl
    rw [hm1, hm2]
    refine List.Perm.append_right _ ?_
    rw [← List.flatMap_cons (f := nF (mkInfo c.1 e))]
    apply List.Perm.flatMap_right
    have hc : ((List.range e.ns.length).flatMap fun n => kidIds ((mkInfo c.1 e).nodeAt n)).Perm
        ((List.range e.ns.length).drop 1) :=
      List.perm_iff_count.2 (BusParent.count_children hg.shape)
    refine (hc.cons 0).trans (List.Perm.of_eq ?_)
    obtain ⟨k, hk'⟩ : ∃ k, e.ns.length = k + 1 := ⟨e.ns.length - 1, by omega⟩
    rw [hk', List.range_succ_eq_map]; rfl
  · have hn' := List.mem_range.1 hn
    simp only [nodeViewOf]
    congr 1
    · exact node_at hg hk uses
    · rw [info_nodeAt hn']
      by_cases ht : e.ns[n].touched = true
      · simp only [ht, ↓reduceIte]; rw [vH_eq hg hn' ht]
        cases hnr : e.ns[n] with
        | leaf k v mem => cases v <;> simp_all [nodeVOf, nslotOf, NodeRec.touched]
        | ext k kid mem => simp_all [NodeRec.touched]
        | branch v kids mem =>
          rcases v with _ | v
          · simp_all [NodeRec.touched]
          · cases v <;> simp_all [nodeVOf, nslotOf, NodeRec.touched]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte]
        cases hnr : e.ns[n] with
        | leaf k v mem => cases v <;> simp_all [nodeVOf, nslotOf, NodeRec.touched]
        | ext k kid mem => simp [nodeVOf]
        | branch v kids mem =>
          rcases v with _ | v
          · simp [nodeVOf]
          · cases v <;> simp_all [nodeVOf, nslotOf, NodeRec.touched]

end

end BusDigest

end ZkFormal.Near.Render
