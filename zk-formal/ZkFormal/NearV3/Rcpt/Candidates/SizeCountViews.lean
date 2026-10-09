import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSegments
import ZkFormal.NearV3.Extract.Node.Proof

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The physical count at the actual node SUM row counts precisely the
nonduplicate records of the very same segmented extracted view. -/
theorem node_count_view {tr : Trace Fp} {pub : List Fp}
    (h : TableLocal nodeTable tr T_NODE pub) {segs : List (Nat×Nat)}
    (hs : NodeProof3.NodeSegs tr segs) :
    (tr.cell T_NODE (segEnd 0 segs) nodeCount).toNat =
      ((NodeProof3.viewOf tr pub segs).filter fun v => !v.dup).length := by
  have hb := node_local_base h
  have hl : TableLocal NodeV3.table tr T_NODE pub := hb
  rw [node_count_prefix h (hs.sumRow hl).1]
  have hp := prefix_segments (recordMark tr T_NODE NodeV3.nf NodeV3.dup)
    (fun p => !(NodeProof3.nodeSOf tr pub p.1 p.2).dup) segs 0 hs.consec (by
      intro p hm
      have hh := hs.seg p hm
      refine ⟨hh.1, ?_, ?_⟩
      · have hf := hh.2.1
        rw [NodeProof3.one_iff] at hf
        have hr : p.1<tr.height T_NODE := by
          have := hs.bound hl hm; have := hs.endLe; have := hh.1; omega
        rcases NodeProof3.isBool hl hr (x := NodeV3.dup) (by simp [NodeV3.boolCols]) with hd|hd
        · simp [recordMark,NodeProof3.nodeSOf,cv,hf,hd]; decide
        · simp [recordMark,NodeProof3.nodeSOf,cv,hf,hd]; decide
      · intro r hr he
        have hn := hh.2.2.2.2.1 r hr he
        simp only [NodeProof3.one,decide_eq_false_iff_not] at hn
        simp [recordMark,hn])
  simpa [recordPrefix,NodeProof3.viewOf,List.filter_map,Function.comp_def] using hp

/-- Value segments include zero-byte records: no `vz` gate is used in the
record count. The supplied segmentation is the one used by `valOf`. -/
theorem val_count_view {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) (segs : List (Nat×Nat))
    (hc : Consec 0 segs) (he : segEnd 0 segs<tr.height t)
    (hs : ∀ p∈segs, IsSeg (ValProof.isOne tr t ValV3.act)
      (ValProof.isOne tr t ValV3.vf) (ValProof.isOne tr t ValV3.vl) p.1 p.2) :
    (tr.cell t (segEnd 0 segs) valCount).toNat =
      ((segs.map (ValProof.valOf tr t)).filter fun v => !v.dup).length := by
  rw [val_count_prefix h he]
  have hp := prefix_segments (recordMark tr t ValV3.vf ValV3.dup)
    (fun p => !(ValProof.valOf tr t p).dup) segs 0 hc (by
      intro p hm
      have hh := hs p hm
      refine ⟨hh.1, ?_, ?_⟩
      · have hf := hh.2.1
        simp only [ValProof.isOne,decide_eq_true_eq] at hf
        have hr : p.1<tr.height t := by
          have := (seg_le_end segs 0 hc p hm).2; have := hh.1; omega
        rcases ValProof.isBool (val_local_base h) hr
          (x := ValV3.dup) (by simp [ValProof.bools]) with hd|hd <;>
          simp [recordMark,ValProof.valOf,hf,hd]
      · intro r hr he
        have hn := hh.2.2.2.2.1 r hr he
        simp only [ValProof.isOne,decide_eq_false_iff_not] at hn
        simp [recordMark,hn])
  simpa [recordPrefix,List.filter_map,Function.comp_def] using hp

/-- Node segmentation is extracted from candidate-local constraints; no
independent count or view selection is assumed. -/
theorem node_count_view_exists {tr : Trace Fp} {pub : List Fp}
    (h : TableLocal nodeTable tr T_NODE pub) :
    ∃ segs, NodeProof3.NodeSegs tr segs ∧
      NodeWf3 (NodeProof3.viewOf tr pub segs) ∧
      (tr.cell T_NODE (segEnd 0 segs) nodeCount).toNat =
        ((NodeProof3.viewOf tr pub segs).filter fun v => !v.dup).length := by
  have hl : TableLocal NodeV3.table tr T_NODE pub := node_local_base h
  obtain ⟨segs,hs⟩ := NodeProof3.nodeSegs_exist hl
  exact ⟨segs,hs,NodeProof3.nodeWfOf hl hs,node_count_view h hs⟩

/-- Complete value segmentation is obtained from the actual local constraints,
including an empty table and zero-byte value records. -/
theorem val_count_view_exists {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) :
    ∃ segs : List (Nat×Nat), Consec 0 segs ∧ segEnd 0 segs<tr.height t ∧
      (∀ p∈segs, IsSeg (ValProof.isOne tr t ValV3.act)
        (ValProof.isOne tr t ValV3.vf) (ValProof.isOne tr t ValV3.vl) p.1 p.2) ∧
      (tr.cell t (segEnd 0 segs) valCount).toNat =
        ((segs.map (ValProof.valOf tr t)).filter fun v => !v.dup).length := by
  have hl := val_local_base h
  have hpos : 0<tr.height t := Nat.two_pow_pos _
  obtain ⟨segs,hc,he,hs,_⟩ : ∃ segs : List (Nat×Nat), Consec 0 segs ∧
      segEnd 0 segs≤tr.height t ∧
      (∀ p∈segs, IsSeg (ValProof.isOne tr t ValV3.act)
        (ValProof.isOne tr t ValV3.vf) (ValProof.isOne tr t ValV3.vl) p.1 p.2) ∧
      (∀ r,segEnd 0 segs≤r → r<tr.height t → ValProof.isOne tr t ValV3.act r=false) := by
    by_cases ha : tr.cell t 0 ValV3.act=1
    · exact segments_of (ValProof.segFacts hl ha) hpos
    · refine ⟨[],trivial,by simp [segEnd],by simp,?_⟩
      have hz : ∀ r,r<tr.height t → tr.cell t r ValV3.act=0 := by
        intro r
        induction r with
        | zero => intro _; exact (ValProof.isBool hl hpos (x := ValV3.act) (by simp [ValProof.bools])).resolve_right ha
        | succ r ih => intro hr; exact (ValProof.padFacts hl hr (ih (by omega))).1
      intro r _ hr
      simp [ValProof.isOne,hz r hr]
  have he' : segEnd 0 segs<tr.height t := by
    by_cases hn : segs=[]
    · subst segs; simpa [segEnd] using hpos
    · have hn' : 0<segs.length := List.length_pos_iff.mpr hn
      let p := segs[segs.length-1]'(by omega)
      have hm : p∈segs := List.getElem_mem _
      have hh := hs p hm
      have hend : segEnd 0 segs=p.1+p.2 := segEnd_last segs 0 hc hn'
      have ha := hh.2.2.2.1 (p.1+p.2-1) (by have := hh.1; omega) (by have := hh.1; omega)
      simp only [ValProof.isOne,decide_eq_true_eq] at ha
      by_cases hbad : segEnd 0 segs<tr.height t
      · exact hbad
      exfalso
      have heq : p.1+p.2-1=tr.height t-1 := by omega
      rw [heq,ValProof.lastRow hl hpos] at ha
      exact (by decide : (0:Fp)≠1) ha
  exact ⟨segs,hc,he',hs,val_count_view h segs hc he' hs⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
