import ZkFormal.NearV3.Rcpt.Candidates.SizeCountValView

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

def countedValTraffic (es : List ValE) : Traffic :=
  ⟨fun b => if b=B_SIZE then [[1,valPayload es,(es.filter fun e => !e.dup).length]] else valSends es b,
    valRecvs es⟩

theorem count_nonSize {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (is : List Interaction) (e : Expr) (b : Nat) (hb : b≠B_SIZE) (side : Bool) (m : List Fp) :
    tableBusCount (is.map (withCount e)) tr t pub b side m=
      tableBusCount is tr t pub b side m := by
  rw [tableBusCount_eq,tableBusCount_eq]
  simp [rowTraffic_withCount,hb]

theorem val_candidate_traffic {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal valTable tr tt pub) (segs : List (Nat×Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs≤tr.height tt)
    (hall : ∀ p∈segs, IsSeg (ValProof.isOne tr tt ValV3.act)
      (ValProof.isOne tr tt ValV3.vf) (ValProof.isOne tr tt ValV3.vl) p.1 p.2)
    (hpad : ∀ r,segEnd 0 segs≤r → r<tr.height tt → ValProof.isOne tr tt ValV3.act r=false) :
    ValWf (segs.map (ValProof.valOf tr tt)) ∧
      TableTraffic valTable.interactions tr tt pub
        (countedValTraffic (segs.map (ValProof.valOf tr tt))) := by
  obtain ⟨hw,ht⟩ := val_view_from_segments (val_local_base h) segs hc hend hall hpad
  refine ⟨hw,fun b m => ⟨?_,?_⟩⟩
  · by_cases hb : b=B_SIZE
    · subst b
      rw [tableBusCount_eq,val_size_sender h segs hc hend hall hpad]
      simp only [countedValTraffic,ite_true,List.map_cons,List.map_nil,Msg.toFp]
      rfl
    · change tableBusCount (ValV3.interactions.map (withCount (c valCount))) tr tt pub b true m=_
      rw [count_nonSize _ _ b hb]
      simpa only [countedValTraffic,if_neg hb,valTraffic] using (ht b m).1
  · by_cases hb : b=B_SIZE
    · subst b
      rw [tableBusCount_eq]
      simp only [valTable,rowTraffic_withCount,ite_true,ValProof.rowT]
      simp [countedValTraffic,valRecvs,B_SIZE,B_BYTES,B_VBYTES,B_VPARENT,B_DUP,B_ENT,flatMap_nil_fun]
    · change tableBusCount (ValV3.interactions.map (withCount (c valCount))) tr tt pub b false m=_
      rw [count_nonSize _ _ b hb]
      exact (ht b m).2

/-- A single concrete candidate value view satisfies full ValWf and every bus
traffic equation, including the authenticated native record count on SIZE. -/
theorem val_candidate_view {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) :
    ∃ es, ValWf es ∧ TableTraffic valTable.interactions tr t pub (countedValTraffic es) := by
  have hl := val_local_base h
  have hpos : 0<tr.height t := Nat.two_pow_pos _
  obtain ⟨segs,hc,he,hs,hpad⟩ : ∃ segs : List (Nat×Nat), Consec 0 segs ∧
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
  exact ⟨segs.map (ValProof.valOf tr t),val_candidate_traffic h segs hc he hs hpad⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
