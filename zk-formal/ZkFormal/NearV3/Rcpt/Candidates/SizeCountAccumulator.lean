import ZkFormal.NearV3.Rcpt.Candidates.SizeCountControl

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

/-- Candidate count-total is the sum of precisely the three received count cells. -/
theorem count_accumulator {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) :
    tr.cell t 2 countTotal=tr.cell t 0 count+tr.cell t 1 count+tr.cell t 2 count := by
  obtain ⟨hh,_,h1,h2,_⟩ := Control.layout h
  have hf := h.constr 0 (by omega) (.mul .isFirst (sub (c countTotal) (c count)))
    (List.mem_append_right _ (by simp))
  simp only [eval_mul,eval_isFirst,ite_true,eval_sub,eval_c] at hf
  have ht (r : Nat) (hr : r+1<tr.height t) (ha : tr.cell t (r+1) SizeV3.act=1) :
      tr.cell t (r+1) countTotal=tr.cell t r countTotal+tr.cell t (r+1) count := by
    have he := h.constr r (by omega)
      (mul3 .isTransition (n SizeV3.act) (sub (n countTotal) (.add (c countTotal) (n count))))
      (List.mem_append_right _ (by simp))
    simp only [eval_mul3,eval_isTransition,eval_n,eval_sub,eval_add,eval_c,
      Nat.mod_eq_of_lt hr,if_neg (show ¬r+1=tr.height t by omega),ha] at he
    grind
  have h01 := ht 0 (by omega) h1
  have h12 := ht 1 (by omega) h2
  grind

/-- Exact physical receiving traffic; padding contributes no count messages. -/
theorem received_counts {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) :
    (List.range (tr.height t)).flatMap (fun r =>
      rowTraffic sizeTable.interactions tr t r pub B_SIZE false) =
      [[0,tr.cell t 0 SizeV3.x,tr.cell t 0 count],
       [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count],
       [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]] := by
  obtain ⟨hh,h0,h1,h2,h3,t0,t1,t2,_⟩ := Control.layout h
  simp only [sizeTable,rowTraffic_withCount,SizeProof.rowT,hh,
    show List.range 4=[0,1,2,3] from rfl,List.flatMap_cons,List.flatMap_nil,
    h0,h1,h2,h3,t0,t1,t2,true_and,ite_true,fp_zero_ne_one,ite_false]
  simp [eval_c]

/-- Exact global SIZE count balance authenticates all received payload/count
cells. The source provider must explicitly send zero store-record count. -/
theorem authenticate_counts {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) (p0 p1 p2 c0 c1 : Fp)
    (hb : ∀ m, tableBusCount sizeTable.interactions tr t pub B_SIZE false m=
      ([[0,p0,c0],[1,p1,c1],[2,p2,0]] : List (List Fp)).count m) :
    tr.cell t 0 SizeV3.x=p0 ∧ tr.cell t 1 SizeV3.x=p1 ∧ tr.cell t 2 SizeV3.x=p2 ∧
    tr.cell t 0 count=c0 ∧ tr.cell t 1 count=c1 ∧ tr.cell t 2 count=0 ∧
    tr.cell t 2 countTotal=c0+c1 := by
  have hp : ([[0,tr.cell t 0 SizeV3.x,tr.cell t 0 count],
      [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count],
      [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]] : List (List Fp)).Perm
      [[0,p0,c0],[1,p1,c1],[2,p2,0]] := by
    apply List.perm_iff_count.mpr
    intro m
    have hh := hb m
    rwa [tableBusCount_eq,received_counts h] at hh
  have h0 := hp.subset (show [0,tr.cell t 0 SizeV3.x,tr.cell t 0 count]∈
    ([[0,tr.cell t 0 SizeV3.x,tr.cell t 0 count],
      [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count],
      [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]] : List (List Fp)) by simp)
  have h1 := hp.subset (show [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count]∈
    ([[0,tr.cell t 0 SizeV3.x,tr.cell t 0 count],
      [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count],
      [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]] : List (List Fp)) by simp)
  have h2 := hp.subset (show [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]∈
    ([[0,tr.cell t 0 SizeV3.x,tr.cell t 0 count],
      [1,tr.cell t 1 SizeV3.x,tr.cell t 1 count],
      [2,tr.cell t 2 SizeV3.x,tr.cell t 2 count]] : List (List Fp)) by simp)
  have ne01 : (0:Fp)≠1 := by decide
  have ne02 : (0:Fp)≠2 := by decide
  have ne12 : (1:Fp)≠2 := by decide
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,
    and_true,true_and,ne01,ne02,ne12,Ne.symm ne01,Ne.symm ne02,Ne.symm ne12,
    false_and,false_or,or_false] at h0 h1 h2
  have hc := count_accumulator h
  grind

theorem payload_accumulator {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) :
    tr.cell t 2 SizeV3.tot=tr.cell t 0 SizeV3.x+tr.cell t 1 SizeV3.x+tr.cell t 2 SizeV3.x := by
  obtain ⟨hh,_,h1,h2,_⟩ := Control.layout h
  have hf := (Control.firstF h (by omega)).2.2.1
  have h01 := ((Control.trF h (r := 0) (by omega)).2.2.2 h1).1
  have h12 := ((Control.trF h (r := 1) (by omega)).2.2.2 h2).1
  grind

/-- The final native inequality follows from exact SIZE balance and the actual
24-bit slack. Public overhead and global no-wrap are explicitly bound. -/
theorem authenticated_total_bound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) (p0 p1 p2 c0 c1 overhead : Nat)
    (hb : ∀ m, tableBusCount sizeTable.interactions tr t pub B_SIZE false m=
      ([[0,(p0:Fp),(c0:Fp)],[1,(p1:Fp),(c1:Fp)],[2,(p2:Fp),0]] : List (List Fp)).count m)
    (ho : SizeV3.ovhE.eval tr t 2 pub=(overhead:Fp))
    (hn : overhead+p0+p1+p2+4*(c0+c1)+2^24≤P) :
    overhead+(p0+p1+p2)+4*(c0+c1)≤8388608 := by
  obtain ⟨hh,_,_,_,_,_,_,_,hl⟩ := Control.layout h
  obtain ⟨h0,h1,h2,_,_,_,hc⟩ := authenticate_counts h (p0:Fp) (p1:Fp) (p2:Fp) (c0:Fp) (c1:Fp) hb
  let slack := bitsVal (fun b => cv tr t 2 (SizeV3.bt b)) 0 24
  have hbval : SizeV3.bitsE.eval tr t 2 pub=(slack:Fp) :=
    eval_bits tr t 2 pub SizeV3.bt 0 24 (fun b hb => Control.isB h (by omega)
      (by rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (f := SizeV3.bt) (List.mem_range.mpr hb))))
  have hslack : slack<2^24 := bitsVal_lt _ 0 24 (fun b hb => cv_bool (Control.isB h (by omega)
    (by rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (f := SizeV3.bt) (List.mem_range.mpr hb)))))
  have ht := payload_accumulator h
  rw [h0,h1,h2,← natCast_add,← natCast_add] at ht
  rw [← natCast_add] at hc
  exact final_total_bound h (by omega) hl slack overhead (p0+p1+p2) (c0+c1)
    hbval ho ht hc (by omega)

/-- Actual candidate-local SIZE constraints plus authenticated bus records pay
for the complete native witness encoding, including every record prefix. -/
theorem authenticated_witness_paid {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal sizeTable tr t pub) (w : NearSpecV3.StateWitness)
    (N p0 p1 sourceSize c0 c1 : Nat)
    (he : w.epochId.length=32) (ha : w.appliedReceiptsHash.length=32)
    (ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32)
    (hd : (NearSpecV3.encList ZkFormal.V3.encodeEntry w.entries).length=sourceSize+44*N+4)
    (hp : witnessPayload w≤p0+p1) (hc : witnessRecordCount w≤c0+c1)
    (hb : ∀ m, tableBusCount sizeTable.interactions tr t pub B_SIZE false m=
      ([[0,(p0:Fp),(c0:Fp)],[1,(p1:Fp),(c1:Fp)],[2,(sourceSize:Fp),0]] : List (List Fp)).count m)
    (ho : SizeV3.ovhE.eval tr t 2 pub=
      ((224+w.innerBytes.length+44*N+69*w.implicit.length:Nat):Fp))
    (hn : (224+w.innerBytes.length+44*N+69*w.implicit.length)+p0+p1+sourceSize+
      4*(c0+c1)+2^24≤P) :
    (ZkFormal.V3.encodeSW w).length≤8388608 := by
  apply counted_witness_paid w N sourceSize (p0+p1) (c0+c1) he ha ht hd hp hc
  exact authenticated_total_bound h p0 p1 sourceSize c0 c1 _ hb ho hn

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
