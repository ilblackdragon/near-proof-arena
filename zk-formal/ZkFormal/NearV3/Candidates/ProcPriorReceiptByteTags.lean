import ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptView
namespace ZkFormal.NearV3.Candidates.ProcPriorReceiptByteTags
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open RcptV3Proof

def Safe (m:Msg):Prop:=m.headD 0<P ∧ 1≤m.headD 0%16 ∧ m.headD 0%16≤5

theorem emit (id off:Nat) (bytes:List Nat) (h:id<P ∧ 1≤id%16 ∧ id%16≤5)
    {m:Msg} (hm:m∈emitAt id off bytes) :Safe m := by
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hm
  exact h

theorem tag (k n:Nat) (hk:1≤k ∧ k≤5) (hn:n<2^22) :
    msgId k n<P ∧ 1≤msgId k n%16 ∧ msgId k n%16≤5 := by
  have he:msgId k n%16=k:=by unfold msgId;omega
  rw [he]
  unfold msgId P
  omega

theorem receipt (pub:List Fp) (xs:List RcptE) (j r o:Nat) (x:RcptE)
    (hj:j<2^22) (hr:r<2^22) {m:Msg} (hm:m∈rSends pub xs j r o x B_BYTES) :Safe m := by
  simp only [rSends,ite_true,List.mem_append,or_assoc] at hm
  have href:∀m∈(if x.hr then emitAt K_RF (bOffs xs r) x.encRefund else []),Safe m := by
    intro m hm
    split at hm
    · exact emit _ _ _ (by decide) hm
    · cases hm
  have hrid:∀m∈(if x.hr then emitAt (msgId K_RID r) 0 (x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0) else []),Safe m := by
    intro m hm
    split at hm
    · exact emit _ _ _ (tag K_RID r (by decide) hr) hm
    · cases hm
  rcases hm with hm|hm|hm|hm|hm
  · exact emit _ _ _ (tag K_RC j (by decide) hj) hm
  · exact href m hm
  · exact emit _ _ _ (tag K_PEO r (by decide) hr) hm
  · exact emit _ _ _ (tag K_LEAF r (by decide) hr) hm
  · exact hrid m hm

theorem receipt_index (ls:RcptV3Vs) (j k:Nat) (hj:j<ls.length)
    (hk:k<(ls.getD j default).rs.length) :baseR ls j+k<(flatR ls).length := by
  induction ls generalizing j with
  | nil=>simp at hj
  | cons x xs ih=>
    cases j with
    | zero=>simpa only [baseR,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,flatR,List.flatMap_cons,List.length_append,List.getD_cons_zero] using
        Nat.lt_of_lt_of_le hk (Nat.le_add_right x.rs.length (flatR xs).length)
    | succ j=>
      have h:=ih j (by simpa using hj) (by simpa using hk)
      simp only [baseR,List.take_succ_cons,List.map_cons,List.sum_cons,flatR,List.flatMap_cons,List.length_append] at *
      omega

theorem inventory (pub:List Fp) (ls:RcptV3Vs) (hl:ls.length<2^22)
    (hr:(flatR ls).length<2^22) {m:Msg} (hm:m∈rcptSends3 pub ls B_BYTES) :Safe m := by
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hj:=List.mem_range.mp hj
  simp only [ite_true,show B_BYTES≠B_RCL by decide,ite_false,List.append_nil,List.mem_append] at hm
  rcases hm with hm|hm
  · exact emit _ _ _ (tag K_RC j (by decide) (by omega)) hm
  · obtain ⟨⟨r,o,x⟩,hmem,hm⟩:=List.mem_flatMap.mp hm
    obtain ⟨k,hk,heq⟩:=List.mem_map.mp hmem
    have hk:=List.mem_range.mp hk
    have hri:=receipt_index ls j k hj hk
    cases heq
    exact receipt pub (flatR ls) j _ _ _ (by omega) (by omega) hm

/-- Every actual receipt BYTES message carries a nonwrapping tag1..5,
so it cannot masquerade as a trie-node or value preimage. -/
theorem physical {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {msg:List Fp}
    (hm:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true msg) :
    1≤(msg.headD 0).toNat%16 ∧ (msg.headD 0).toNat%16≤5 := by
  obtain ⟨bs,e,hc,htraffic,hlen,hcount⟩:=ProcPriorRoutedReceiptView.view hH htables
  rw [tableBusCount_eq] at hm
  have hmem:=List.count_pos_iff.mp hm
  have hmem:=htraffic.mem_iff.mp hmem
  obtain ⟨m,hm,heq⟩:=List.mem_map.mp hmem
  have hflat:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length=
      (bs.map fun b=>b.receipts.length).sum := by
    rw [flat_views,List.length_map]
    simp only [List.length_flatMap]
  have hsafe:=inventory pub _ (by simpa using hlen) (by omega) hm
  have hehead:msg.headD 0=Fp.ofNat (m.headD 0) := by
    rw [←heq]
    cases m <;> rfl
  rw [hehead,Fp.toNat_ofNat,Nat.mod_eq_of_lt hsafe.1]
  exact hsafe.2
end ZkFormal.NearV3.Candidates.ProcPriorReceiptByteTags
