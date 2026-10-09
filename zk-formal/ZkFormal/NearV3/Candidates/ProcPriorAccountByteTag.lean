import ZkFormal.NearV3.Candidates.ProcPriorVbytesIdBound
namespace ZkFormal.NearV3.Candidates.ProcPriorAccountByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ZkFormal.Near.Dsl
set_option maxRecDepth 32768

theorem paired {i:Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[6]!).interactions) (hb:i.bus=B_BYTES) (hs:i.send=true) (hn:i.mult≠[]) :
    ∃j,j∈(ProcPriorComparatorRoutedFamily.tables[6]!).interactions ∧ j.bus=B_VBYTES ∧ j.send=true ∧ j.mult=i.mult ∧
      j.msg.headD (k 0)=c Acct.kk ∧ i.msg.headD (k 0)=mid K_VPOST (c Acct.kk) := by
  have hall:(ProcPriorComparatorRoutedFamily.tables[6]!).interactions.all (fun i=>i.bus != B_BYTES || !i.send || i.mult.isEmpty ||
      (ProcPriorComparatorRoutedFamily.tables[6]!).interactions.any (fun j=>decide (j.bus=B_VBYTES ∧ j.send=true ∧ j.mult=i.mult ∧
        j.msg.headD (k 0)=c Acct.kk ∧ i.msg.headD (k 0)=mid K_VPOST (c Acct.kk))))=true := by decide +kernel
  have h:=List.all_eq_true.mp hall i hi
  have hnil:i.mult.isEmpty=false:=by cases hx:i.mult <;> simp_all
  simp only [hb,hs,hnil,bne_self_eq_false,Bool.not_true,Bool.false_or] at h
  obtain ⟨j,hj,h⟩:=List.any_eq_true.mp h
  exact ⟨j,hj,of_decide_eq_true h⟩

theorem tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {r:Nat} (hr:r<tr.height 6) {i:Interaction}
    (hi:i∈AP.tables[6]!.interactions) (hb:i.bus=B_BYTES) (hs:i.send=true)
    (hm:i.multNat tr 6 r pub≠0) :((i.msgVal tr 6 r pub).headD 0).toNat%16=K_VPOST := by
  have he:AP.tables[6]!.interactions=(ProcPriorComparatorRoutedFamily.tables[6]!).interactions:=by rw [htables]
  rw [he] at hi
  obtain ⟨j,hj,hjb,hjs,hjm,hjhead,hihead⟩:=paired hi hb hs (by intro he; simp [Interaction.multNat,Interaction.multNat.go,he] at hm)
  have ht:6<AP.tables.length:=by rw [htables];decide +kernel
  have hj':j∈AP.tables[6]!.interactions:=by rw [he];exact hj
  have hmult:j.multNat tr 6 r pub≠0:=by simpa only [Interaction.multNat,hjm] using hm
  have hbound:=ProcPriorVbytesIdBound.sender_id hH htables hpub ht hr hj' hjb hjs hmult
  have eval_head (x:Interaction): (x.msgVal tr 6 r pub).headD 0=(x.msg.headD (k 0)).eval tr 6 r pub := by
    cases h:x.msg <;> simp [Interaction.msgVal,h,k,Expr.eval,Expr.evalWith,rowEnv] <;> rfl
  rw [eval_head j,hjhead,eval_c] at hbound
  rw [eval_head i,hihead]
  have hsmall:msgId K_VPOST (tr.cell 6 r Acct.kk).toNat<P:=by unfold msgId K_VPOST P;omega
  have hcast:(mid K_VPOST (c Acct.kk)).eval tr 6 r pub=Fp.ofNat (msgId K_VPOST (tr.cell 6 r Acct.kk).toNat) := by
    simp only [mid,eval_add,eval_smul,eval_k,eval_c,msgId]
    change Fp.ofNat K_VPOST+Fp.ofNat 16*tr.cell 6 r Acct.kk=Fp.ofNat (K_VPOST+16*(tr.cell 6 r Acct.kk).toNat)
    rw [←ofNat_add',←ofNat_mul',Fp.ofNat_toNat]
  rw [hcast,Fp.toNat_ofNat,Nat.mod_eq_of_lt hsmall]
  simp [msgId,K_VPOST,Nat.add_mod]
end ZkFormal.NearV3.Candidates.ProcPriorAccountByteTag
