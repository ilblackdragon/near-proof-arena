import ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound
import ZkFormal.NearV3.Candidates.ProcPriorAccountByteTag
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ZkFormal.Near.Dsl ProcPriorAccountByteTag
set_option maxRecDepth 32768
theorem tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {r:Nat} (hr:r<tr.height 6) {i:Interaction}
    (hi:i∈AP.tables[6]!.interactions) (hb:i.bus=B_BYTES) (hs:i.send=true)
    (hm:i.multNat tr 6 r pub≠0) :((i.msgVal tr 6 r pub).headD 0).toNat%16=K_VPOST := by
  have he:AP.tables[6]!.interactions=(ProcPriorComparatorRoutedFamily.tables[6]!).interactions:=by rw [v.wires]
  rw [he] at hi
  obtain ⟨j,hj,hjb,hjs,hjm,hjhead,hihead⟩:=paired hi hb hs (by intro he; simp [Interaction.multNat,Interaction.multNat.go,he] at hm)
  have ht:6<AP.tables.length:=by rw [v.length];decide +kernel
  have hj':j∈AP.tables[6]!.interactions:=by rw [he];exact hj
  have hmult:j.multNat tr 6 r pub≠0:=by simpa only [Interaction.multNat,hjm] using hm
  have hbound:=ProcessRepairVbytesIdBound.sender_id v hpub ht hr hj' hjb hjs hmult
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
end ZkFormal.NearV3.Candidates.ProcessRepairAccountByteTag
