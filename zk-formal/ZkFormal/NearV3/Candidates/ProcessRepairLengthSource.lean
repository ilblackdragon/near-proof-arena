import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthSource
namespace ZkFormal.NearV3.Candidates.ProcessRepairLengthSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedLengthSource
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=73) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃q,q<tr.height 0 ∧ cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate=1 ∧
      announcement.msgVal (ProcPriorRoutedRawBytes.value tr) 0 q pub=i.msgVal tr t r pub := by
  rcases recv_src view.valid ht hr hi hb hs hm with hp|hp
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0:=Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference, ←view.length] using ht') hn j (by simpa only [view.wires t', ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have hg:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1:=by
      by_cases he:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1
      · exact he
      · change (if (ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1 then 1 else 0)+0≠0 at hjm
        simp only [he,ite_false,Nat.zero_add] at hjm
        exact (hjm rfl).elim
    refine ⟨q,hq,?_,hmsg⟩
    unfold cv
    rw [hg]
    rfl
theorem header {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    {q:Nat} (hq:q<tr.height 0)
    (hg:cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate=1) :
    cv (ProcPriorRoutedRawBytes.value tr) 0 q ValV3.vf=1 := by
  let e:Expr:=.mul (c ProcPriorValueLength.gate) (ZkFormal.Near.Dsl.not (c ValV3.vf))
  have h:=view.component 5 (by decide +kernel) (by decide)
  have heq:=h.constr q hq e (by
    change e∈Rcpt.Candidates.EmptyValueFusion.valueTable.constraints
    simp [e,Rcpt.Candidates.EmptyValueFusion.valueTable,ProcPriorValueLength.table,c,ZkFormal.Near.Dsl.c])
  have hgc:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1:=by
    rw [←Fp.ofNat_toNat ((ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate)]
    change Fp.ofNat (cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate)=1
    rw [hg];rfl
  change (ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate *
    (1 + - (ProcPriorRoutedRawBytes.value tr).cell 0 q ValV3.vf)=0 at heq
  rw [hgc] at heq
  have hvc:(ProcPriorRoutedRawBytes.value tr).cell 0 q ValV3.vf=1:=by grind
  unfold cv
  rw [hvc]
  rfl
end ZkFormal.NearV3.Candidates.ProcessRepairLengthSource
