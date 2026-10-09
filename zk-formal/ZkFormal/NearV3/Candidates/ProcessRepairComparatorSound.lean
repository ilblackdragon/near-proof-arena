import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedSound
namespace ZkFormal.NearV3.Candidates.ProcessRepairComparatorSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorComparatorRoutedSound
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem sound {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {t r : Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i : Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=40) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) {x y b : Fp} (hmsg:i.msgVal tr t r pub=[x,y,b])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :
    (b=1 ∧ y.toNat≤x.toNat) ∨ (b=0 ∧ x.toNat<y.toNat) := by
  have ht0:0<AP.tables.length := by rw [view.length];decide +kernel
  have hother:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=40→i.send=true:=by
    intro t ht hn i hi hb
    rw [view.wires] at hi
    exact other_tables (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference,←view.length] using ht) hn i hi hb
  obtain ⟨q,hq,j,hj,hjb,hjs,hmatch,_⟩:=send_matched view.valid ht0 hother hpub ht hr hi hb hs hm
  rw [view.wires] at hj
  have hej:=receiver_eq hj hjb hjs
  subst j
  rw [receiver_message,hmsg] at hmatch
  simp only [Cmp.interactions,List.getElem!_cons_zero,Interaction.msgVal,Cmp.msg,List.map_cons,List.map_nil,List.cons.injEq] at hmatch
  obtain ⟨ex,ey,eb,_⟩:=hmatch
  have hlocal:=view.component 12 (by decide +kernel) (by decide)
  change ZkFormal.Near.TableLocal (Cmp.table 40) (comparator tr) 0 pub at hlocal
  have hc:Cmp.CLocal (comparator tr) 0 pub:=hlocal.constr
  have cx:cv (comparator tr) 0 q Cmp.colX=x.toNat := by rw [←ex];rfl
  have cy:cv (comparator tr) 0 q Cmp.colY=y.toNat := by rw [←ey];rfl
  have cb:(comparator tr).cell 0 q Cmp.colB=b := eb
  rcases Cmp.cmp_row hc hq (by rw [cx];exact hx) (by rw [cy];exact hy) with ⟨hb,ho⟩|⟨hb,ho⟩
  · left
    refine ⟨?_,by rw [←cx,←cy];exact ho⟩
    rw [←cb]
    rw [←Fp.ofNat_toNat ((comparator tr).cell 0 q Cmp.colB)]
    change Fp.ofNat (cv (comparator tr) 0 q Cmp.colB)=1
    rw [hb];rfl
  · right
    refine ⟨?_,by rw [←cx,←cy];exact ho⟩
    rw [←cb]
    rw [←Fp.ofNat_toNat ((comparator tr).cell 0 q Cmp.colB)]
    change Fp.ofNat (cv (comparator tr) 0 q Cmp.colB)=0
    rw [hb];rfl

theorem prior_ge {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {t r : Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i : Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=40) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) {x y : Fp} (hmsg:i.msgVal tr t r pub=[x,y,1])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :y.toNat≤x.toNat := by
  rcases sound view hpub ht hr hi hb hs hm hmsg hx hy with h|h
  · exact h.2
  · have hn:(1:Fp)≠0 := by decide +kernel
    exact (hn h.1).elim
end ZkFormal.NearV3.Candidates.ProcessRepairComparatorSound
