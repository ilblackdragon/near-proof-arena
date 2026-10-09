import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaView
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedShaFacts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

def count (tr:Trace Fp) (pub:List Fp) (j:Nat) (dir:Bool) (b:Nat) (msg:List Fp):Nat:=
  tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
    (ProcPriorRoutedShaView.sha j tr) 0 pub b dir msg

theorem facts (j:Nat) (hj:j<4) {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ShaFacts (count tr pub j true) (count tr pub j false) := by
  have he (dir:Bool):count tr pub j dir=
      Assembly.shaCountAt (ShaPackingTrace.decodeTrace (ProcPriorRoutedShaView.sha j tr)) pub 0 dir := by
    funext b msg
    exact ShaPackingTrace.table_traffic _ 0 B_BYTES B_DIGEST b pub msg dir
  rw [he true,he false]
  exact ProcPriorRoutedShaView.facts j hj hH htables

def sumCount (tr:Trace Fp) (pub:List Fp):List Nat→Bool→Nat→List Fp→Nat
  | [],_,_,_=>0
  | j::js,dir,b,msg=>count tr pub j dir b msg+sumCount tr pub js dir b msg

/-- Checked SHA semantics for the actual four installed physical projections,
without honest/generated job lists or a supplied hash oracle. -/
theorem union_facts {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (js:List Nat) (hjs:∀j∈js,j<4) :
    ShaFacts (sumCount tr pub js true) (sumCount tr pub js false) := by
  induction js with
  | nil=>
    refine ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,?_⟩
    intro m hm;cases hm
  | cons j js ih=>
    have hh:=facts j (hjs j (by simp)) hH htables
    have ht:=ih (fun k hk=>hjs k (by simp [hk]))
    refine ⟨?_,?_,?_⟩
    · intro b m hb
      simp only [sumCount,hh.sends_only_digest b m hb,ht.sends_only_digest b m hb]
    · intro b m hb
      simp only [sumCount,hh.recvs_only_bytes b m hb,ht.recvs_only_bytes b m hb]
    · intro m hm
      by_cases hp:0<count tr pub j true B_DIGEST m
      · obtain ⟨id,bs,he,hbytes⟩:=hh.digest m hp
        refine ⟨id,bs,he,?_⟩
        intro i hi;have hb:=hbytes i hi
        simp only [sumCount];omega
      · have hp':0<sumCount tr pub js true B_DIGEST m := by simp only [sumCount] at hm;omega
        obtain ⟨id,bs,he,hbytes⟩:=ht.digest m hp'
        refine ⟨id,bs,he,?_⟩
        intro i hi;have hb:=hbytes i hi
        simp only [sumCount];omega

theorem four {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ShaFacts (sumCount tr pub [0,1,2,3] true) (sumCount tr pub [0,1,2,3] false) :=
  union_facts hH htables _ (by intro j hj;simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj;omega)
end ZkFormal.NearV3.Candidates.ProcPriorRoutedShaFacts
