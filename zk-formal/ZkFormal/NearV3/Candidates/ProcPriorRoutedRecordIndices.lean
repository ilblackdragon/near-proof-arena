import ZkFormal.NearV3.Candidates.ProcPriorRecordEndpoint
import ZkFormal.NearV3.Candidates.ProcPriorRoutedIdBound
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordIndices
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def recordTrace (tr:Trace Fp):Trace Fp:=HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr
def col (b:Bool):Nat:=if b then sender else receiver
def found (b:Bool):Nat:=if b then senderFound else receiverFound
def index (b:Bool):Nat:=if b then senderIndex else receiverIndex
def vertical (b:Bool):Interaction:=ProcPriorVertical4Linear.interaction 3
  (ProcPriorRecordLinear.interactions 75 71 72 67 76)[if b then 4 else 5]!
def endpoint (b:Bool):Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset (vertical b)

theorem member (b:Bool):endpoint b∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hbase:(ProcPriorRecordLinear.interactions 75 71 72 67 76)[if b then 4 else 5]!∈ProcPriorRecordLinear.interactions 75 71 72 67 76 := by
    have hb:(if b then 4 else 5)<(ProcPriorRecordLinear.interactions 75 71 72 67 76).length := by cases b <;> decide +kernel
    rw [getElem!_pos (ProcPriorRecordLinear.interactions 75 71 72 67 76) (if b then 4 else 5) hb];exact List.getElem_mem hb
  have hv:vertical b∈ProcPriorCodecActualFamily.overlay.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRecordLinear.table 75 71 72 67 76,3),by simp [ProcPriorCodecActualFamily.components,ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨_,hbase,rfl⟩
  have hroute:ProcPriorComparatorRoutedFamily.route (vertical b)=vertical b := by cases b <;> rfl
  have hraw:endpoint b∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,ProcPriorRoutedFamilyWrite.overlay_location,?_⟩
    apply List.mem_map.mpr
    refine ⟨vertical b,?_,rfl⟩
    exact List.mem_map.mpr ⟨vertical b,hv,hroute⟩
  have hp:endpoint b∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠endpoint b := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (s:Bool):InteractionTriples.dummy s≠endpoint b := by
    intro he
    have hb:=congrArg Interaction.bus he
    cases b <;> change 0=72 at hb <;> omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠endpoint b) (hd true) (hd false)).mp hall) _ hp rfl

theorem message (b:Bool) (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    (endpoint b).msgVal tr t r pub=(vertical b).msgVal (recordTrace tr) t r pub := by
  simp only [endpoint,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem mult (b:Bool) (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    (endpoint b).multNat tr t r pub=(vertical b).multNat (recordTrace tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (recordTrace tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)

theorem live {tr:Trace Fp} {t r:Nat} {pub:List Fp} (b:Bool)
    (hs:cv (recordTrace tr) t r (ProcPriorVertical4Linear.stage 3)=1)
    (hc:cv (recordTrace tr) t r (col b)=1) (ht:cv (recordTrace tr) t r topLimb=1) :
    (endpoint b).multNat tr t r pub≠0 := by
  rw [mult]
  have hcell (x:Nat) (hx:cv (recordTrace tr) t r x=1):(recordTrace tr).cell t r x=Fp.ofNat 1 := by
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  have h1:=hcell _ hs
  have h2:=hcell _ hc
  have h3:=hcell _ ht
  cases b <;>
    change (if (recordTrace tr).cell t r (ProcPriorVertical4Linear.stage 3)*
      ((recordTrace tr).cell t r topLimb*(recordTrace tr).cell t r _)=1 then 1 else 0)+0≠0
  all_goals simp only [col,Bool.false_eq_true,if_false,if_true] at h2
  all_goals rw [h1,h2,h3];decide +kernel

theorem endpoint64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (ha:ProcPriorIdSoundBound.PublicSendBound AP tr pub 64)
    (h70:∀msg,pubCount AP pub 70 true msg=0) (h72:∀msg,pubCount AP pub 72 true msg=0)
    (b:Bool) {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hc:cv (recordTrace tr) 0 r (col b)=1) (ht:cv (recordTrace tr) 0 r topLimb=1)
    (hf:cv (recordTrace tr) 0 r (found b)=1) :cv (recordTrace tr) 0 r (index b)<64 := by
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:endpoint b∈AP.tables[0]!.interactions := by rw [htables];exact member b
  have hfound:((endpoint b).msgVal tr 0 r pub)[2]! =Fp.ofNat 1 := by
    rw [message]
    have hcell:(recordTrace tr).cell 0 r (found b)=Fp.ofNat 1 := by rw [←hf];exact (Fp.ofNat_toNat _).symm
    cases b <;> exact hcell
  have hb:=ProcPriorRoutedIdBound.result_bound hH htables 64 h70 ha h72 ht0 hr hi
    (show (endpoint b).bus=72 by cases b <;> rfl) (show (endpoint b).send=false by cases b <;> rfl)
    (live b hs hc ht) hfound
  rw [message] at hb
  cases b <;> exact hb

theorem write_indices {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (ha:ProcPriorIdSoundBound.PublicSendBound AP tr pub 64)
    (h70:∀msg,pubCount AP pub 70 true msg=0) (h72:∀msg,pubCount AP pub 72 true msg=0)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv (recordTrace tr) 0 r writeGate=1) :
    cv (recordTrace tr) 0 r senderIndex<64 ∧ cv (recordTrace tr) 0 r receiverIndex<64 := by
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht0
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  obtain ⟨hac,hsen,hrecv,hamt,hfirst,hmid,htop,hsf,hrf⟩:=ProcPriorRecordGeometry.write_shape hv hr hs hw
  obtain ⟨s,hsr,hss,hsc,hst,hsfound,hsindex⟩:=ProcPriorRecordEndpoint.sender_origin hv r hr hs hac (by omega) hsen
  obtain ⟨v,hvr,hvs,hvc,hvt,hvfound,hvindex⟩:=ProcPriorRecordEndpoint.receiver_origin hv r hr hs hac hamt
  have hsbound:=endpoint64 hH htables ha h70 h72 true (show s<tr.height 0 by omega) hss hsc hst (hsfound.trans hsf)
  have hvbound:=endpoint64 hH htables ha h70 h72 false (show v<tr.height 0 by omega) hvs hvc hvt (hvfound.trans hrf)
  change cv (recordTrace tr) 0 s senderIndex=cv (recordTrace tr) 0 r senderIndex at hsindex
  change cv (recordTrace tr) 0 v receiverIndex=cv (recordTrace tr) 0 r receiverIndex at hvindex
  change cv (recordTrace tr) 0 s senderIndex<64 at hsbound
  change cv (recordTrace tr) 0 v receiverIndex<64 at hvbound
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordIndices
