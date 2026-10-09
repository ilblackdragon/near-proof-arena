import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicRow
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdRequestRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedFamilyId
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
def requestRead : Interaction:=HorizontalTables.interaction offset
  (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[1]!))

theorem member :requestRead∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions := by
  have hf:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==71 && !i.send)=[requestRead]:=rfl
  have hr:requestRead∈ProcPriorComparatorRoutedFamily.raw.interactions:=
    (List.mem_filter.mp (hf ▸ List.mem_singleton_self requestRead)).1
  have hp:requestRead∈ProcPriorComparatorRoutedFamily.paired.interactions:=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hr
  apply Classical.byContradiction
  intro hn
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠requestRead:=by
    intro j hj he;subst j;exact hn hj
  have hd (b : Bool) : InteractionTriples.dummy b≠requestRead:=by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=71 at hb
    omega
  have hh':∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j≠requestRead:=
    (InteractionTriples.forall_iff _ _ (hd true) (hd false)).mp hh
  exact hh' requestRead hp rfl


theorem live {tr:Trace Fp} {r:Nat} {pub:List Fp}
    (hs:cv (HorizontalTrace.project offset tr) 0 r (ProcPriorVertical4Linear.stage 1)=1)
    (ha:cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.act=1)
    (hp:cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.isPublic=0) :
    requestRead.multNat tr 0 r pub≠0 := by
  let pt:=HorizontalTrace.project offset tr
  have he:=HorizontalTraffic.mult_map (HorizontalTables.expression offset)
    (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[1]!)).mult
    tr pt 0 r 0 pub (by intro e he;exact HorizontalTrace.expression_eval tr 0 r offset pub e)
  change requestRead.multNat tr 0 r pub=_ at he
  rw [he]
  have h: (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[1]!)).multNat pt 0 r pub=1 := by
    apply Codec.mult_of rfl
    change zev (tenv pt 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (ProcPriorIdTable.notE (c ProcPriorIdTable.isPublic))))=1
    simp only [ProcPriorIdTable.notE,zev_mul,zev_sub,zev_k,zev_c,cur_cv,pt,hs,ha,hp]
    rfl
  change (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[1]!)).multNat pt 0 r pub≠0
  rw [h];omega

theorem message (tr:Trace Fp) (r:Nat) (pub:List Fp) :
    requestRead.msgVal tr 0 r pub=
      [Fp.ofNat (cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.tau),
       Fp.ofNat (cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.ordinal),
       Fp.ofNat (cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.keyLo),
       Fp.ofNat (cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.keyMid),
       Fp.ofNat (cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.keyHi)] := by
  simp only [requestRead,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  change [(HorizontalTables.expression offset (c ProcPriorIdTable.tau)).eval tr 0 r pub,
    (HorizontalTables.expression offset (c ProcPriorIdTable.ordinal)).eval tr 0 r pub,
    (HorizontalTables.expression offset (c ProcPriorIdTable.keyLo)).eval tr 0 r pub,
    (HorizontalTables.expression offset (c ProcPriorIdTable.keyMid)).eval tr 0 r pub,
    (HorizontalTables.expression offset (c ProcPriorIdTable.keyHi)).eval tr 0 r pub]=_
  simp only [HorizontalTrace.expression_eval,Codec.ev_c]
end ZkFormal.NearV3.Candidates.ProcessRepairIdRequestRows
