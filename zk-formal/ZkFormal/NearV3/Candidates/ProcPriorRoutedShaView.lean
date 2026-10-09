import ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadView
import ZkFormal.NearV3.Candidates.ShaPackingTrace
import ZkFormal.NearV3.Assembly.ShaUnionFacts
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedShaView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset (j:Nat):Nat:=((ProcPriorComparatorRoutedFamily.selected.take j).map (·.width)).sum
def sha (j:Nat) (tr:Trace Fp):Trace Fp:=HorizontalTrace.project (offset j) tr
def routed (i:Interaction):Interaction:=ProcPriorComparatorRoutedFamily.route
  i
def interaction (j:Nat) (i:Interaction):Interaction:=HorizontalTables.interaction (offset j) (routed i)

theorem location (j:Nat) (hj:j<4) :HorizontalTables.shifted (offset j)
    (ProcPriorComparatorRoutedFamily.routeTable (ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST))∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have hcases:j=0 ∨ j=1 ∨ j=2 ∨ j=3:=by omega
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[j]?=
    some (HorizontalTables.shifted (offset j)
      (ProcPriorComparatorRoutedFamily.routeTable (ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST))) := by rcases hcases with rfl | rfl | rfl | rfl <;> rfl
  exact List.mem_iff_getElem?.mpr ⟨j,he⟩

theorem constraint_member (j:Nat) (hj:j<4) {e:Expr} (he:e∈(ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST).constraints) :
    HorizontalTables.expression (offset j) e∈ProcPriorComparatorRoutedFamily.fused.constraints := by
  change _∈ProcPriorComparatorRoutedFamily.raw.constraints
  apply List.mem_flatMap.mpr
  refine ⟨_,location j hj,List.mem_map.mpr ⟨e,?_,rfl⟩⟩
  exact he

theorem mult_eq (i:Interaction):(routed i).mult=i.mult := by
  unfold routed
  rw [ProcPriorComparatorRoutedFamily.route_mult]


theorem member (j:Nat) (hj:j<4) {i:Interaction} (hi:i∈(ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST).interactions) :
    interaction j i∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hraw:interaction j i∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,location j hj,List.mem_map.mpr ⟨routed i,?_,rfl⟩⟩
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hp:interaction j i∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  have hallmult:(ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST).interactions.all (fun j=>decide (0<j.mult.length))=true := by decide +kernel
  have hb:0<i.mult.length := by simpa using List.all_eq_true.mp hallmult i hi
  apply Classical.byContradiction
  intro hn
  have hall:∀ii∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,ii≠interaction j i := by
    intro ii hii he;exact hn (he ▸ hii)
  have hd (b:Bool):InteractionTriples.dummy b≠interaction j i := by
    intro he
    have hh:=congrArg (fun j:Interaction=>j.mult.length) he
    change 0=((routed i).mult.map (HorizontalTables.expression (offset j))).length at hh
    rw [List.length_map,mult_eq] at hh
    omega
  exact ((InteractionTriples.forall_iff _ (fun ii=>ii≠interaction j i) (hd true) (hd false)).mp hall) _ hp rfl

/-- Each of four installed packed SHA components is locally valid on its actual projection. -/
theorem local_sha (j:Nat) (hj:j<4) {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal (ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST) (sha j tr) 0 pub := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused := by rw [htables];rfl
  refine ⟨(hH.logBound 0 ht).1,?_,?_,?_⟩
  · have hh:tr.log 0≤AP.tables[0]!.maxLog := by
      rw [getElem!_pos AP.tables 0 ht]
      exact (hH.logBound 0 ht).2
    rw [htab] at hh
    exact hh
  · intro r hr e he
    have hh:=local_of_holdsP hH ht r hr (HorizontalTables.expression (offset j) e)
    rw [htab] at hh
    have heq:=hh (constraint_member j hj he)
    rw [HorizontalTrace.expression_eval] at heq
    exact heq
  · intro r hr i hi b hb
    have him:interaction j i∈AP.tables[0]!.interactions := by rw [htab];exact member j hj hi
    have hbm:HorizontalTables.expression (offset j) b∈(interaction j i).mult := by
      change _∈(routed i).mult.map (HorizontalTables.expression (offset j))
      rw [mult_eq]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [getElem!_pos AP.tables 0 ht] at him
    have hh:=hH.bits 0 ht r hr _ him _ hbm
    rw [HorizontalTrace.expression_eval] at hh
    exact hh

theorem facts (j:Nat) (hj:j<4) {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.ShaFacts
      (Assembly.shaCountAt (ShaPackingTrace.decodeTrace (sha j tr)) pub 0 true)
      (Assembly.shaCountAt (ShaPackingTrace.decodeTrace (sha j tr)) pub 0 false) := by
  have hl:=ShaPackingTrace.decode_local (local_sha j hj hH htables)
  exact Assembly.shaFactsAt _ pub 0 ⟨hl.log_ge,hl.log_le,hl.constr⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedShaView
