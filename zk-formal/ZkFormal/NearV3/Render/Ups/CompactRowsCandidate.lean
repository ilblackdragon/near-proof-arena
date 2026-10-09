import ZkFormal.NearV3.Render.Ups.CodecRelayCandidate
import ZkFormal.NearV3.Render.Ups.AcceptedTrafficList

/-! Isolated row allocation for the codec-relay repair. This removes redundant
fresh-value rows; it does not claim the old UPS transition constraints hold on it. -/
namespace ZkFormal.NearV3.Render.UpsRelay
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3.Assembly UpsGen

def compactRecsI (I : UpsInst) : List RK :=
  (List.range 4).map RK.w ++
    (List.range (nQ I)).flatMap fun k=>(List.range (part I k).q.length).map (RK.q k)
def compactR (insts : List UpsInst) : Nat := (insts.map fun I=>(compactRecsI I).length).sum

theorem compactRecsI_length (I : UpsInst) :
    (compactRecsI I).length+L I=(recsI I).length := by
  simp only [compactRecsI,recsI,List.length_append,List.length_map,List.length_range,
    List.length_flatMap]
  omega

private theorem charges_sum (us : List SchedulerUpsertWitness) :
    (us.map (fun u=>4+outputByteCharge u.run)).sum=
      4*us.length+(us.map (fun u=>outputByteCharge u.run)).sum := by
  induction us with
  | nil => simp
  | cons u us ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

/-- Exact reduced row count of the same native allocation. -/
theorem compact_rows_exact {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I) :
    compactR insts=4*us.length+(us.map (fun u=>outputByteCharge u.run)).sum := by
  have hm : insts.map (fun I=>(compactRecsI I).length)=us.map (fun u=>4+outputByteCharge u.run) := by
    apply List.ext_getElem (by simpa using hl)
    intro i hi hu
    simp only [List.length_map] at hi hu
    simp only [List.getElem_map]
    have hh := ha i us[i] insts[i] (List.getElem?_eq_getElem hu) (List.getElem?_eq_getElem hi)
    have hcost := hh.2.2.2.2.2.2.1
    have he := compactRecsI_length insts[i]
    have hv : L insts[i]=(us[i]).value.length := by simp only [L,hh.2.2.2.1,List.length_map]
    omega
  unfold compactR
  rw [hm,charges_sum]

/-- Accepted input fits maxLog22 in the reduced row allocation, with all prior
native/SHA certificates preserved. Transition/extraction repair is still separate. -/
theorem checkD0a_compact_rows {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ (us : List SchedulerUpsertWitness) (insts : List UpsInst),
      1≤us.length ∧ us.length≤32 ∧ insts.length=us.length ∧ compactR insts+1≤2^22 ∧
      ∀ tau u I,us[tau]?=some u → insts[tau]?=some I →
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I := by
  obtain ⟨us,insts,hpos,hlen,hl,_,hout,_,ha⟩ := checkD0a_nativeTrafficList hk hw h baseI base
  refine ⟨us,insts,hpos,hlen,hl,?_,ha⟩
  rw [compact_rows_exact hl (fun tau u I hu hI=>(ha tau u I hu hI).1)]
  exact compact_rows_fit hlen hout
end ZkFormal.NearV3.Render.UpsRelay
