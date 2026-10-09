import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
import ZkFormal.Near.Extract.BusCount
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorRouting
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorComparatorRoutedFamily

theorem other_row (xs : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (bus : Nat) (h69:bus≠69) (h40:bus≠40) (sd : Bool) :
    rowTraffic (xs.map route) tr t r pub bus sd=rowTraffic xs tr t r pub bus sd := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    simp only [List.map_cons,rowTraffic,List.flatMap_cons] at ih ⊢
    rw [ih]
    by_cases hi:i.bus=69
    · simp [route,hi,h69.symm,h40.symm,ZkFormal.NearV3.Sched.B_SCMP]
    · simp [route,hi]

/-- Every prior comparison occurrence is merged with the existing comparator
requests; none is dropped or deduplicated. Equality is of natural counts. -/
theorem shared_row (xs : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sd : Bool) (msg : List Fp) :
    (rowTraffic (xs.map route) tr t r pub 40 sd).count msg=
      (rowTraffic xs tr t r pub 40 sd).count msg+(rowTraffic xs tr t r pub 69 sd).count msg := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    simp only [List.map_cons,rowTraffic,List.flatMap_cons,List.count_append] at ih ⊢
    rw [ih]
    by_cases hi:i.bus=69
    · simp [route,hi,ZkFormal.NearV3.Sched.B_SCMP,Interaction.multNat,Interaction.msgVal]
      omega
    · by_cases hj:i.bus=40
      · simp [route,hj]
        omega
      · simp [route,hi,hj]

theorem other_count (xs : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (h69:bus≠69) (h40:bus≠40) (sd : Bool) (msg : List Fp) :
    tableBusCount (xs.map route) tr t pub bus sd msg=tableBusCount xs tr t pub bus sd msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  simp only [other_row xs tr t _ pub bus h69 h40 sd]

theorem shared_count (xs : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (sd : Bool) (msg : List Fp) :
    tableBusCount (xs.map route) tr t pub 40 sd msg=
      tableBusCount xs tr t pub 40 sd msg+tableBusCount xs tr t pub 69 sd msg := by
  simp only [tableBusCount_eq]
  have all (rs : List Nat) :
      (rs.flatMap (fun r=>rowTraffic (xs.map route) tr t r pub 40 sd)).count msg=
      (rs.flatMap (fun r=>rowTraffic xs tr t r pub 40 sd)).count msg+
      (rs.flatMap (fun r=>rowTraffic xs tr t r pub 69 sd)).count msg := by
    induction rs with
    | nil=>rfl
    | cons r rs ih=>
      simp only [List.flatMap_cons,List.count_append,shared_row,ih]
      omega
  exact all _
/-- Retagging comparisons preserves all local constraints and multiplicity
bit checks. Global bus balance is transported separately by the count lemmas. -/
theorem local_iff (T : Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    TableLocal (routeTable T) tr t pub ↔ TableLocal T tr t pub := by
  constructor
  · rintro ⟨hl,hu,hc,hb⟩
    refine ⟨hl,hu,hc,?_⟩
    intro r hr i hi e he
    apply hb r hr (route i) (List.mem_map.mpr ⟨i,hi,rfl⟩) e
    simpa only [route_mult] using he
  · rintro ⟨hl,hu,hc,hb⟩
    refine ⟨hl,hu,hc,?_⟩
    intro r hr i hi e he
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
    rw [route_mult] at he
    exact hb r hr j hj e he
end ZkFormal.NearV3.Candidates.ProcPriorComparatorRouting
