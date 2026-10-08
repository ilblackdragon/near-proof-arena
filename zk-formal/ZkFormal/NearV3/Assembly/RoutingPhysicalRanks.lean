import ZkFormal.NearV3.Assembly.RoutingCounterTraffic

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- The exact four field elements carried by a physical routing request,
represented canonically as naturals. -/
def physicalBoundaryKey (tr : Trace Fp) (t r : Nat) : Msg :=
  [(65*tr.cell t r q+tr.cell t r iB).toNat,
    (tr.cell t r loB).toNat,(tr.cell t r hiB).toNat,(tr.cell t r hnB).toNat]

def selectedBoundary (tr : Trace Fp) (t : Nat) (key : Msg) (r : Nat) : Bool :=
  decide (tr.cell t r gBd=1) && (physicalBoundaryKey tr t r==key)

def physicalBoundaryRank (tr : Trace Fp) (t r : Nat) : Nat :=
  (List.range r).countP (selectedBoundary tr t (physicalBoundaryKey tr t r))

def physicalBoundaryUsers (tr : Trace Fp) (t : Nat) (key : Msg) : Nat :=
  (List.range (tr.height t)).countP (selectedBoundary tr t key)

def physicalRanksFor (tr : Trace Fp) (t : Nat) (key : Msg) : List Nat :=
  (List.range (tr.height t)).filterMap (fun r=>
    if selectedBoundary tr t key r then some (physicalBoundaryRank tr t r) else none)

private theorem range_count_ranks (p : Nat→Bool) (n : Nat) :
    (List.range n).filterMap (fun r=>if p r then some ((List.range r).countP p) else none)=
      List.range' 0 ((List.range n).countP p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filterMap_append,ih,List.countP_append]
    cases h : p n <;> simp [h,List.range'_1_concat]

theorem physicalRanksFor_exact (tr : Trace Fp) (t : Nat) (key : Msg) :
    physicalRanksFor tr t key=List.range' 0 (physicalBoundaryUsers tr t key) := by
  rw [physicalBoundaryUsers,←range_count_ranks]
  unfold physicalRanksFor
  congr 1
  funext r
  by_cases hs : selectedBoundary tr t key r=true
  · have hk : physicalBoundaryKey tr t r=key := by
      simpa only [selectedBoundary,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
        (show (tr.cell t r gBd=1) ∧ physicalBoundaryKey tr t r=key from by
          simpa only [selectedBoundary,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using hs).2
    simp [hs,physicalBoundaryRank,hk]
  · have hf : selectedBoundary tr t key r=false := by
      cases he : selectedBoundary tr t key r <;> simp_all
    simp [hf]

theorem physicalBoundaryRank_bound (tr : Trace Fp) (t r : Nat) :
    physicalBoundaryRank tr t r≤r := by
  have := List.countP_le_length (p:=selectedBoundary tr t (physicalBoundaryKey tr t r))
    (l:=List.range r)
  simpa [physicalBoundaryRank] using this

theorem physicalBoundaryRank_field {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL : TableLocal candidateTable tr t pub) (hr : r<tr.height t) :
    physicalBoundaryRank tr t r<P := by
  have hh := height_le (local_base hL)
  have hb := physicalBoundaryRank_bound tr t r
  unfold P;omega

theorem physical_counter_chain (tr : Trace Fp) (t : Nat) (key : Msg) :
    (key++[0])::((physicalRanksFor tr t key).map (fun u=>key++[u+1]))=
      (physicalRanksFor tr t key).map (fun u=>key++[u])++[key++[physicalBoundaryUsers tr t key]] := by
  rw [physicalRanksFor_exact]
  have h : 0::(List.range' 0 (physicalBoundaryUsers tr t key)).map (·+1)=
      List.range' 0 (physicalBoundaryUsers tr t key)++[physicalBoundaryUsers tr t key] := by
    rw [←List.range'_succ_left]
    simpa only [List.range'_succ,Nat.zero_add] using
      List.range'_1_concat (s:=0) (n:=physicalBoundaryUsers tr t key)
  simpa only [List.map_cons,List.map_map,List.map_append,List.map_nil,Function.comp_def] using
    congrArg (List.map (fun u=>key++[u])) h

theorem ranked_trace_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal candidateTable tr t pub) :
    TableLocal candidateTable (counterPatch tr t (physicalBoundaryRank tr t)) t pub :=
  counterPatch_local hL _

end ZkFormal.NearV3.Assembly.RoutingQCandidate
