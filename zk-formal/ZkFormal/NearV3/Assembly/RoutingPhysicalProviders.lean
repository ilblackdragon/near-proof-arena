import ZkFormal.NearV3.Assembly.RoutingPhysicalMessages
import ZkFormal.NearV3.Assembly.RoutingBoundedRender

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open RoutingBoundedLayout

def physicalActiveRows (tr : Trace Fp) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter (fun r=>decide (tr.cell t r gBd=1))

def physicalBoundaryKeys (tr : Trace Fp) (t : Nat) : List Msg :=
  (physicalActiveRows tr t).map (physicalBoundaryKey tr t)

theorem physicalBoundaryKeys_count (tr : Trace Fp) (t : Nat) (key : Msg) :
    (physicalBoundaryKeys tr t).count key=physicalBoundaryUsers tr t key := by
  simp only [physicalBoundaryKeys,physicalActiveRows,List.count_eq_countP,List.countP_map,
    List.countP_filter,physicalBoundaryUsers,Function.comp_def]
  apply List.countP_congr
  intro r _
  simp [selectedBoundary,Bool.and_comm]

theorem physicalBoundaryKeys_length (tr : Trace Fp) (t : Nat) :
    (physicalBoundaryKeys tr t).length≤tr.height t := by
  simpa [physicalBoundaryKeys,physicalActiveRows] using
    List.length_filter_le (fun r=>decide (tr.cell t r gBd=1)) (List.range (tr.height t))

theorem physicalBoundaryKeys_bound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal candidateTable tr t pub) : (physicalBoundaryKeys tr t).length<P := by
  have hh := height_le (local_base hL)
  have hl := physicalBoundaryKeys_length tr t
  unfold P;omega

theorem physicalEntries_usage (bounds : List (Option NearSpec.Bytes×Option NearSpec.Bytes))
    (tr : Trace Fp) (t x : Nat) :
    (boundaryEntry bounds (physicalBoundaryKeys tr t) x).U=
      physicalBoundaryUsers tr t (boundaryEntry bounds (physicalBoundaryKeys tr t) x).rec4 := by
  rw [boundaryEntry_usage,physicalBoundaryKeys_count]

theorem boundaryEntries_nodup (bounds : List (Option NearSpec.Bytes×Option NearSpec.Bytes))
    (keys : List Msg) : ((boundaryEntries bounds keys).map BndE.rec4).Nodup := by
  rw [boundaryEntries,List.map_map]
  have inj : Function.Injective (BndE.rec4 ∘ boundaryEntry bounds keys) := by
    intro x y he
    have h := congrArg List.head? he
    simpa [Function.comp_def,BndE.rec4,boundaryEntry] using h
  have go : ∀rs : List Nat,rs.Nodup → (rs.map (BndE.rec4 ∘ boundaryEntry bounds keys)).Nodup := by
    intro rs
    induction rs with
    | nil => simp
    | cons x rs ih =>
      intro hn
      simp only [List.nodup_cons] at hn
      simp only [List.map_cons,List.nodup_cons]
      refine ⟨?_,ih hn.2⟩
      intro hm
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
      exact hn.1 (inj he ▸ hy)
  exact go _ List.nodup_range

theorem physicalEntries_usage_all (bounds : List (Option NearSpec.Bytes×Option NearSpec.Bytes))
    (tr : Trace Fp) (t : Nat) :
    ∀e∈boundaryEntries bounds (physicalBoundaryKeys tr t),e.U=physicalBoundaryUsers tr t e.rec4 := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact physicalEntries_usage bounds tr t x

/-- The same physical receipt trace provides the exact endpoint use counts;
the native preparation provides the normalized provider rows and capacity. -/
theorem physical_provider_render {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint}
    {p : NearSpecV3.Prep} {k : NearSpecV3.WalkD0}
    (hp : NearSpecV3.prepD0 cb hint=.ok p) (hk : NearSpecV3.walkD0 cb=.ok k)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : TableLocal candidateTable tr t pub) :
    let bounds := (boundedPrep p k.L k.H.shardId).bnds
    let es := boundaryEntries bounds (physicalBoundaryKeys tr t)
    BndWf es ∧ es.map BndE.rec4=Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
    TableLocal BndV3.table (boundaryTrace bounds (physicalBoundaryKeys tr t)) 0 pub ∧
    TableTraffic BndV3.interactions (boundaryTrace bounds (physicalBoundaryKeys tr t)) 0 pub (bndTraffic es) :=
  normalized_render hp hk _ (physicalBoundaryKeys_bound hL) pub

end ZkFormal.NearV3.Assembly.RoutingQCandidate
