import ZkFormal.NearV3.Assembly.RoutingBoundedPrep
import ZkFormal.NearV3.Rcpt.Render.BndRender

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air

def boundaryEntry (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) (x : Nat) : BndE :=
  let row := Public.boundaryRow bounds x
  ⟨x,(row.getD 0 0).toNat,(row.getD 1 0).toNat,(row.getD 2 0).toNat,
    requests.count ([x]++row.map UInt8.toNat)⟩

def boundaryEntries (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) : List BndE :=
  (List.range (65*bounds.length)).map (boundaryEntry bounds requests)

theorem boundaryEntry_record (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) (x : Nat) :
    (boundaryEntry bounds requests x).rec4=[x]++(Public.boundaryRow bounds x).map UInt8.toNat := by
  simp [boundaryEntry,BndE.rec4,Public.boundaryRow]

theorem boundaryEntry_usage (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) (x : Nat) :
    (boundaryEntry bounds requests x).U=requests.count (boundaryEntry bounds requests x).rec4 := by
  rw [boundaryEntry_record];rfl

theorem boundaryEntries_length (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) :
    (boundaryEntries bounds requests).length=65*bounds.length := by simp [boundaryEntries]

theorem boundaryEntries_records (p : Prep) (requests : List Msg) :
    (boundaryEntries p.bnds requests).map BndE.rec4=Public.boundaryRecords p := by
  simp only [boundaryEntries,List.map_map,Public.boundaryRecords]
  apply List.map_congr_left
  intro x _
  exact boundaryEntry_record _ _ _

theorem boundaryEntries_wf (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg)
    (hcap : 65*bounds.length≤2^13) (hr : requests.length<ZkFormal.Algebra.P) :
    BndWf (boundaryEntries bounds requests) := by
  refine ⟨?_,?_⟩
  · intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    have hx' := List.mem_range.mp hx
    have hbyte (i : Nat) : ((Public.boundaryRow bounds x).getD i 0).toNat<ZkFormal.Algebra.P := by
      have := ((Public.boundaryRow bounds x).getD i 0).toNat_lt
      unfold ZkFormal.Algebra.P;omega
    refine ⟨by change x<ZkFormal.Algebra.P; unfold ZkFormal.Algebra.P;omega,hbyte 0,hbyte 1,hbyte 2,?_⟩
    exact Nat.lt_of_le_of_lt (List.count_le_length) hr
  · rw [boundaryEntries_length];exact hcap

def boundaryTrace (bounds : List (Option Bytes×Option Bytes)) (requests : List Msg) : Trace Fp :=
  let es := boundaryEntries bounds requests
  ⟨fun _=>Near.Render.logOf es.length,fun _ r c=>Fp.ofNat (Render.BndGen.cell es r c)⟩

/-- Concrete honest boundary table over exactly the normalized public records.
Usage counters count actual request keys; their chain assignment on receipt rows
is separate from this provider construction. -/
theorem normalized_render {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (requests : List Msg) (hr : requests.length<ZkFormal.Algebra.P) (pub : List Fp) :
    let bounds := (boundedPrep p k.L k.H.shardId).bnds
    let es := boundaryEntries bounds requests
    BndWf es ∧
    es.map BndE.rec4=Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
    TableLocal BndV3.table (boundaryTrace bounds requests) 0 pub ∧
    TableTraffic BndV3.interactions (boundaryTrace bounds requests) 0 pub (bndTraffic es) := by
  dsimp only
  have hw := boundaryEntries_wf _ requests (native_capacity hp hk).2 hr
  refine ⟨hw,boundaryEntries_records _ _,?_,?_⟩
  · exact Render.bnd_render_local _ hw.rows _ 0 pub rfl (fun _ _ _ _=>rfl)
  · exact Render.bnd_render_traffic _ _ 0 pub rfl (fun _ _ _ _=>rfl)

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
