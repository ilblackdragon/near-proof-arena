import ZkFormal.NearV3.Public.PreparedFit

/-! Concrete public-bus indexing for the packed NEAR prepared statement. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

def recordNats (plan : PubSeg) (j : Nat) (row : ByteString) : List Nat :=
  plan.msgPrefix ++ (match plan.indexBase with | none => [] | some off => [off+j]) ++
    row.map UInt8.toNat

theorem recordNats_field (plan : PubSeg) (j : Nat) (row : ByteString) :
    (recordNats plan j row).map Fp.ofNat = recordValues plan j row := by
  cases h : plan.indexBase <;>
    simp only [recordNats,recordValues,h,List.map_append,List.map_map,List.map_nil,List.map_cons] <;> rfl

def segmentIndex (seg : PubSeg) : Nat := (seg.countAt-202)/8

def preparedRecords (p : Prep) (seg : PubSeg) : List (List Nat) :=
  let rows := (preparedBlocks p).getD (segmentIndex seg) []
  (List.range rows.length).map (fun j => recordNats seg j (rows.getD j []))

theorem descriptor_index (plan : PubSeg) (i : Nat) :
    segmentIndex (descriptor plan 202 i) = i := by
  simp only [segmentIndex,descriptor]
  omega

theorem prepared_segment_msgs (p : Prep) (witnessOverhead : Nat)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4)
    (seg : PubSeg) (hseg : seg ∈ preparedSegments) :
    seg.msgs (ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)) =
      (preparedRecords p seg).map (·.map Fp.ofNat) := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hseg
  have hi : i < 9 := List.mem_range.mp hi
  have hbi : i < (preparedBlocks p).length := by rw [preparedBlocks_length]; exact hi
  obtain ⟨hn,ho⟩ := descriptor_u32_bounds (plans.getD i sourcePlan) _ _ hbi
    (plan_width_positive hi) (prepared_width p hr hs hi) hlen
  unfold preparedRecords
  rw [descriptor_index]
  change (descriptor (plans.getD i sourcePlan) 202 i).msgs
      (ZkFormal.Udr.pubOf Fp (encode (headerBytes p witnessOverhead) (preparedBlocks p))) = _
  rw [← headerBytes_length p witnessOverhead hr,
    descriptor_msgs _ _ _ hbi hn (prepared_width p hr hs hi) ho,List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [recordNats_field]
  rfl

/-- Assembly supplies its actual AIR tables and these fixed public segments.
No public-bus record multiplicity premise remains. -/
def prepared_pubIdx (AP : AirP) (p : Prep) (witnessOverhead : Nat)
    (hseg : AP.pubSegs = preparedSegments)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) :
    PubIdx AP (ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)) Fp.ofNat := by
  apply pubIdx_of_segments AP _ Fp.ofNat (preparedRecords p)
  intro seg hmem
  apply prepared_segment_msgs p witnessOverhead hr hs hlen seg
  rwa [hseg] at hmem

def preparedOn (p : Prep) (bus : Nat) (side : Bool) : List (List Nat) :=
  (preparedSegments.filter (fun seg => decide (seg.bus=bus ∧ seg.send=side))).flatMap (preparedRecords p)

theorem prepared_pubIdx_recs (AP : AirP) (p : Prep) (witnessOverhead : Nat)
    (hseg : AP.pubSegs = preparedSegments)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) (bus : Nat) (side : Bool) :
    (prepared_pubIdx AP p witnessOverhead hseg hr hs hlen).recs bus side = preparedOn p bus side := by
  change (AP.pubSegs.filter _).flatMap (preparedRecords p) = _
  rw [hseg]
  rfl

theorem preparedOn_source (p : Prep) :
    preparedOn p B_SRC true = preparedRecords p (descriptor sourcePlan 202 0) := by
  change preparedRecords p (descriptor sourcePlan 202 0) ++ [] = _
  exact List.append_nil _

theorem preparedOn_boundary (p : Prep) :
    preparedOn p B_BNDP true = preparedRecords p (descriptor boundaryPlan 202 1) := by
  change preparedRecords p (descriptor boundaryPlan 202 1) ++ [] = _
  exact List.append_nil _

theorem preparedOn_body (p : Prep) :
    preparedOn p 0 false = preparedRecords p (descriptor bodyPlan 202 2) := by
  change preparedRecords p (descriptor bodyPlan 202 2) ++ [] = _
  exact List.append_nil _

end ZkFormal.NearV3.Public
