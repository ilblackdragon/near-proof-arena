import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Render.NodeRender
import ZkFormal.NearV3.Render.UniqRender
import ZkFormal.NearV3.Render.WalkRender

/-! Concrete aligned trie generators. The local and traffic proofs apply to
array-backed traces, including padding and cyclic next-row reads. Assembly
must still connect these arrays to the other tables and discharge HoldsP. -/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size

def nodeTraceAligned (vs : List NodeS3) : Trace Fp :=
  let log := padLog22 (logOf ((vs.map fun s => (s.v.ser false).length).sum + 1))
  rowsTrace log (mkTab (2 ^ log) NodeV3.width (NodeGen3.cell vs (2 ^ log)))

/-- Local constraints and exact traffic at the aligned height. -/
theorem node_aligned_complete (vs : List NodeS3) (hok : NodeOk vs) (t : Nat) (pub : List Fp) :
    TableLocal NodeV3.table (nodeTraceAligned vs) t pub ∧
    TableTraffic NodeV3.interactions (nodeTraceAligned vs) t pub (nodeTraffic3 vs) ∧
    (nodeTraceAligned vs).log t % 3 = 1 := by
  have hh := padded_log_fits ((vs.map fun s => (s.v.ser false).length).sum + 1) (hok.rows)
  have hcell : ∀ r x, r < (nodeTraceAligned vs).height t → x < NodeV3.width →
      (nodeTraceAligned vs).cell t r x = Fp.ofNat
        (NodeGen3.cell vs ((nodeTraceAligned vs).height t) r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨node_render_local_at vs hok _ t pub 22 ⟨hh.2.1, hh.2.2.1⟩ hh.1 hcell,
    node_render_traffic_at vs hok _ t pub hh.1 hcell, hh.2.2.2⟩

def uniqTraceAligned (L : List UEnt) : Trace Fp :=
  let log := padLog22 (logOf (32 * L.length))
  rowsTrace log (mkTab (2 ^ log) Uniq.width (UniqGen.cell L (2 ^ log)))

/-- Local constraints and exact traffic at the aligned height. -/
theorem uniq_aligned_complete (L : List UEnt) (hok : UOk L) (t : Nat) (pub : List Fp) :
    TableLocal Uniq.table (uniqTraceAligned L) t pub ∧
    TableTraffic Uniq.interactions (uniqTraceAligned L) t pub (uniqTraffic (uniqEntries L)) ∧
    (uniqTraceAligned L).log t % 3 = 1 := by
  have hh := padded_log_fits (32 * L.length) (hok.cap)
  have hcell : ∀ r x, r < (uniqTraceAligned L).height t → x < Uniq.width →
      (uniqTraceAligned L).cell t r x = Fp.ofNat
        (UniqGen.cell L ((uniqTraceAligned L).height t) r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨uniq_render_local_at L hok _ t pub 22 ⟨hh.2.1, hh.2.2.1⟩ hh.1 hcell,
    uniq_render_traffic_at L hok _ t pub hh.1 hcell, hh.2.2.2⟩

def walkTraceAligned (ws : List WalkR) : Trace Fp :=
  let log := padLog22 (logOf (rows ws))
  rowsTrace log (mkTab (2 ^ log) WalkV3.width (WalkGen.cell ws (2 ^ log)))

/-- Local constraints and exact traffic at the aligned height. -/
theorem walk_aligned_complete (ws : List WalkR) (hok : WalkOk ws) (t : Nat) (pub : List Fp) :
    TableLocal { WalkV3.table with maxLog := 22 } (walkTraceAligned ws) t pub ∧
    TableTraffic WalkV3.interactions (walkTraceAligned ws) t pub (walkTraffic3 ws) ∧
    (walkTraceAligned ws).log t % 3 = 1 := by
  have hh := padded_log_fits (rows ws) (Nat.le_trans hok.cap (by decide))
  have hcell : ∀ r x, r < (walkTraceAligned ws).height t → x < WalkV3.width →
      (walkTraceAligned ws).cell t r x = Fp.ofNat
        (WalkGen.cell ws ((walkTraceAligned ws).height t) r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨walk_render_local_at ws hok _ t pub 22 ⟨hh.2.1, hh.2.2.1⟩ hh.1 hcell,
    walk_render_traffic_at ws hok _ t pub hh.1 hcell, hh.2.2.2⟩

end ZkFormal.NearV3.Render
