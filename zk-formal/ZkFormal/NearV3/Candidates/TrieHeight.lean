import ZkFormal.NearV3.Render.PaddedTrie
namespace ZkFormal.NearV3.Candidates.TrieHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render

/-- These native cell builders take the actual physical height, so SUM rows and
cyclic successors are generated at22 rather than copied from a shorter trace. -/
def node (vs : List NodeS3) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat (NodeGen3.cell vs (2^22) r c)⟩
def value (es : List ValE) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat (ValGen.cell es (2^22) r c)⟩
def uniq (es : List UEnt) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat (UniqGen.cell es (2^22) r c)⟩

theorem node_complete (vs : List NodeS3) (hok : NodeOk vs) (t : Nat) (pub : List Fp) :
    TableLocal NodeV3.table (node vs) t pub ∧
    TableTraffic NodeV3.interactions (node vs) t pub (nodeTraffic3 vs) ∧
    (node vs).log t=22 := by
  exact ⟨node_render_local_at vs hok _ t pub 22 ⟨by change 1≤22; decide,by change 22≤22; decide⟩ hok.rows (by intros; rfl),
    node_render_traffic_at vs hok _ t pub hok.rows (by intros; rfl),rfl⟩

theorem value_complete (es : List ValE) (hok : ValOk es) (t : Nat) (pub : List Fp) :
    TableLocal ValV3.table (value es) t pub ∧
    TableTraffic ValV3.interactions (value es) t pub (valTraffic es) ∧
    (value es).log t=22 := by
  exact ⟨val_render_local_at es hok _ t pub 22 ⟨by change 1≤22; decide,by change 22≤22; decide⟩ hok.wf.rows (by intros; rfl),
    val_render_traffic_at es hok _ t pub hok.wf.rows (by intros; rfl),rfl⟩

theorem uniq_complete (es : List UEnt) (hok : UOk es) (t : Nat) (pub : List Fp) :
    TableLocal Uniq.table (uniq es) t pub ∧
    TableTraffic Uniq.interactions (uniq es) t pub (uniqTraffic (uniqEntries es)) ∧
    (uniq es).log t=22 := by
  exact ⟨uniq_render_local_at es hok _ t pub 22 ⟨by change 1≤22; decide,by change 22≤22; decide⟩ hok.cap (by intros; rfl),
    uniq_render_traffic_at es hok _ t pub hok.cap (by intros; rfl),rfl⟩
end ZkFormal.NearV3.Candidates.TrieHeight
