import ZkFormal.NearV3.Candidates.ProcPriorForestByteIdentity
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedForestBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ProcPriorForestByteIdentity

/-- A live actual Node byte interaction belongs to the SAME extracted forest
inventory. This does not admit any caller-defined supplier list. -/
theorem node_source {tr:Trace Fp} {pub:List Fp} {vs:List NodeS3} {es:List ValE}
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    {r:Nat} (hr:r<tr.height 0) {i:Interaction} (hi:i∈NodeV3.interactions)
    (hb:i.bus=B_BYTES) (hs:i.send=true)
    (hm:i.multNat (ProcPriorRoutedNodeView.node tr) 0 r pub≠0) :
    Provider (vs:=vs) (es:=es) (i.msgVal (ProcPriorRoutedNodeView.node tr) 0 r pub) := by
  have hr':r<(ProcPriorRoutedNodeView.node tr).height 0:=hr
  have hp:=tableBusCount_pos hr' hi hm
  rw [hb,hs,(hN _ _).1] at hp
  unfold Provider
  rw [List.map_append]
  exact List.mem_append_left _ (List.count_pos_iff.mp (Nat.pos_of_ne_zero hp))

theorem value_source {tr:Trace Fp} {pub:List Fp} {vs:List NodeS3} {es:List ValE}
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0) {i:Interaction} (hi:i∈ValV3.interactions)
    (hb:i.bus=B_BYTES) (hs:i.send=true)
    (hm:i.multNat (ProcPriorRoutedRawBytes.value tr) 0 r pub≠0) :
    Provider (vs:=vs) (es:=es) (i.msgVal (ProcPriorRoutedRawBytes.value tr) 0 r pub) := by
  have hr':r<(ProcPriorRoutedRawBytes.value tr).height 0:=hr
  have hp:=tableBusCount_pos hr' hi hm
  rw [hb,hs,(hV _ _).1] at hp
  unfold Provider
  rw [List.map_append]
  exact List.mem_append_right _ (List.count_pos_iff.mp (Nat.pos_of_ne_zero hp))

theorem node_pre_unique {vs:List NodeS3} {es:List ValE}
    (hw:NodeWf3 vs) (hv:ValWf es) {n:Nat} (hn:n<vs.length) {pos a b:Fp}
    (ha:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_NPRE n),pos,a])
    (hb:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_NPRE n),pos,b]) :a=b := by
  have he: a.toNat=b.toNat:=(node_pre_byte hw hv hn ha).2.trans (node_pre_byte hw hv hn hb).2.symm
  have hh:=congrArg Fp.ofNat he
  simpa only [Fp.ofNat_toNat] using hh

theorem value_pre_unique {vs:List NodeS3} {es:List ValE}
    (hw:NodeWf3 vs) (hv:ValWf es) {n:Nat} (hn:n<es.length) {pos a b:Fp}
    (ha:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_VPRE n),pos,a])
    (hb:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_VPRE n),pos,b]) :a=b := by
  have he: a.toNat=b.toNat:=(value_pre_byte hw hv hn ha).2.trans (value_pre_byte hw hv hn hb).2.symm
  have hh:=congrArg Fp.ofNat he
  simpa only [Fp.ofNat_toNat] using hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedForestBytes
