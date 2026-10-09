import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedValueNode
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes

/-- Existing node/value conservation selects the entry at the exact original
value ID, not a newly allocated identifier. Node/VParent authenticity is an
explicit separate input until its installed-family transport is assembled. -/
theorem node_entry {vs:List NodeS3} {es:List ValE}
    (hn:NodeWf3 vs) (hw:ValWf es) (hb:Link3.VParentBal vs es)
    {n:Nat} (hni:n<vs.length) {id len:Nat} {pre post:List Nat} {written:Bool}
    (hv:vs[n].v.value=some (id,len,pre,post,written)) :
    id<es.length ∧ es[id]!.vid=id ∧ es[id]!.len=len := by
  obtain ⟨k,hk,hid,hlen⟩:=Link3.val_link hn hw hb hni hv
  have hk0:=ProcPriorRoutedValueBytes.value_id_at hw k hk
  have he:k=id := hk0.symm.trans hid
  rw [←he,getElem!_pos es k hk]
  exact ⟨hk,hk0,hlen⟩

theorem node_unique {vs:List NodeS3} {es:List ValE}
    (hn:NodeWf3 vs) (hw:ValWf es) (hb:Link3.VParentBal vs es)
    {n n':Nat} (hni:n<vs.length) (hnj:n'<vs.length)
    {id len len':Nat} {pre post pre' post':List Nat} {written written':Bool}
    (hv:vs[n].v.value=some (id,len,pre,post,written))
    (hv':vs[n'].v.value=some (id,len',pre',post',written')) :n=n' :=
  Link3.val_unique hn hw hb (ProcPriorRoutedValueBytes.value_count hw) hni hnj hv hv'

/-- Present RawFrame bytes and a node's revealed value use the same extracted
entry and exact vid. This asserts byte equality with that Value entry; it does
not silently replace the node's digest fields with decoded native bytes. -/
theorem raw_node_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {vs:List NodeS3} {es:List ValE} (hn:NodeWf3 vs) (hw:ValWf es)
    (hb:Link3.VParentBal vs es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1)
    (hpres:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1)
    {n:Nat} (hni:n<vs.length) {len:Nat} {pre post:List Nat} {written:Bool}
    (hv:vs[n].v.value=some (cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid,len,pre,post,written)) :
    let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
    let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
    id<es.length ∧ es[id]!.vid=id ∧ es[id]!.len=len ∧ pos<es[id]!.bytes.length ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨hidx,hid,hpos,hbyte⟩:=ProcPriorRoutedValueBytes.raw_byte_index hH htables hpub hw hT hr hs ha hpres
  have hnode:=node_entry hn hw hb hni hv
  exact ⟨hidx,hid,hnode.2.2,hpos,hbyte⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedValueNode
