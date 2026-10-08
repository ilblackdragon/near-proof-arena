import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupPayloadLeaf
import ZkFormal.Near.Render.Proof.NodeInfo

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

def nativeStoredKeyLength : PTrie→Nat
  | .leaf key _ _=>key.length
  | .ext key _ _=>key.length
  | _=>0

theorem nativeStoredKeyLength_bytes (t : PTrie) : nativeStoredKeyLength t≤2*(nodeEnc t).length := by
  cases t with
  | hash b=>simp [nativeStoredKeyLength]
  | branch v cs m=>simp [nativeStoredKeyLength]
  | leaf key value mem=>
    have hh:=Near.Render.NodeInfo.hexPrefix_len key true
    simp only [nativeStoredKeyLength,nodeEnc,List.length_append,List.length_singleton]
    omega
  | ext key child mem=>
    have hh:=Near.Render.NodeInfo.hexPrefix_len key false
    simp only [nativeStoredKeyLength,nodeEnc,List.length_append,List.length_singleton]
    omega

theorem native_forest_key_bound (ts : List PTrie) (hb : Assembly.preBytes ts≤2000000)
    (o : PTrie) (ho : o∈ts.flatMap occs) : nativeStoredKeyLength o<P := by
  have he:=nativeStoredKeyLength_bytes o
  have hm:=Link3.le_sum_mem (List.mem_map.mpr ⟨o,ho,rfl⟩ :
    (nodeEnc o).length∈(ts.flatMap occs).map (fun o=>(nodeEnc o).length))
  have hs:=node_occurrence_byte_sum ts
  unfold P;omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
