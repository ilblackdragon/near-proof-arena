import ZkFormal.NearV3.Candidates.PairedStoreKeys
import ZkFormal.NearV3.Candidates.ChainStoreCharge
namespace ZkFormal.NearV3.Candidates.PairedStoreCharge
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem native_charge (pairs : List (PTrie×PTrie)) (store : Nat→List Bytes)
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true) (hb : preBytes (pairs.map Prod.fst)≤2000000)
    (hs : ∀p∈(pairs.map Prod.fst).zipIdx,Stored (mkStore (store p.2)) p.1) :
    let vs:=pairedForest 0 0 0 pairs
    let es:=Render.UpsGen.seedValuesFrom 0 (forestBytes (pairs.map Prod.fst))
    let tau:=NativeStoreProvenance.valueTau (pairs.map Prod.fst)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs tau es)
    StoreSelectedCharge.nodeCharge (ChainMetadata.assign cs 0 vs)+
      StoreSelectedCharge.valueCharge (ChainMetadata.assignValues cs es)≤
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals (pairs.map Prod.fst) store) := by
  dsimp only
  have hv:=NativeValueWf.forest_wf (pairs.map Prod.fst) hw hb
  rw [ChainStoreCharge.exact_charge _ _ _ hv,PairedStoreKeys.forest_occurrences pairs hp]
  have hn:=ChainStoreCharge.native_charge (pairs.map Prod.fst) store hw hb hs
  dsimp only at hn
  rwa [ChainStoreCharge.exact_charge _ _ _ hv] at hn
end ZkFormal.NearV3.Candidates.PairedStoreCharge
