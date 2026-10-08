import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaJobs
import ZkFormal.Near.Render.Proof.DigMrk

namespace ZkFormal.NearV3.Candidates.MerkleRender
open NearSpec ZkFormal.Near ZkFormal.Near.Render MrkGen
open ZkFormal.NearV3.Rcpt.Candidates

def leafHashes (leaves : List (List Nat)) : List Bytes :=
  leaves.map (fun b => sha256 (ofNats b))

theorem succ_get (leaves : List (List Nat)) (j i : Nat)
    (hi : i<size leaves.length (j+1)) :
    (levelsFromLeaves leaves (j+1)).getD i default=
      if 2*i+1<size leaves.length j then
        ⟨msgId K_MRK (qBase leaves.length (j+1)+i),64,
          shaN (((levelsFromLeaves leaves j).getD (2*i) default).dig++
            ((levelsFromLeaves leaves j).getD (2*i+1) default).dig)⟩
      else (levelsFromLeaves leaves j).getD (2*i) default := by
  have hh : i<((levelsFromLeaves leaves j).length+1)/2 := by
    rw [levelsFromLeaves_length]; exact hi
  simp [levelsFromLeaves,List.getD_eq_getElem?_getD,List.getElem?_map,
    levelsFromLeaves_length,List.getElem?_range (show i<(size leaves.length j+1)/2 from hi)]

/-- The concrete V3 generator follows the native merklize levels exactly. -/
theorem levels_native (leaves : List (List Nat)) : ∀ j i, i<size leaves.length j →
    ((levelsFromLeaves leaves j).getD i default).dig=
      toNats ((Link.lvl (leafHashes leaves) j).getD i [])
  | 0,i,hi => by
    simp only [size] at hi
    simp [levelsFromLeaves,Link.lvl,leafHashes,List.getD_eq_getElem?_getD,
      List.getElem?_map,List.getElem?_zipIdx,hi,shaN]
  | j+1,i,hi => by
    rw [succ_get leaves j i hi]
    have hl : (Link.lvl (leafHashes leaves) j).length=size leaves.length j := by
      rw [Link.lvl_length]
      simp only [leafHashes,List.length_map,BusDigest.size_sz]
    have hi' : i<((Link.lvl (leafHashes leaves) j).length+1)/2 := by rw [hl]; exact hi
    rw [Link.lvl,Link.merkleLevel_get _ i hi',hl]
    split
    · rename_i h
      simp only
      rw [levels_native leaves j (2*i) (by omega),levels_native leaves j (2*i+1) h,BusDigest.shaN_toNats]
    · exact levels_native leaves j (2*i) (by simp only [size] at hi; omega)

theorem top_native (leaves : List (List Nat)) (hn : 1≤leaves.length) :
    ((levelsFromLeaves leaves (topJ leaves.length)).getD 0 default).dig=
      toNats (merkleRoot (leafHashes leaves)) := by
  have hs := BusDigest.size_topJ hn
  rw [levels_native leaves _ 0 (by omega),Link.merkleRoot_eq _
    (by simpa [leafHashes] using hn) (topJ leaves.length)
    (by simpa only [leafHashes,List.length_map,←BusDigest.size_sz] using hs)]

/-- Total root, including the native zero hash for the empty tree. -/
def rootDigest (leaves : List (List Nat)) : List Nat :=
  if leaves=[] then toNats zeroHash
  else ((levelsFromLeaves leaves (topJ leaves.length)).getD 0 default).dig

theorem root_native (leaves : List (List Nat)) :
    rootDigest leaves=toNats (merkleRoot (leafHashes leaves)) := by
  by_cases he : leaves=[]
  · subst leaves; rfl
  · rw [rootDigest,if_neg he]
    exact top_native leaves (by cases leaves <;> simp_all)

def outcomePreimages (os : List Outcome) : List (List Nat) :=
  os.map (fun o => toNats (u32 2++o.id++sha256 o.partialEncode))

theorem outcome_hashes (os : List Outcome) :
    leafHashes (outcomePreimages os)=os.map Outcome.leaf := by
  simp [leafHashes,outcomePreimages,List.map_map,NodeInfo.ofNats_toNats,Outcome.leaf]

/-- Actual native outcome root, without a v1 claim or receipt-domain premise. -/
theorem outcome_root (os : List Outcome) :
    rootDigest (outcomePreimages os)=toNats (outcomeRoot os) := by
  rw [root_native,outcome_hashes]
  rfl

end ZkFormal.NearV3.Candidates.MerkleRender
