import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaCount
import ZkFormal.Near.Render.Proof.MrkTraffic3

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec ZkFormal.Near ZkFormal.Near.Render MrkGen

/-- Generic V3 level constructor from actual outcome-leaf preimages. It does not
require v1 Info. Odd nodes retain their child's ID, digest, and length. -/
def levelsFromLeaves (leaves : List (List Nat)) : Nat→List MNode
  | 0 => (leaves.zipIdx).map (fun (b,r) => ⟨msgId K_LEAF r,b.length,shaN b⟩)
  | j+1 =>
    let prev := levelsFromLeaves leaves j
    (List.range ((prev.length+1)/2)).map fun i =>
      if 2*i+1<prev.length then
        let L := prev.getD (2*i) default
        let R := prev.getD (2*i+1) default
        ⟨msgId K_MRK (qBase leaves.length (j+1)+i),64,shaN (L.dig++R.dig)⟩
      else prev.getD (2*i) default

def levelTable (leaves : List (List Nat)) : List (List MNode) :=
  (List.range (leaves.length+2)).map (levelsFromLeaves leaves)

theorem levelsFromLeaves_length (leaves : List (List Nat)) : ∀j,
    (levelsFromLeaves leaves j).length=size leaves.length j
  | 0 => by simp [levelsFromLeaves,size]
  | j+1 => by simp [levelsFromLeaves,size,levelsFromLeaves_length leaves j]

theorem levelsFromLeaves_digest (leaves : List (List Nat)) : ∀j,∀m∈levelsFromLeaves leaves j,
    m.dig.length=32
  | 0,m,hm => by
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hm
    exact shaN_length _
  | j+1,m,hm => by
    simp only [levelsFromLeaves,List.mem_map,List.mem_range] at hm
    obtain ⟨i,hi,rfl⟩ := hm
    split
    · exact shaN_length _
    · have hk : 2*i<(levelsFromLeaves leaves j).length := by omega
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
      exact levelsFromLeaves_digest leaves j _ (List.getElem_mem _)

theorem levelTable_get (leaves : List (List Nat)) (j : Nat) (hj : j<leaves.length+2) :
    (levelTable leaves).getD j []=levelsFromLeaves leaves j := by
  simp [levelTable,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hj]

/-- Exact whole MRK messages in the actual AIR shape order. -/
def merkleShaJobs (leaves : List (List Nat)) : List ZkFormal.Near.Render.Msg :=
  ((mrkShape leaves.length).filter (·.2.2)).map fun x =>
    let C (i : Nat) := (levelsFromLeaves leaves (x.1-1)).getD i default
    ⟨msgId K_MRK (qBase leaves.length x.1+x.2.1), (C (2*x.2.1)).dig++(C (2*x.2.1+1)).dig⟩

theorem merkleShaJobs_count (leaves : List (List Nat)) :
    (merkleShaJobs leaves).length=leaves.length-1 := by
  simp only [merkleShaJobs,List.length_map,merkle_shape_hash_count]

theorem merkleShaJobs_length (leaves : List (List Nat)) :
    ∀m∈merkleShaJobs leaves,m.bytes.length=64 := by
  intro m hm
  by_cases hn : leaves.length=0
  · have hl := merkleShaJobs_count leaves
    rw [hn] at hl
    have he : merkleShaJobs leaves=[] := List.eq_nil_of_length_eq_zero hl
    rw [he] at hm
    cases hm
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    obtain ⟨hmem,hh⟩ := List.mem_filter.mp hx
    have hr := MrkTraffic.shape_rec (by omega : 1≤leaves.length) hmem
    rcases hr with ⟨h1,h2,h3,h4,_⟩
    simp only at h1 h2 h3 h4
    have hsz : size leaves.length x.1=(size leaves.length (x.1-1)+1)/2 := by
      obtain ⟨j,hj⟩ : ∃j,x.1=j+1 := ⟨x.1-1,by omega⟩
      rw [hj]; rfl
    have hl : 2*x.2.1<(levelsFromLeaves leaves (x.1-1)).length := by
      rw [levelsFromLeaves_length]; omega
    have hh' : 2*x.2.1+1<(levelsFromLeaves leaves (x.1-1)).length := by
      rw [levelsFromLeaves_length]
      rw [hh] at h4
      simp at h4
      omega
    have hd : ∀i (hi : i<(levelsFromLeaves leaves (x.1-1)).length),
        ((levelsFromLeaves leaves (x.1-1)).getD i default).dig.length=32 := by
      intro i hi
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact levelsFromLeaves_digest leaves _ _ (List.getElem_mem _)
    exact by simp only [List.length_append,hd _ hl,hd _ hh']

theorem merkleShaJobs_rows (leaves : List (List Nat)) :
    hashRows ((merkleShaJobs leaves).map (fun m => m.bytes.length))=35*(leaves.length-1) := by
  have hs : ∀xs : List ZkFormal.Near.Render.Msg, (∀m∈xs,m.bytes.length=64) →
      hashRows (xs.map (fun m => m.bytes.length))=35*xs.length := by
    intro xs hx
    induction xs with
    | nil => simp [hashRows]
    | cons x xs ih =>
      have hh := hx x (by simp)
      have hi := ih (fun x hx' => hx x (by simp [hx']))
      have h64 : ZkFormal.Near.Render.rowsOf 64=35 := by decide
      simp only [List.map_cons,hashRows,List.sum_cons,List.length_cons,hh,h64] at *
      omega
  rw [hs _ (merkleShaJobs_length leaves),merkleShaJobs_count]

end ZkFormal.NearV3.Rcpt.Candidates
