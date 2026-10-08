import ZkFormal.NearV3.Candidates.MerkleRender.NativeRoot
import ZkFormal.NearV3.Candidates.MerkleRender.Honest

namespace ZkFormal.NearV3.Candidates.MerkleRender
open NearSpec ZkFormal.Near ZkFormal.Near.Render MrkGen ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Rcpt.Candidates

theorem top_bound {n : Nat} (hn : 1≤n) : topJ n<n+2 := by
  obtain ⟨_,rok,_,r,hr,_,_,_,he⟩ := recs_facts n hn
  have hh := (rok r (List.mem_of_getLast? hr)).2.1
  omega

/-- The actual level-table root consumed by the root row is the native root. -/
theorem levelTable_root (os : List Outcome) (hn : 1≤os.length) :
    (((levelTable (outcomePreimages os)).getD (topJ os.length) []).getD 0 default).dig=
      toNats (outcomeRoot os) := by
  have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
  rw [levelTable_get _ _ (by rw [hl]; exact top_bound hn),←hl,
    top_native _ (by rwa [hl]),outcome_hashes]
  rfl

/-- Concrete native outcome digests, not caller-selected level data. -/
def outcomeTrace (os : List Outcome) (pub : List Fp) : Trace Fp :=
  honestTrace os.length (levelTable (outcomePreimages os)) pub

/-- Honest local validity with the exact native root and count in public fields.
Whole-family SHA/MPOS balance is a separate obligation. -/
theorem outcome_local (os : List Outcome) (pub : List Fp) (hn : os.length≤4481)
    (hp : ∀ i<4, pub.getD (PH_N+i) 0=Fp.ofNat (os.length/256^i%256))
    (ho : ∀ i<32, pub.getD (PH_OUT+i) 0=
      Fp.ofNat (((outcomeRoot os).getD i 0).toNat)) :
    TableLocal MerkleEmpty.table (outcomeTrace os pub) T_MRK pub := by
  apply honest_local _ _ _ hn hp
  intro he i hi
  have hos : os=[] := List.eq_nil_of_length_eq_zero he
  rw [ho i hi,hos]
  change Fp.ofNat (((List.replicate 32 (0 : UInt8)).getD i 0).toNat)=0
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,if_pos hi,Option.getD_some]
  rfl

/-- Instantiating concrete native levels does not change the checked hash-job
count: exactly n−1 internal pair hashes, each64bytes/35SHArows. -/
theorem outcome_jobs (os : List Outcome) :
    (merkleShaJobs (outcomePreimages os)).length=os.length-1 ∧
    (∀m∈merkleShaJobs (outcomePreimages os),m.bytes.length=64) ∧
    hashRows ((merkleShaJobs (outcomePreimages os)).map (fun m => m.bytes.length))=
      35*(os.length-1) := by
  have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
  exact ⟨by rw [merkleShaJobs_count,hl],merkleShaJobs_length _,by rw [merkleShaJobs_rows,hl]⟩

end ZkFormal.NearV3.Candidates.MerkleRender
