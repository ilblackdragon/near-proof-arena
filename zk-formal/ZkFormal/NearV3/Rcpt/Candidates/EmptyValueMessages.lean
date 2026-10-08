import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueTable
import ZkFormal.Near.Render.Proof.BusDigest
namespace ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
open ZkFormal.Near ZkFormal.Near.Render

def emptyMsg (vid : Nat) : ZkFormal.Near.Msg := digMsg (msgId K_VPRE vid) 0 emptyHash
/-- No deduplication: equal byte strings at different occurrences retain their
own digest suppliers. -/
def emptyMessages (es : List ValE) : List ZkFormal.Near.Msg :=
  es.flatMap (fun e=>if e.bytes=[] then [emptyMsg e.vid] else [])
def valueDigests (es : List ValE) : List ZkFormal.Near.Msg :=
  es.map (fun e=>digestMsg ⟨msgId K_VPRE e.vid,e.bytes⟩)

theorem empty_digest (vid : Nat) : digestMsg ⟨msgId K_VPRE vid,[]⟩=emptyMsg vid := rfl

theorem nonempty_omitted (e : ValE) (h:e.bytes≠[]) : emptyMessages [e]=[] := by
  simp [emptyMessages,h]

theorem empty_occurrence (e : ValE) (h:e.bytes=[]) : emptyMessages [e]=[emptyMsg e.vid] := by
  simp [emptyMessages,h]

/-- Complete VPRE supplier accounting: ordinary SHA jobs plus the fixed-empty
providers equal all value digest requests, retaining occurrence multiplicity. -/
theorem complete_digest_inventory (es : List ValE) :
    ((nativeValueShaJobs es).map digestMsg++emptyMessages es).Perm (valueDigests es) := by
  induction es with
  | nil=>simp [nativeValueShaJobs,emptyMessages,valueDigests]
  | cons e es ih=>
    by_cases he:e.bytes=[]
    · simp only [nativeValueShaJobs,he,if_pos,List.nil_append,emptyMessages,
        List.flatMap_cons,valueDigests,List.map_cons]
      have hi:=List.Perm.cons (emptyMsg e.vid) ih
      have hs : ((nativeValueShaJobs es).map digestMsg++(emptyMsg e.vid::emptyMessages es)).Perm
          (emptyMsg e.vid::((nativeValueShaJobs es).map digestMsg++emptyMessages es)) := by
        exact List.perm_middle
      simpa only [he,empty_digest,List.cons_append,List.nil_append,emptyMessages,valueDigests] using hs.trans hi
    · simp only [nativeValueShaJobs,he,if_false,List.cons_append,List.nil_append,
        List.map_cons,emptyMessages,List.flatMap_cons,List.nil_append,valueDigests]
      exact List.Perm.cons _ ih

end ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
