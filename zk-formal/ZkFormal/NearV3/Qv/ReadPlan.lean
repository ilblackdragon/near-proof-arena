import ZkFormal.NearV3.Qv.ReceiptPreserve
import ZkFormal.NearV3.Qv.Bounds
import ZkFormal.NearV3.Rcpt.Ids

/-! Executable queue read requests, preserving duplicates and parser modes.
These are semantic witness data for queue AIR construction, not an AIR proof. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3

inductive ParseMode where
  | empty
  | buffered (shards : List Nat)
  | raw

def ParseMode.Accepts : ParseMode → Option Bytes → Prop
  | .empty, v => EmptyQueue v
  | .buffered ss, v => BufferedValue v ss
  | .raw, _ => True

structure ReadRequest where
  key : List Nat
  value : Option Bytes
  mode : ParseMode

def ReadRequest.Holds (r : ReadRequest) (t : PTrie) : Prop :=
  t.find r.key = some r.value ∧ r.mode.Accepts r.value

def mainRequests (pre : PTrie) (v : MainValues) : List ReadRequest :=
  [⟨keyDelayedIdx,v.delayed,.empty⟩,
   ⟨keyBufferedIdx,v.buffered,.buffered v.shards⟩,
   ⟨keyYieldIdx,v.yielded,.empty⟩] ++
  v.shards.map (fun s => ⟨keyGroupsData s,(pre.find (keyGroupsData s)).getD none,.raw⟩)

theorem mainRequests_length (pre : PTrie) (v : MainValues) :
    (mainRequests pre v).length = 3 + v.shards.length := by simp [mainRequests]; omega

theorem mainRequests_hold (pre : PTrie) (v : MainValues)
    (hv : v.Valid) (hr : v.Reads pre pre pre) :
    ∀ r ∈ mainRequests pre v, r.Holds pre := by
  obtain ⟨hd,hb,hy⟩ := hv
  obtain ⟨rd,rb,rg,ry⟩ := hr
  intro r hm
  simp only [mainRequests,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hm
  rcases hm with (rfl | rfl | rfl) | ⟨s,hs,rfl⟩
  · exact ⟨rd,hd⟩
  · exact ⟨rb,hb⟩
  · exact ⟨ry,hy⟩
  · obtain ⟨value,hval⟩ := rg s hs
    exact ⟨by simp [hval],trivial⟩

theorem applyNewChunk_requests {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : pre.wf = true) (h : applyNewChunk prims ctx pre rs = .ok out) :
    ∃ v : MainValues, ∀ r ∈ mainRequests pre v, r.Holds pre := by
  obtain ⟨v,hv,hr⟩ := applyNewChunk_pre_queue_reads hw h
  exact ⟨v,mainRequests_hold pre v hv hr⟩

def missingRequest (pre : PTrie) : ReadRequest :=
  ⟨keyDelayedIdx,(pre.find keyDelayedIdx).getD none,.raw⟩

theorem applyMissingChunk_request {prims : Prims} {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre = .ok post) : (missingRequest pre).Holds pre := by
  obtain ⟨value,hv⟩ := applyMissingChunk_delayed_read h
  exact ⟨by simp [missingRequest,hv],trivial⟩

/-- Disjoint queue walk identifiers; instance index is the low six bits. -/
def walkId (tau slot : Nat) : Nat := W_QV + tau + 64 * slot

theorem walkId_injective {t u i j : Nat} (ht : t < 64) (hu : u < 64)
    (h : walkId t i = walkId u j) : t=u ∧ i=j := by
  unfold walkId at h
  omega

theorem main_group_count_bound (v : MainValues) (hv : v.Valid) {budget : Nat}
    (hb : (v.buffered.map List.length).getD 0 ≤ budget) :
    24 * v.shards.length ≤ budget := by
  have hbuf := hv.2.1
  cases hval : v.buffered with
  | none =>
    have he : v.shards=[] := by simpa [hval,BufferedValue] using hbuf
    simp [he]
  | some bs =>
    have he := bufferedValue_length (show BufferedValue (some bs) v.shards by simpa [hval] using hbuf)
    simp only [hval,Option.map_some,Option.getD_some] at hb
    omega

/-- A conservative canonicality bound from a value-byte bound, without a new
queue-domain condition. Actual assembly must supply the authenticated bound. -/
theorem main_walkId_bound (v : MainValues) (hv : v.Valid)
    (hb : (v.buffered.map List.length).getD 0 < 256^3)
    {pre : PTrie} {tau slot : Nat} (ht : tau < 64) (hs : slot < (mainRequests pre v).length) :
    walkId tau slot < 2^26 := by
  have hn := main_group_count_bound v hv (Nat.le_of_lt hb)
  rw [mainRequests_length] at hs
  unfold walkId W_QV
  omega

end ZkFormal.NearV3.Qv
