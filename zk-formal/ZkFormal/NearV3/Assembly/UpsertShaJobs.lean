import ZkFormal.NearV3.Render.Ups.TreePartCount
import ZkFormal.NearV3.IdsUps
import ZkFormal.Sha.Gen

/-! Actual native output SHA jobs; aggregate byte/row budget and bus balance
remain separate obligations. Native output memory is serialized modulo u64. -/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def upsertJobId (tau j : Nat) : Nat := 12+16*(512*tau+j)
def upsertShaJob (tau j : Nat) (bytes : Bytes) : ZkFormal.Sha.Gen.Msg :=
  ⟨upsertJobId tau j,bytes.map UInt8.toNat,true⟩
def upsertShaFrom (tau : Nat) : Nat → List Bytes → List ZkFormal.Sha.Gen.Msg
  | _, [] => []
  | j, b::bs => upsertShaJob tau j b::upsertShaFrom tau (j+1) bs

/-- Slot zero is the new scheduler value; subsequent slots are bottom-up native
node outputs, including pass-through parts. No output-wf premise is needed. -/
def upsertShaJobs (tau : Nat) (value : Bytes) (run : TreeRun) : List ZkFormal.Sha.Gen.Msg :=
  upsertShaFrom tau 0 (value::run.parts.map (fun p => nodeEnc p.output))

@[simp] theorem upsertShaFrom_length (tau j : Nat) (bs : List Bytes) :
    (upsertShaFrom tau j bs).length=bs.length := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih => simp [upsertShaFrom,ih]

theorem upsertShaFrom_get (tau j : Nat) (bs : List Bytes) (i : Nat) :
    (upsertShaFrom tau j bs)[i]?=bs[i]?.map (upsertShaJob tau (j+i)) := by
  induction bs generalizing j i with
  | nil => simp [upsertShaFrom]
  | cons b bs ih =>
    cases i with
    | zero => simp [upsertShaFrom]
    | succ i => simpa [upsertShaFrom,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1) i

theorem upsertShaFrom_member {tau j : Nat} {bs : List Bytes} {M : ZkFormal.Sha.Gen.Msg}
    (hm : M∈upsertShaFrom tau j bs) :
    ∃ i b, i<bs.length ∧ bs[i]?=some b ∧ M=upsertShaJob tau (j+i) b := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  have hg : (upsertShaFrom tau j bs)[i]?=some M := List.getElem?_eq_some_iff.mpr ⟨hi,he⟩
  rw [upsertShaFrom_get] at hg
  obtain ⟨b,hb,hM⟩ := Option.map_eq_some_iff.mp hg
  exact ⟨i,b,by simpa using hi,hb,hM.symm⟩

@[simp] theorem upsertShaJobs_length (tau : Nat) (value : Bytes) (run : TreeRun) :
    (upsertShaJobs tau value run).length=run.parts.length+1 := by simp [upsertShaJobs]

theorem upsertShaJobs_value (tau : Nat) (value : Bytes) (run : TreeRun) :
    (upsertShaJobs tau value run)[0]?=some (upsertShaJob tau 0 value) := rfl

theorem upsertShaJobs_part (tau : Nat) (value : Bytes) (run : TreeRun) (i : Nat) :
    (upsertShaJobs tau value run)[i+1]?=
      run.parts[i]?.map (fun p => upsertShaJob tau (i+1) (nodeEnc p.output)) := by
  simp [upsertShaJobs,upsertShaFrom_get,List.getElem?_map,Function.comp_def]

theorem upsertShaJobs_bytes {tau : Nat} {value : Bytes} {run : TreeRun}
    {M : ZkFormal.Sha.Gen.Msg} (hm : M∈upsertShaJobs tau value run) :
    M.dmult=true ∧ ∀x∈M.bytes,x<256 := by
  obtain ⟨i,b,_,_,rfl⟩ := upsertShaFrom_member hm
  refine ⟨rfl,?_⟩
  intro x hx
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
  exact u.toNat_lt

theorem upsertJobId_injective {tau j tau' j' : Nat} (hj : j<512) (hj' : j'<512)
    (he : upsertJobId tau j=upsertJobId tau' j') : tau=tau' ∧ j=j' := by
  unfold upsertJobId at he
  omega

theorem upsertJobId_kind (tau j : Nat) : upsertJobId tau j%16=K_VUPS := by
  unfold upsertJobId K_VUPS
  omega

theorem upsertJobId_bound {tau j : Nat} (ht : tau<32) (hj : j<512) :
    upsertJobId tau j<262144 := by unfold upsertJobId; omega

theorem partialTrie_shaJobs_count (values : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hr : root.length=32) (key : List Nat) (v : Bytes) (run : TreeRun)
    (h : traceUpsert (partialTrie values root keys) key v=some run) (tau : Nat) :
    (upsertShaJobs tau v run).length≤404 ∧ (upsertShaJobs tau v run).length≤512 := by
  have hc := partialTrie_part_count values root keys hr key v run h
  simp only [upsertShaJobs_length]
  omega

theorem partialTrie_shaJobs_ids (values : List Bytes) (root : Bytes) (keys : List (List Nat))
    (hr : root.length=32) (key : List Nat) (v : Bytes) (run : TreeRun)
    (h : traceUpsert (partialTrie values root keys) key v=some run) (tau : Nat)
    {M : ZkFormal.Sha.Gen.Msg} (hm : M∈upsertShaJobs tau v run) :
    ∃ j, j<512 ∧ M.id=upsertJobId tau j := by
  obtain ⟨i,b,hi,_,rfl⟩ := upsertShaFrom_member hm
  have hc := partialTrie_part_count values root keys hr key v run h
  refine ⟨i,?_,?_⟩
  · simp only [List.length_cons,List.length_map] at hi; omega
  · simp [upsertShaJob]

theorem upsertShaJob_node_digest {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (h : traceUpsert t key v=some run) {p : TreePart} (hp : p∈run.parts) :
    sha256 (nodeEnc p.output)=p.output.hashOf :=
  (hashOf_eq_enc _ ((traceUpsert_nodeParts t key v run h) p hp).2).symm

theorem upsertShaFrom_ids_ordered (tau j : Nat) (bs : List Bytes) :
    ((upsertShaFrom tau j bs).map (·.id)).Pairwise (·<·) := by
  induction bs generalizing j with
  | nil => simp [upsertShaFrom]
  | cons b bs ih =>
    simp only [upsertShaFrom,List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih (j+1)⟩
    intro id hid
    obtain ⟨M,hm,rfl⟩ := List.mem_map.mp hid
    obtain ⟨i,c,_,_,rfl⟩ := upsertShaFrom_member hm
    simp only [upsertShaJob,upsertJobId]
    omega

theorem upsertShaJobs_ids_nodup (tau : Nat) (v : Bytes) (run : TreeRun) :
    ((upsertShaJobs tau v run).map (·.id)).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (upsertShaFrom_ids_ordered tau 0 _).imp (fun h => Nat.ne_of_lt h)

theorem upsertShaJobs_transitions_disjoint {tau tau' : Nat} (ht : tau≠tau')
    {v v' : Bytes} {run run' : TreeRun}
    (hc : run.parts.length<512) (hc' : run'.parts.length<512)
    {M M' : ZkFormal.Sha.Gen.Msg}
    (hm : M∈upsertShaJobs tau v run) (hm' : M'∈upsertShaJobs tau' v' run') :
    M.id≠M'.id := by
  obtain ⟨i,b,hi,_,rfl⟩ := upsertShaFrom_member hm
  obtain ⟨i',b',hi',_,rfl⟩ := upsertShaFrom_member hm'
  simp only [List.length_cons,List.length_map] at hi hi'
  intro he
  exact ht (upsertJobId_injective (by omega) (by omega) he).1

theorem upsertShaFrom_byte_count (tau j : Nat) (bs : List Bytes) :
    ((upsertShaFrom tau j bs).map (fun M => M.bytes.length)).sum=
      (bs.map List.length).sum := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih => simp [upsertShaFrom,upsertShaJob,ih]

/-- Exact cost accounting, without claiming the intermediate output cost is
bounded by the authenticated pre-state or rebuilt final diff. -/
theorem upsertShaJobs_byte_count (tau : Nat) (v : Bytes) (run : TreeRun) :
    ((upsertShaJobs tau v run).map (fun M => M.bytes.length)).sum=
      v.length+(run.parts.map (fun p => (nodeEnc p.output).length)).sum := by
  simp [upsertShaJobs,upsertShaFrom_byte_count,List.map_map,Function.comp_def]

theorem upsertJobId_renderer (I : Render.UpsInst) (j : Nat) :
    (upsertJobId I.tau j : Int)=Render.UpsGen.upsIdV I j := by
  simp [upsertJobId,Render.UpsGen.upsIdV,Int.natCast_add,Int.natCast_mul]

end ZkFormal.NearV3.Assembly
