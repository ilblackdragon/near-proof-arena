import ZkFormal.NearV3.Candidates.NativeStoreProvenance
import ZkFormal.NearV3.Assembly.QueueSeedSublist
import ZkFormal.NearV3.Rcpt.Candidates.NativeOccurrenceSha
namespace ZkFormal.NearV3.Candidates.NativeValueWf
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Assembly Render.UpsGen

def rows (bs : List Bytes) : Nat := (bs.map fun b=>max 1 b.length).sum

theorem seed_rows (bs : List Bytes) (v : Nat) :
    ((seedValuesFrom v bs).map fun e=>if e.vz then 1 else e.len).sum=rows bs := by
  induction bs generalizing v with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [seedValuesFrom,seedValue,rows,ih]

theorem count_le (bs : List Bytes) : bs.length≤rows bs := by
  induction bs with
  | nil => simp [rows]
  | cons b bs ih => simp only [rows,List.map_cons,List.sum_cons,List.length_cons] at *; omega

theorem length_le (bs : List Bytes) (b : Bytes) (hb : b∈bs) : b.length≤rows bs := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    simp only [List.mem_cons] at hb
    simp only [rows,List.map_cons,List.sum_cons]
    rcases hb with rfl|hb
    · omega
    · have :=ih hb; unfold rows at this; omega

/-- All value validity obligations follow from the actual allocated row budget.
Empty native byte strings consume one physical row and keep their value ID. -/
theorem native_wf (bs : List Bytes) (hr : rows bs+1≤2^22) :
    ValWf (seedValuesFrom 0 bs) := by
  have hn:=count_le bs
  have hp : bs.length<Algebra.P := by unfold Algebra.P; omega
  have hlen : (seedValuesFrom 0 bs).length=bs.length := by
    rw [seedValuesFrom_zipIdx]; simp
  have hid : ∀i (hi : i<(seedValuesFrom 0 bs).length),
      (seedValuesFrom 0 bs)[i].vid=i := by
    intro i hi
    simp [seedValuesFrom_zipIdx,seedValue] 
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    rw [seedValuesFrom_zipIdx] at he
    obtain ⟨⟨b,i⟩,_,rfl⟩:=List.mem_map.mp he
    cases b <;> simp [seedValue]
  · intro e he
    rw [seedValuesFrom_zipIdx] at he
    obtain ⟨⟨b,i⟩,hi,rfl⟩:=List.mem_map.mp he
    have hb:=List.fst_mem_of_mem_zipIdx hi
    have hib:=List.snd_lt_of_mem_zipIdx hi
    have hl:=length_le bs b hb
    refine ⟨?_,?_,?_,?_⟩
    · simp only [seedValue,Nat.zero_add]; omega
    · simp only [seedValue]; unfold Algebra.P; omega
    · simp [seedValue,Algebra.P]
    · intro x hx
      obtain ⟨u,_,rfl⟩:=List.mem_map.mp hx
      have :=u.toNat_lt
      unfold Algebra.P; omega
  · intro i hi
    rw [hid (i+1) hi,hid i (by omega)]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · intro h; exact hid 0 h
  · rw [seed_rows]; exact hr
theorem rows_le (bs : List Bytes) : rows bs≤bs.length+(bs.map List.length).sum := by
  induction bs with
  | nil => simp [rows]
  | cons b bs ih =>
    simp only [rows,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

/-- The unchanged two-million-byte native unfolding cap pays every value row,
including empty values. No new acceptance guard is needed. -/
theorem forest_wf (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : preBytes ts≤2000000) : ValWf (seedValuesFrom 0 (forestBytes ts)) := by
  have hn:=(Rcpt.Candidates.NodePostUpdate.forest_allocation_counts ts hb).2
  have hh:=Rcpt.Candidates.forest_occurrence_bytes ts hw
  simp only [forestStoreViews,Rcpt.Candidates.seedValues_bytes_length] at hh
  have hr:=rows_le (forestBytes ts)
  apply native_wf
  omega

/-- Actual native forests supply both validity and provenance to the exact
selected-record accounting theorem; no abstract validity or charge premise. -/
theorem forest_charge (ts : List PTrie) (store : Nat→List Bytes)
    (hw : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1) :
    let vs := forestNodes 0 0 0 ts
    let es := seedValuesFrom 0 (forestBytes ts)
    let tau := NativeStoreProvenance.valueTau ts
    let rs := CombinedStoreOccurrences.allOccurrences vs tau es
    StoreSelectedCharge.nodeCharge (StoreDuplicateMetadata.assign rs 0 vs)+
      StoreSelectedCharge.valueCharge (ValueDuplicateMetadata.assign rs tau es)≤
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store) := by
  exact StoreSelectedCharge.native_charge_le _ _ _ (forest_wf ts hw hb) _
    (NativeStoreProvenance.original_keys ts store hw hs)

end ZkFormal.NearV3.Candidates.NativeValueWf
