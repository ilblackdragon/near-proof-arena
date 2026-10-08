import ZkFormal.NearV3.Rcpt.Candidates.RetainedStorePayload
import ZkFormal.NearV3.Assembly.OriginalBlobIds
namespace ZkFormal.NearV3.Candidates.HonestStoreRepresentatives
open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly Rcpt.Candidates

/-- Transition tags are part of identity. Node and value occurrences share one
byte namespace, matching the native transition's single serialized store. -/
abbrev Key := Nat × Bytes

def representatives (occurrences : List Key) : List Key := occurrences.eraseDups

def firstIndex (occurrences : List Key) (key : Key) : Option Nat :=
  occurrences.findIdx? (·==key)

private theorem erased_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a::xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp,erased_nodup _⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem distinct (xs : List Key) : (representatives xs).Nodup := erased_nodup xs

theorem covers (xs : List Key) (key : Key) : key∈representatives xs ↔ key∈xs :=
  List.mem_eraseDups

theorem first_get {xs : List Key} {key : Key} {i : Nat} (h : firstIndex xs key=some i) :
    xs[i]?=some key := by
  obtain ⟨hi,hb,_⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact List.getElem?_eq_some_iff.mpr ⟨hi,by simpa using hb⟩

/-- Every selected byte class has a concrete original occurrence; no synthetic
representative ID or hash-injectivity assumption is used. -/
theorem representative_index (xs : List Key) (key : Key) (h : key∈representatives xs) :
    ∃ i,firstIndex xs key=some i ∧ xs[i]?=some key := by
  have hm := (covers xs key).mp h
  obtain ⟨i,hi⟩ : ∃i,firstIndex xs key=some i :=
    ⟨_,List.findIdx?_eq_some_of_exists ⟨key,hm,by simp⟩⟩
  exact ⟨i,hi,first_get hi⟩

theorem index_unique {xs : List Key} {a b : Key} {i : Nat}
    (ha : firstIndex xs a=some i) (hb : firstIndex xs b=some i) : a=b :=
  Option.some.inj ((first_get ha).symm.trans (first_get hb))

/-- Full store charge, including the four-byte prefix even for empty values. -/
def charge (xs : List Key) : Nat := (xs.map fun key=>key.2.length+4).sum

/-- A byte-class representative is paid at most once by its transition's native
store, regardless of how often unfolding visits the same stored object. -/
theorem charge_le (occurrences original : List Key) (hc : occurrences⊆original) :
    charge (representatives occurrences)≤charge original := by
  exact nodup_weight_le (fun key : Key=>key.2.length+4) (distinct occurrences)
    (fun key hm=>hc ((covers occurrences key).mp hm))

theorem charge_split (xs : List Key) :
    charge xs=(xs.map fun key=>key.2.length).sum+4*xs.length := by
  induction xs with
  | nil => rfl
  | cons key xs ih =>
    simp only [charge,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

/-- Native transition tags prevent cross-transition coalescing while permitting
node/value sharing inside the same actual native store. -/
theorem transition_separate (a b : Nat) (bytes : Bytes) (h : a≠b) :
    representatives [(a,bytes),(b,bytes)]=[(a,bytes),(b,bytes)] := by
  simp [representatives,List.eraseDups_cons,h,Ne.symm h]
end ZkFormal.NearV3.Candidates.HonestStoreRepresentatives
