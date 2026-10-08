import ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
import ZkFormal.NearV3.Assembly.QueuePartition
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Near Assembly

def events (pre : PTrie) (rs : List Receipt) : List (Nat×Nat) :=
  rs.zipIdx.filterMap (fun x=>(choice pre x.1).map (fun i=>(i,uses pre (rs.take x.2) i)))

theorem event_coverage (pre : PTrie) (rs : List Receipt) (x : Nat×Nat)
    (hx:x∈events pre rs) : x.1∈(NativeAccessKeyProviders.selected pre rs).eraseDups := by
  obtain ⟨y,hy,he⟩:=List.mem_filterMap.mp hx
  cases hi:choice pre y.1 with
  | none=>simp [hi] at he
  | some i=>
    simp only [hi,Option.map_some,Option.some.injEq] at he
    subst x
    rw [List.mem_eraseDups,selected_choice]
    exact List.mem_filterMap.mpr ⟨y.1,List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hy),hi⟩

theorem event_ranks (pre : PTrie) (rs : List Receipt) (i : Nat) :
    (events pre rs).filterMap (fun x=>if x.1==i then some x.2 else none)=ranks pre rs i := by
  simp only [events,List.filterMap_filterMap,ranks]
  congr 1
  funext x
  cases h:choice pre x.1 with
  | none=>simp [h]
  | some j=>by_cases he:j=i <;> simp [h,he]

theorem event_group (pre : PTrie) (rs : List Receipt) (i : Nat) :
    ((events pre rs).filter (fun x=>x.1==i)).map (fun x=>x.2)=ranks pre rs i := by
  rw [←event_ranks]
  induction events pre rs with
  | nil=>rfl
  | cons x xs ih=>by_cases h:x.1=i <;> simp [h,ih,List.filter_cons,List.filterMap_cons]

private theorem erase_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  match xs with
  | []=>simp
  | a::xs=>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp,erase_nodup _⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem selected_nodup (pre : PTrie) (rs : List Receipt) :
    (NativeAccessKeyProviders.selected pre rs).eraseDups.Nodup := erase_nodup _
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
