import ZkFormal.NearV3.Render.Ups.TreeValueInput
import ZkFormal.NearV3.Render.Ups.SplitKids

/-! The runtime's sparse Kids constructors serialize to the update renderer's
one-child and two-child slot vectors. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

@[simp] theorem treeKidsFrom_length : ∀ n i f,
    (treeKids (kidsFrom n i f)).length=n
  | 0,_,_ => rfl
  | n+1,i,f => by
    cases h : f i <;> simp [kidsFrom,h,treeKids,treeKidsFrom_length n (i+1) f]

theorem treeKidsFrom_at : ∀ n i f j, j<n →
    (treeKids (kidsFrom n i f)).getD j .none=((f (i+j)).map treeKid).getD .none
  | 0,_,_,_,h => by omega
  | n+1,i,f,0,_ => by cases h : f i <;> simp [kidsFrom,h,treeKids]
  | n+1,i,f,j+1,hj => by
    have ih := treeKidsFrom_at n (i+1) f j (by omega)
    cases h : f i <;> simpa [kidsFrom,h,treeKids,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem treeKids_one (x : Nat) (child : PTrie) (hx : x<16) :
    treeKids (kids1 x child)=oneKid x (treeKid child) := by
  apply List.ext_getElem (by simp [kids1,oneKid_length _ _ hx])
  intro j hj hj'
  have h16 : j<16 := by simpa [kids1] using hj
  have h1 := treeKidsFrom_at 16 0 (fun i => if i=x then some child else none) j h16
  have h2 := oneKid_at x j (treeKid child) hx h16
  have he : (treeKids (kids1 x child)).getD j .none=(oneKid x (treeKid child)).getD j .none := by
    rw [h2]
    by_cases h : j=x <;> simpa [kids1,h] using h1
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hj',Option.getD_some] using he

theorem treeKids_two (ts x : Nat) (old new : PTrie) (hx : x<16)
    (hd : x≠if ts=1 then 0 else 15) :
    treeKids (kids2 x old (if ts=1 then 0 else 15) new)=twoEdgeKids ts x (treeKid old) (treeKid new) := by
  apply List.ext_getElem (by simp [kids2,twoEdgeKids_length _ _ _ _ hx hd])
  intro j hj hj'
  have h16 : j<16 := by simpa [kids2] using hj
  have h1 := treeKidsFrom_at 16 0
    (fun i => if i=x then some old else if i=(if ts=1 then 0 else 15) then some new else none) j h16
  have h2 := twoEdgeKids_at ts x j (treeKid old) (treeKid new) hx h16 hd
  have he : (treeKids (kids2 x old (if ts=1 then 0 else 15) new)).getD j .none=
      (twoEdgeKids ts x (treeKid old) (treeKid new)).getD j .none := by
    rw [h2]
    by_cases h : j=x <;> by_cases h' : j=(if ts=1 then 0 else 15) <;> simpa [kids2,h,h',Ne.symm hd] using h1
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hj',Option.getD_some] using he

theorem oneKid_wf (x : Nat) (child : NKid) (hw : child.wf) : ∀ k∈oneKid x child,k.wf := by
  intro k hk
  simp only [oneKid,List.mem_append,List.mem_cons,List.mem_replicate] at hk
  rcases hk with h|rfl|h
  · rcases h with ⟨_,rfl⟩; trivial
  · exact hw
  · rcases h with ⟨_,rfl⟩; trivial

theorem twoEdgeKids_wf (ts x : Nat) (old new : NKid) (ho : old.wf) (hn : new.wf) :
    ∀ k∈twoEdgeKids ts x old new,k.wf := by
  intro k hk
  unfold twoEdgeKids at hk
  split at hk
  · simp only [List.mem_append,List.mem_cons,List.mem_replicate] at hk
    rcases hk with (rfl|⟨_,rfl⟩)|(rfl|⟨_,rfl⟩) <;> simp_all [NKid.wf]
  · simp only [List.mem_append,List.mem_cons,List.mem_replicate,List.not_mem_nil,or_false] at hk
    rcases hk with (⟨_,rfl⟩|rfl|⟨_,rfl⟩)|rfl <;> simp_all [NKid.wf]

end ZkFormal.NearV3.Render.UpsGen
