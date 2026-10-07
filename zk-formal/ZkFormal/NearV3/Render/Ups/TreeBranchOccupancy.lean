import ZkFormal.NearV3.Render.Ups.TreeKidsTrace
import ZkFormal.NearV3.Render.Ups.TreeViews
import ZkFormal.NearV3.Render.Ups.KidOccupancy

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

theorem viewKids_occupancy (n : Nat) (kids : Kids) :
    kidOccupancy (viewKids n kids)=kidOccupancy (treeKids kids) := by
  cases kids with
  | nil => rfl
  | none rest =>
    simpa only [viewKids,treeKids,kidOccupancy,List.map_cons,NKid.present] using
      congrArg (fun xs : List Bool=>false::xs) (viewKids_occupancy n rest)
  | some child rest =>
    have hp : (viewKid n child).present=true := by unfold viewKid; split <;> rfl
    change (viewKid n child).present :: kidOccupancy (viewKids (n+tsize child) rest)=
      true :: kidOccupancy (treeKids rest)
    rw [hp]
    exact congrArg (fun xs : List Bool=>true::xs) (viewKids_occupancy (n+tsize child) rest)
termination_by kids

/-- An actual existing-child update preserves every branch occupancy bit. -/
theorem traceKids_occupancy : ∀ source wholeKey kids slot key value run,
    traceKids source wholeKey kids slot key value=some run → run.inserted=false →
    kidOccupancy (treeKids run.output)=kidOccupancy (treeKids kids)
  | _,_,.nil,_,_,_,_,h,_ => by simp [traceKids] at h
  | source,wholeKey,.none rest,0,key,value,run,h,hi => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    cases hi
  | source,wholeKey,.some child rest,0,key,value,run,h,hi => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert child key value with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        simp [treeKids,kidOccupancy,treeKid,NKid.present]
  | source,wholeKey,.none rest,slot+1,key,value,run,h,hi => by
    cases hr : traceKids source wholeKey rest slot key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_occupancy source wholeKey rest slot key value inner hr hi
      simpa [treeKids,kidOccupancy] using congrArg (fun xs : List Bool=>false::xs) ih
  | source,wholeKey,.some child rest,slot+1,key,value,run,h,hi => by
    cases hr : traceKids source wholeKey rest slot key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_occupancy source wholeKey rest slot key value inner hr hi
      simpa [treeKids,kidOccupancy,treeKid,NKid.present] using congrArg (fun xs : List Bool=>true::xs) ih
end ZkFormal.NearV3.Render.UpsGen
