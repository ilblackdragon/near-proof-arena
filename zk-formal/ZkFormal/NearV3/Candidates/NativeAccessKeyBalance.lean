import ZkFormal.NearV3.Candidates.NativeAccessKeyEvents
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Near Assembly

def eventMessages (pre : PTrie) (rs : List Receipt) (sd : Bool) : List Msg :=
  (events pre rs).map (fun x=>[x.1,x.2+(if sd then 1 else 0)])
def providerMessages (pre : PTrie) (rs : List Receipt) (i : Nat) (sd : Bool) : List Msg :=
  (ranks pre rs i).map (fun u=>[i,u+(if sd then 1 else 0)])

theorem events_partition (pre : PTrie) (rs : List Receipt) (sd : Bool) :
    (eventMessages pre rs sd).Perm
      ((NativeAccessKeyProviders.selected pre rs).eraseDups.flatMap (fun i=>providerMessages pre rs i sd)) := by
  have h:=provider_partition (events pre rs) (NativeAccessKeyProviders.selected pre rs).eraseDups
    Prod.fst id (by simpa using selected_nodup pre rs)
    (by simpa using event_coverage pre rs)
  have hm:=h.map (fun x=>[x.1,x.2+(if sd then 1 else 0)])
  rw [List.map_flatMap] at hm
  apply hm.trans
  apply List.Perm.of_eq
  apply ZkFormal.Near.Render.flatMap_congr'
  intro i _
  rw [providerMessages,←event_group,List.map_map]
  apply List.map_congr_left
  intro x hx
  have he:x.1=i:=by simpa using (List.mem_filter.mp hx).2
  simp [Function.comp_def,he]

/-- All real conditional access-key uses close against the provider's actual
selected count. No uniqueness or membership premise is left to the caller. -/
theorem counter_balance (pre : PTrie) (rs : List Receipt) :
    (akeySends (NativeAccessKeyProviders.providers pre rs) B_AKC++eventMessages pre rs true).Perm
      (eventMessages pre rs false++akeyRecvs (NativeAccessKeyProviders.providers pre rs) B_AKC) := by
  let es:=(NativeAccessKeyProviders.selected pre rs).eraseDups
  have he:es.flatMap (fun i=>[[i,0]]++providerMessages pre rs i true)=
      es.flatMap (fun i=>providerMessages pre rs i false++[[i,(NativeAccessKeyProviders.selected pre rs).count i]]) := by
    apply ZkFormal.Near.Render.flatMap_congr'
    intro i _
    have h:=congrArg (List.map (fun u=>[i,u])) (ranks_balance pre rs i)
    simpa [providerMessages,List.map_map,Function.comp_def] using h
  have hp:=(ZkFormal.Near.Render.perm_flatMap_append es (fun i=>[[i,0]])
    (fun i=>providerMessages pre rs i true)).symm.trans (List.Perm.of_eq he)
  have hp':=hp.trans (ZkFormal.Near.Render.perm_flatMap_append es
    (fun i=>providerMessages pre rs i false) (fun i=>[[i,(NativeAccessKeyProviders.selected pre rs).count i]]))
  simp only [←List.map_eq_flatMap] at hp'
  have hh:=((events_partition pre rs true).append_left (es.map (fun i=>[i,0]))).trans
    (hp'.trans ((events_partition pre rs false).symm.append_right _))
  simpa only [akeySends,akeyRecvs,NativeAccessKeyProviders.providers,List.map_map,
    Function.comp_def,show B_AKC≠B_VBYTES by decide,ite_false,ite_true,es] using hh
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
