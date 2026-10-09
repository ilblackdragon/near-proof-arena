import ZkFormal.NearV3.Assembly.SchedulerBranchContexts
import ZkFormal.NearV3.Render.Ups.NativeBranchWindow
import ZkFormal.NearV3.Render.Ups.SplitKidCounts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

private theorem child_present (kids : Kids) (slot : Nat) (child : PTrie)
    (hc : nativeChildAt kids slot=some child) :
    0<((treeKids kids).filter (fun k=>k≠.none)).length := by
  cases kids with
  | nil=>simp [nativeChildAt] at hc
  | none rest=>
    cases slot with
    | zero=>simp [nativeChildAt] at hc
    | succ n=>simpa [treeKids] using child_present rest n child hc
  | some c rest=>simp [treeKids,treeKid]
termination_by kids

/-- Both insertion and replacement branch parts contain their actual rewritten
child. This uses runtime recursion, without output wf or a memory bound. -/
theorem traceUpsert_branch_windows {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {p : TreePart} (hp : p∈run.parts)
    (hk : p.kind=.RDB ∨ p.kind=.RBI) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) : 0<nWin Q.shape := by
  obtain ⟨sv,kids,mem,key',v,inner,hsrc,hout,hcall⟩:=
    traceUpsert_branchContexts root key value run hr p hp hk
  have hc:=traceKids_newChild (.branch sv kids mem) (p.slot::key') kids p.slot key' v inner hcall
  have hn:=child_present inner.output p.slot inner.inner.output hc
  simp [encodeTreePart,hsrc,hout,treeNode] at he
  subst Q
  rw [encodePart_windows]
  change 0<(NodeGen3.branchWins (treeKids inner.output)).length
  rw [branchWins_count]
  exact hn

/-- The same signed, encoded instance has a physical child window for every
RDB/RBI part; callers need no separate branch-size assumption. -/
theorem nativeInstance_branch_windows (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<nQ (nativeInstance recordId baseI root run value Qs))
    (hkind : (part (nativeInstance recordId baseI root run value Qs) k).kind=0 ∨
      (part (nativeInstance recordId baseI root run value Qs) k).kind=5) :
    0<nWin (part (nativeInstance recordId baseI root run value Qs) k).shape := by
  rw [nativeInstance_nQ] at hk
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  rw [hpart] at hkind ⊢
  change Q.kind=0 ∨ Q.kind=5 at hkind
  change 0<nWin Q.shape
  rw [encodeTreePart_kind henc] at hkind
  have hpk : p.kind=.RDB ∨ p.kind=.RBI := by
    cases h : p.kind <;> simp_all [UpsRows.UKind.ix]
  exact traceUpsert_branch_windows hr (List.mem_of_getElem? hp) hpk henc

end ZkFormal.NearV3.Assembly
