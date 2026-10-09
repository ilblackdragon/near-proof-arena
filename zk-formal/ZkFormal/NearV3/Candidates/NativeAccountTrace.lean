import ZkFormal.NearV3.Rcpt.Render.AcctRender
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyTraffic

namespace ZkFormal.NearV3.Candidates.NativeAccountTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render Rcpt.Candidates

def trace (as : List AcctV) : Trace Fp :=
  if as=[] then AccountEmpty.emptyTrace else
    {log:=fun _=>ZkFormal.Near.Render.logOf (16*as.length),
     cell:=fun _ r x=>Fp.ofNat (AcctV3Gen.cell as r x)}

theorem renderer_ok (as : List AcctV) (hw : AcctWf as) (hc : as.length≤8192)
    (hb : ∀a∈as,∀b∈a.pre,b<256) : AcctV3Ok as := by
  refine ⟨by have h:=List.length_pos_iff.mpr hw.nonempty;omega,?_,?_,?_,?_⟩
  · change 16*as.length≤131072;omega
  · intro a ha
    refine ⟨(hw.len a ha).1,hb a ha,hw.notMax a ha ?_⟩
    intro i hi
    have hil : i<a.pre.length := by rw [(hw.len a ha).1];omega
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hil,Option.getD_some]
    exact hb a ha _ (List.getElem_mem hil)
  · intro a ha
    exact ⟨(hw.len a ha).2.1,fun b h=>hw.canon a ha b (List.mem_append_right _ h)⟩
  · intro a ha
    exact (hw.len a ha).2.2

theorem complete (as : List AcctV) (hw : as=[] ∨ AcctWf as) (hc : as.length≤8192)
    (hb : ∀a∈as,∀b∈a.pre,b<256) (t : Nat) (pub : List Fp) :
    TableLocal AccountEmpty.table (trace as) t pub ∧
    TableTraffic AccountEmpty.table.interactions (trace as) t pub (acctV3Traffic as) := by
  rcases hw with rfl|hw
  · have he : trace []=AccountEmpty.emptyTrace := by simp [trace]
    rw [he]
    refine ⟨AccountEmpty.empty_local t pub,?_⟩
    intro b msg
    have hs : ∀sd,tableBusCount AccountEmpty.table.interactions AccountEmpty.emptyTrace t pub b sd msg=0 := by
      intro sd
      rw [tableBusCount_eq]
      have hn : (List.range (AccountEmpty.emptyTrace.height t)).flatMap
          (fun r => rowTraffic AccountEmpty.table.interactions AccountEmpty.emptyTrace t r pub b sd) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro r _
        exact AccountEmpty.empty_traffic t r pub b sd
      rw [hn]
      rfl
    simp [acctV3Traffic,acctV3Sends,acctRecvs,hs]
  · have hok:=renderer_ok as hw hc hb
    have hlog : (trace as).log t=ZkFormal.Near.Render.logOf (16*as.length) := by
      simp [trace,hw.nonempty]
    have hcell : ∀r x,r<(trace as).height t→x<AcctV3.width→
        (trace as).cell t r x=Fp.ofNat (AcctV3Gen.cell as r x) := by
      intro r x _ _
      simp [trace,hw.nonempty]
    exact ⟨AccountEmpty.old_local (acctV3_render_local as hok _ t pub hlog hcell),
      acctV3_render_traffic as hok _ t pub hlog hcell⟩

end ZkFormal.NearV3.Candidates.NativeAccountTrace
