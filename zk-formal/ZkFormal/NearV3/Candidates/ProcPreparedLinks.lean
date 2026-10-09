import ZkFormal.NearV3.Candidates.ProcPreparedSequence
import ZkFormal.NearV3.Candidates.ProcPendingCurrent
import ZkFormal.NearV3.Candidates.ProcCoreReplay
namespace ZkFormal.NearV3.Candidates.ProcPreparedLinks
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open List

theorem conv_links_sublist (p : Params) (n : Nat) (raw : List RawReq) :
    (convRaw p n raw).map (·.link) <+ raw.map (fun q=>q.s*n+q.r) := by
  induction raw with
  | nil => exact List.Sublist.refl _
  | cons q qs ih =>
    cases hi : incsOf p q.bm with
    | nil => simpa [convRaw,hi] using List.Sublist.cons (q.s*n+q.r) ih
    | cons x xs => simpa [convRaw,hi] using List.Sublist.cons_cons (q.s*n+q.r) ih

theorem prepared_links_nodup (sp : SchedPub) (hs : SchedPubOk sp) :
    ((convRaw sp.params sp.ids.length (instOf sp).raw).map (·.link)).Nodup := by
  have hb : ((rawOf sp.ids sp.raw).map (fun q=>q.s*sp.ids.length+q.r)).Nodup := by
    rw [rawOf_rawKeys]
    exact keysOf_nodup sp.ids sp.raw hs.keys hs.a8
  have hf : ((instOf sp).raw.map (fun q=>q.s*sp.ids.length+q.r)).Nodup := by
    apply List.Sublist.nodup _ hb
    exact List.Sublist.map _ List.filter_sublist
  exact (conv_links_sublist sp.params sp.ids.length (instOf sp).raw).nodup hf

theorem prepared_links_bound (sp : SchedPub) (q : Req)
    (hq : q∈convRaw sp.params sp.ids.length (instOf sp).raw) : q.link<sp.ids.length*sp.ids.length := by
  have hm : q.link∈(convRaw sp.params sp.ids.length (instOf sp).raw).map (·.link) :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  have hr := (conv_links_sublist sp.params sp.ids.length (instOf sp).raw).subset hm
  have hf : (instOf sp).raw.map (fun q=>q.s*sp.ids.length+q.r) <+
      (rawOf sp.ids sp.raw).map (fun q=>q.s*sp.ids.length+q.r) :=
    List.Sublist.map _ List.filter_sublist
  have hb := hf.subset hr
  rw [rawOf_rawKeys] at hb
  exact keysOf_lt sp.ids sp.raw q.link hb

theorem prepared_initial_current (sp : SchedPub) (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    let reqs := convRaw I.p I.ids.length I.raw
    let st := ProcCoreReplay.initial I
    ProcPendingCurrent.Current reqs st.al (ProcModelStep.initial reqs st).1 := by
  dsimp only
  apply ProcPendingCurrent.initial_current
  intro q hq
  have hb := prepared_links_bound sp q hq
  simpa [ProcCoreReplay.initial,ProcPreparedSequence.input,linkPass] using hb
end ZkFormal.NearV3.Candidates.ProcPreparedLinks
