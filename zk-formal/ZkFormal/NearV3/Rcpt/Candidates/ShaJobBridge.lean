import ZkFormal.NearV3.Rcpt.Candidates.SourceJobTraffic
import ZkFormal.NearV3.Assembly.SourceShaMessages

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

def jobsToSha (ms : List Render.Msg) : List Sha.Gen.Msg :=
  ms.map (fun m => ⟨m.id,m.bytes,true⟩)

theorem jobsToSha_weights (ms : List Render.Msg) :
    Assembly.upsertShaWeights (jobsToSha ms)=ms.map (fun m => Render.rowsOf m.bytes.length) := by
  simp only [Assembly.upsertShaWeights,jobsToSha,List.map_map,Function.comp_def,Render.msgRows_length]

theorem jobsToSha_rows (ms : List Render.Msg) :
    (Sha.Gen.honestRows (jobsToSha ms)).length=
      (ms.map (fun m => Render.rowsOf m.bytes.length)).sum := by
  rw [←Assembly.upsertShaWeights_sum,jobsToSha_weights]

theorem sourceViewJobs_compiled (sources : List NearSpecV3.SrcList)
    (entries : List NearSpecV3.ProofEntry) :
    jobsToSha (sourceViewJobs (DedupCompile.blocks sources entries))=
      Assembly.sourceShaMessages sources entries := by
  simp only [jobsToSha,sourceViewJobs,Assembly.sourceShaMessages,Assembly.sourceShaPayload,
    List.map_flatMap,List.map_map,Function.comp_def]
  rfl

/-- The allocator's weight is exactly the physical honest SHA row length. -/
theorem fourSha_physical_fit (scheduler native receipt source : List Sha.Gen.Msg)
    (hs : (Sha.Gen.honestRows scheduler).length≤1663260)
    (hv : (Sha.Gen.honestRows native).length≤2925275)
    (hr : (Sha.Gen.honestRows receipt).length≤1373299)
    (hp : (Sha.Gen.honestRows source).length≤8932712)
    (hm : ∀m∈source,(Sha.Gen.msgRows m).length≤35) :
    let bins := fourShaJobBins (fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length)
      scheduler native receipt source
    bins.length=4 ∧ (∀bin∈bins,(Sha.Gen.honestRows bin).length≤2^22) ∧
      bins.flatten.Perm (scheduler++native++receipt++source) := by
  have hs' := hs
  have hv' := hv
  have hr' := hr
  have hp' := hp
  rw [←Assembly.upsertShaWeights_sum] at hs' hv' hr' hp'
  obtain ⟨hcount,hfit⟩ := fourShaJobBins_fit (fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length)
    scheduler native receipt source hs' hv' hr' hp' hm
  refine ⟨hcount,?_,fourShaJobBins_preserve _ _ _ _ _⟩
  intro bin hb
  rw [←Assembly.upsertShaWeights_sum]
  exact hfit bin hb

end ZkFormal.NearV3.Rcpt.Candidates
