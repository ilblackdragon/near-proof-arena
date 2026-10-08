import ZkFormal.NearV3.Assembly.SourceSchedulerShaLog22

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Sha.Gen
open Rcpt.Candidates Rcpt.Candidates.DedupCompile

/-- Greedy placement of actual messages; never splits preimages or rewrites IDs. -/
def splitShaMessages : Nat → List Msg → List Msg × List Msg
  | _,[] => ([],[])
  | cap,M::ms =>
    if (msgRows M).length≤cap then
      let p := splitShaMessages (cap-(msgRows M).length) ms
      (M::p.1,p.2)
    else ([],M::ms)

theorem splitShaMessages_reconstruct (cap : Nat) (ms : List Msg) :
    (splitShaMessages cap ms).1++(splitShaMessages cap ms).2=ms := by
  induction ms generalizing cap with
  | nil => rfl
  | cons M ms ih =>
    unfold splitShaMessages
    split
    · simp only [List.cons_append,ih]
    · rfl

theorem splitShaMessages_weights (cap : Nat) (ms : List Msg) :
    upsertShaWeights (splitShaMessages cap ms).1=(splitBudget cap (upsertShaWeights ms)).1 ∧
    upsertShaWeights (splitShaMessages cap ms).2=(splitBudget cap (upsertShaWeights ms)).2 := by
  induction ms generalizing cap with
  | nil => exact ⟨rfl,rfl⟩
  | cons M ms ih =>
    simp only [splitShaMessages,upsertShaWeights,List.map_cons,splitBudget]
    split
    · exact ⟨congrArg (List.cons _) (ih _).1,(ih _).2⟩
    · exact ⟨rfl,rfl⟩

def sourceShaMessageBins (ms : List Msg) : List (List Msg) :=
  let p := splitShaMessages (2^22) ms
  let q := splitShaMessages (2^22) p.2
  [p.1,q.1,q.2]

theorem sourceShaMessageBins_reconstruct (ms : List Msg) :
    (sourceShaMessageBins ms).flatten=ms := by
  simp only [sourceShaMessageBins,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [splitShaMessages_reconstruct,splitShaMessages_reconstruct]

theorem sourceShaMessageBins_weights (ms : List Msg) :
    (sourceShaMessageBins ms).map upsertShaWeights=sourceShaBins (upsertShaWeights ms) := by
  simp only [sourceShaMessageBins,sourceShaBins,List.map_cons,List.map_nil]
  rw [(splitShaMessages_weights _ _).1,(splitShaMessages_weights _ _).1,
    (splitShaMessages_weights _ _).2,(splitShaMessages_weights _ _).2,
    (splitShaMessages_weights _ _).2]

theorem sourceShaMessageBins_fit (ms : List Msg)
    (hm : ∀a∈upsertShaWeights ms,a≤35) (ht : (honestRows ms).length≤8932712) :
    ∀ bin∈sourceShaMessageBins ms,(honestRows bin).length≤2^22 := by
  intro bin hb
  have hmem : upsertShaWeights bin∈sourceShaBins (upsertShaWeights ms) := by
    rw [←sourceShaMessageBins_weights]
    exact List.mem_map.mpr ⟨bin,hb,rfl⟩
  have h := sourceShaBins_fit _ hm (by rw [upsertShaWeights_sum];exact ht) _ hmem
  rwa [upsertShaWeights_sum] at h

end ZkFormal.NearV3.Assembly
