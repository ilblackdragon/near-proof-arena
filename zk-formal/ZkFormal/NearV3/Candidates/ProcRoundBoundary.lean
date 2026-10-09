import ZkFormal.NearV3.Candidates.ProcEntryPosition
namespace ZkFormal.NearV3.Candidates.ProcRoundBoundary
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcNativeRows ProcEntryPosition

theorem tail_lookup (R : Run) : atRow R (procVs R).length=tailV R := by
  simp [atRow]

theorem after_round (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) :
    atRow R (roundStart R pre+1+rd.entries.toArray.size)=
      match post with | [] => tailV R | next::_ => hdrV R next := by
  cases post with
  | nil =>
    have hl : roundStart R pre+1+rd.entries.toArray.size=(procVs R).length := by
      simp [roundStart,procVs,he,List.flatMap_append,roundVs]
      omega
    rw [hl,tail_lookup]
  | cons next rest =>
    have hn : R.rounds=(pre++[rd])++next::rest := by simpa [List.append_assoc] using he
    have hp := header_lookup R (pre++[rd]) rest next hn
    have hl : roundStart R (pre++[rd])=roundStart R pre+1+rd.entries.toArray.size := by
      simp [roundStart,List.flatMap_append,roundVs]
      omega
    rw [hl] at hp
    exact hp

theorem last_round (R : Run) (pre : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++[rd]) : R.rounds.getLast?=some rd := by
  simp [he]
end ZkFormal.NearV3.Candidates.ProcRoundBoundary
