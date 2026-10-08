import ZkFormal.NearV3.Candidates.ProcNativeRows
namespace ZkFormal.NearV3.Candidates.ProcEntryPosition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcNativeRows

def roundStart (R : Run) (pre : List RoundD) : Nat :=
  (keyVs R ++ pre.flatMap (roundVs R)).length

theorem block_lookup (R : Run) (pre block post : List PV)
    (he : procVs R=pre++block++post) (i : Nat) (hi : i<block.length) :
    atRow R (pre.length+i)=block[i] := by
  have hlt : pre.length+i<(procVs R).length := by simp [he]; omega
  rw [atRow,dif_pos hlt]
  simp only [he,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left hi]

theorem round_lookup (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) (i : Nat) (hi : i<(roundVs R rd).length) :
    atRow R (roundStart R pre+i)=(roundVs R rd)[i] := by
  apply block_lookup R (keyVs R++pre.flatMap (roundVs R)) (roundVs R rd)
    (post.flatMap (roundVs R)) _ i hi
  simp [procVs,he,List.flatMap_append,List.append_assoc]

theorem entry_lookup (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) (i : Nat) (hi : i<rd.entries.toArray.size) :
    atRow R (roundStart R pre+1+i)=entV R rd rd.entries.toArray i := by
  have h := round_lookup R pre post rd he (i+1) (by simp [roundVs]; omega)
  simpa [roundVs,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem header_lookup (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) : atRow R (roundStart R pre)=hdrV R rd := by
  have h := round_lookup R pre post rd he 0 (by simp [roundVs])
  simpa [roundVs] using h
end ZkFormal.NearV3.Candidates.ProcEntryPosition
