import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordPartition
open ZkFormal.Air ZkFormal.NearV3.Sched.Codec

def pieces : List (List Expr) := [cRec.take 1,(cRec.drop 1).take 5,
  (cRec.drop 6).take 5,(cRec.drop 11).take 1,(cRec.drop 12).take 5,
  (cRec.drop 17).take 8,(cRec.drop 25).take 5,(cRec.drop 30).take 3,
  (cRec.drop 33).take 2,(cRec.drop 35).take 6,(cRec.drop 41).take 1,
  (cRec.drop 44).take 4,(cRec.drop 48).take 1,(cRec.drop 49).take 3,
  (cRec.drop 52).take 2,(cRec.drop 54).take 5,(cRec.drop 59).take 1,
  (cRec.drop 60).take 3,(cRec.drop 63).take 1]

theorem exact_partition : cRec.filter (fun e=>!(ProcPriorCodecActual.retiredRec.contains e))=pieces.flatten := by decide +kernel

theorem assemble (P : Expr→Prop)
    (h : ∀group∈pieces,∀e∈group,P e) :
    ∀e∈cRec.filter (fun e=>!(ProcPriorCodecActual.retiredRec.contains e)),P e := by
  rw [exact_partition]
  intro e he
  obtain ⟨group,hg,he⟩ := List.mem_flatten.mp he
  exact h group hg e he
end ZkFormal.NearV3.Candidates.ProcCodecRecordPartition
