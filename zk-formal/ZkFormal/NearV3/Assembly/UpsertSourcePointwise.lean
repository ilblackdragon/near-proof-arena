import ZkFormal.NearV3.Assembly.SchedulerAllBounds
import ZkFormal.NearV3.Render.Ups.NativeSourceOccurrences

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

private theorem member_sum {α : Type} (f : α→Nat) {xs : List α} {x : α}
    (hx : x∈xs) : f x≤(xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · simp
    · have hh := ih hx; simp only [List.map_cons,List.sum_cons]; omega

theorem traceUpsert_source_length {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) {p : TreePart} (hp : p∈run.parts) :
    (nodeEnc p.source).length≤unfoldedBytesT t := by
  have ho := traceUpsert_source_occurrence hr hp
  have hs := member_sum (fun x=> (nodeEnc x).length) ho
  have ht := nodeByteCharge_le_unfolded t
  unfold nodeByteCharge at ht
  omega

theorem scheduler_source_length_bound {us : List SchedulerUpsertWitness}
    (hc : preBytes (us.map SchedulerUpsertWitness.pre)≤2000000)
    {u : SchedulerUpsertWitness} (hu : u∈us) (hv : u.Valid)
    {p : TreePart} (hp : p∈u.run.parts) : (nodeEnc p.source).length<2^22 := by
  have h1 := traceUpsert_source_length hv.1 hp
  have h2 := member_sum (fun x : SchedulerUpsertWitness=>unfoldedBytesT x.pre) hu
  simp only [preBytes,List.map_map,Function.comp_def] at hc
  omega

end ZkFormal.NearV3.Assembly
