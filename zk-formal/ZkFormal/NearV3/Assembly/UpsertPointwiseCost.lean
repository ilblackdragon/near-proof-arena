import ZkFormal.NearV3.Assembly.SchedulerSizedWitness

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

private theorem sum_member {α : Type} (f : α → Nat) {xs : List α} {x : α}
    (hx : x∈xs) : f x≤(xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · simp
    · have hh := ih hx; simp only [List.map_cons,List.sum_cons]; omega

theorem output_part_length_le_charge {run : TreeRun} {p : TreePart} (hp : p∈run.parts) :
    (nodeEnc p.output).length≤outputByteCharge run :=
  sum_member (fun q => (nodeEnc q.output).length) hp

theorem scheduler_part_length_bound {us : List SchedulerUpsertWitness}
    (hc : (us.map (fun u => outputByteCharge u.run)).sum≤2131072)
    {u : SchedulerUpsertWitness} (hu : u∈us) {p : TreePart} (hp : p∈u.run.parts) :
    (nodeEnc p.output).length<2^22 := by
  have h1 := output_part_length_le_charge hp
  have h2 := sum_member (fun x => outputByteCharge x.run) hu
  omega

theorem scheduler_value_length_bound {u : SchedulerUpsertWitness} (hv : u.Valid)
    (hl : u.ctx.layout.numShards≤64) : u.value.length<2^24 := by
  have h := u.value_bound hv hl
  omega

end ZkFormal.NearV3.Assembly
