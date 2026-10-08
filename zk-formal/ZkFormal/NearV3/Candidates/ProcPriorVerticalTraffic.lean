import ZkFormal.NearV3.Candidates.ProcPriorVerticalEval
import ZkFormal.Near.Extract.Segments
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E

def trafficWith (is : List Interaction) (en : Env Fp) (bus : Nat) (sd : Bool) : List (List Fp):=
  is.flatMap fun i=>if i.bus=bus ∧ i.send=sd then
    List.replicate (multWith en i.mult 0) (i.msg.map (·.evalWith en)) else []

theorem mult_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (es : List Expr) (k : Nat) :
    Interaction.multNat.go tr tt r pub es k=multWith (rowEnv tr tt r pub) es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [Interaction.multNat.go,multWith,Expr.eval,ih]; rfl

theorem traffic_row (is : List Interaction) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic is tr tt r pub bus sd=trafficWith is (rowEnv tr tt r pub) bus sd := by
  unfold rowTraffic trafficWith
  apply flatMap_congr'
  intro i hi
  simp only [Interaction.multNat,mult_row,Interaction.msgVal,Expr.eval]

theorem active_traffic (is : List Interaction) (en : Env Fp) (i bus : Nat) (sd : Bool)
    (hm:en.col (stage i) false=1) (hr:en.mul=(·*·)) :
    trafficWith (is.map (interaction i)) en bus sd=trafficWith is (windowEnv en) bus sd := by
  unfold trafficWith
  rw [List.flatMap_map]
  apply flatMap_congr'
  intro a ha
  simp only [interaction,mult_one en i a.mult 0 hm hr,List.map_map]
  have he:a.msg.map (fun e=>(expression e).evalWith en)=a.msg.map (fun e=>e.evalWith (windowEnv en)) := by
    apply List.map_congr_left
    intro e he
    exact expression_eval en e
  change (if a.bus=bus ∧ a.send=sd then List.replicate _ (a.msg.map (fun e=>(expression e).evalWith en)) else [])=_
  rw [he]

theorem inactive_traffic (is : List Interaction) (en : Env Fp) (i bus : Nat) (sd : Bool)
    (hm:en.col (stage i) false=0) (hr:en.mul=(·*·)) :
    trafficWith (is.map (interaction i)) en bus sd=[] := by
  unfold trafficWith
  rw [List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro a ha
  simp only [interaction,mult_zero en i a.mult 0 hm hr,List.replicate_zero,ite_self]

/-- Exact physical row traffic, before applying the one-hot stage facts.
The decomposition retains every component and all natural multiplicities. -/
theorem table_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic table.interactions tr tt r pub bus sd=
      components.zipIdx.flatMap (fun (T,i)=>trafficWith (T.interactions.map (interaction i))
        (rowEnv tr tt r pub) bus sd) := by
  rw [traffic_row]
  simp only [table,trafficWith,List.flatMap_assoc,component]

end ZkFormal.NearV3.Candidates.ProcPriorVertical
