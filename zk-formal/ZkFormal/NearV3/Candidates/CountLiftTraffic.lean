import ZkFormal.NearV3.Candidates.CountLift
import ZkFormal.NearV3.Candidates.HorizontalTraffic
namespace ZkFormal.NearV3.Candidates.CountLiftTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates.SizeCount CountLift HorizontalTraffic

def annotated (tr : Trace Fp) (inc : Expr) (t r : Nat) (pub : List Fp) (i : Interaction) : List Fp :=
  if i.bus=B_SIZE then i.msgVal tr t r pub++[tally tr inc t r pub] else i.msgVal tr t r pub

theorem old_msg (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (i : Interaction) (h : ∀e∈i.msg,e.colBound≤col) :
    i.msgVal (trace tr col inc pub) t r pub=i.msgVal tr t r pub := by
  unfold Interaction.msgVal
  apply List.map_congr_left
  intro e he
  exact eval_old tr col inc t r pub e (h e he)

theorem old_mult (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (i : Interaction) (h : ∀e∈i.mult,e.colBound≤col) :
    i.multNat (trace tr col inc pub) t r pub=i.multNat tr t r pub := by
  unfold Interaction.multNat
  simpa only [List.map_id] using mult_map id i.mult (trace tr col inc pub) tr t r 0 pub
    (by intro e he; exact eval_old tr col inc t r pub e (h e he))

theorem lifted_msg (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (i : Interaction) (h : ∀e∈i.msg,e.colBound≤col) :
    (withCount (Dsl.c col) i).msgVal (trace tr col inc pub) t r pub=annotated tr inc t r pub i := by
  unfold withCount annotated
  split
  · change ((i.msg++[Dsl.c col]).map (fun e=>e.eval (trace tr col inc pub) t r pub))=_
    rw [List.map_append,List.map_cons,List.map_nil,current]
    rw [show i.msg.map (fun e=>e.eval (trace tr col inc pub) t r pub)=i.msgVal tr t r pub
      from old_msg tr col inc t r pub i h]
  · exact old_msg tr col inc t r pub i h

theorem lifted_mult (tr : Trace Fp) (col : Nat) (inc : Expr) (t r : Nat) (pub : List Fp)
    (i : Interaction) (h : ∀e∈i.mult,e.colBound≤col) :
    (withCount (Dsl.c col) i).multNat (trace tr col inc pub) t r pub=i.multNat tr t r pub := by
  have hm : (withCount (Dsl.c col) i).mult=i.mult := by unfold withCount; split <;> rfl
  unfold Interaction.multNat
  rw [hm]
  exact old_mult tr col inc t r pub i h

def annotatedRow (T : Air.Table) (tr : Trace Fp) (inc : Expr) (t r : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) : Nat :=
  (T.interactions.map (fun i=>if i.bus=bus ∧ i.send=send ∧ annotated tr inc t r pub i=msg
    then i.multNat tr t r pub else 0)).sum

theorem row_lift (T : Air.Table) (tr : Trace Fp) (col : Nat) (inc : Expr)
    (t r : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hcols : ∀e∈T.exprs,e.colBound≤col) :
    rowCount (table T col inc).interactions (trace tr col inc pub) t r pub bus send msg=
      annotatedRow T tr inc t r pub bus send msg := by
  unfold rowCount annotatedRow
  simp only [table,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  have he : ∀e∈i.exprs,e.colBound≤col := by
    intro e he
    exact hcols e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩))
  have hm := lifted_msg tr col inc t r pub i (by intro e he'; exact he e (List.mem_append_right _ he'))
  have hn := lifted_mult tr col inc t r pub i (by intro e he'; exact he e (List.mem_append_left _ he'))
  rw [hm,hn]
  have hb : (withCount (Dsl.c col) i).bus=i.bus := by unfold withCount; split <;> rfl
  have hs : (withCount (Dsl.c col) i).send=i.send := by unfold withCount; split <;> rfl
  rw [hb,hs]

theorem count_lift (T : Air.Table) (tr : Trace Fp) (col : Nat) (inc : Expr)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hcols : ∀e∈T.exprs,e.colBound≤col) :
    tableBusCount (table T col inc).interactions (trace tr col inc pub) t pub bus send msg=
      ((List.range (tr.height t)).map (fun r=>annotatedRow T tr inc t r pub bus send msg)).sum := by
  simp only [table_sum,row_lift T tr col inc t _ pub bus send msg hcols]
  rfl

theorem count_non_size (T : Air.Table) (tr : Trace Fp) (col : Nat) (inc : Expr)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hcols : ∀e∈T.exprs,e.colBound≤col) (hb : bus≠B_SIZE) :
    tableBusCount (table T col inc).interactions (trace tr col inc pub) t pub bus send msg=
      tableBusCount T.interactions tr t pub bus send msg := by
  rw [count_lift T tr col inc t pub bus send msg hcols,table_sum]
  congr 1
  apply List.map_congr_left
  intro r hr
  unfold annotatedRow rowCount
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h:i.bus=bus
  · have hn : i.bus≠B_SIZE := by omega
    simp [annotated,hn]
  · simp [h]
end ZkFormal.NearV3.Candidates.CountLiftTraffic
