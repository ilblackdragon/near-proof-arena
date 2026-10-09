import ZkFormal.NearV3.Candidates.HorizontalAssembly
namespace ZkFormal.NearV3.Candidates.HorizontalTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace HorizontalJoin HorizontalAssembly

def rowCount (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) : Nat :=
  (is.map (fun i=>if i.bus=bus ∧ i.send=send ∧ i.msgVal tr t r pub=msg then i.multNat tr t r pub else 0)).sum

theorem add_fold {α : Type} (xs : List α) (f : α→Nat) (n : Nat) :
    xs.foldr (fun x acc=>f x+acc) n=(xs.map f).sum+n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

theorem table_sum (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount is tr t pub bus send msg=
      ((List.range (tr.height t)).map (fun r=>rowCount is tr t r pub bus send msg)).sum := by
  simp only [tableBusCount,add_fold,rowCount,Nat.add_zero]

theorem sum_add {α : Type} (xs : List α) (f g : α→Nat) :
    (xs.map (fun x=>f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

theorem count_append (xs ys : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (xs++ys) tr t pub bus send msg=
      tableBusCount xs tr t pub bus send msg+tableBusCount ys tr t pub bus send msg := by
  simp only [table_sum,rowCount,List.map_append,List.sum_append,sum_add]

def mapI (f : Expr→Expr) (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map f,msg:=i.msg.map f}

theorem mult_map (f : Expr→Expr) (xs : List Expr) (a b : Trace Fp)
    (t r k : Nat) (pub : List Fp)
    (h : ∀e∈xs,(f e).eval a t r pub=e.eval b t r pub) :
    Interaction.multNat.go a t r pub (xs.map f) k=Interaction.multNat.go b t r pub xs k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,Interaction.multNat.go,h x (by simp)]
    rw [ih (k+1) (by intro e he; exact h e (by simp [he]))]

theorem row_map (f : Expr→Expr) (xs : List Interaction) (a b : Trace Fp)
    (t r : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (h : ∀i∈xs,∀e∈i.exprs,(f e).eval a t r pub=e.eval b t r pub) :
    rowCount (xs.map (mapI f)) a t r pub bus send msg=rowCount xs b t r pub bus send msg := by
  unfold rowCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hm : (mapI f i).msgVal a t r pub=i.msgVal b t r pub := by
    simp only [Interaction.msgVal,mapI,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro e he
    exact h i hi e (List.mem_append_right _ he)
  have hb : (mapI f i).multNat a t r pub=i.multNat b t r pub :=
    mult_map f i.mult a b t r 0 pub (by intro e he; exact h i hi e (List.mem_append_left _ he))
  change (if i.bus=bus ∧ i.send=send ∧ (mapI f i).msgVal a t r pub=msg
    then (mapI f i).multNat a t r pub else 0)=_
  rw [hm,hb]

theorem count_map (f : Expr→Expr) (xs : List Interaction) (a b : Trace Fp)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hl : a.log t=b.log t)
    (h : ∀r,∀i∈xs,∀e∈i.exprs,(f e).eval a t r pub=e.eval b t r pub) :
    tableBusCount (xs.map (mapI f)) a t pub bus send msg=tableBusCount xs b t pub bus send msg := by
  simp only [table_sum,Trace.height,hl]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact row_map f xs a b t r pub bus send msg (h r)

@[simp] theorem mapI_id (i : Interaction) : mapI id i=i := by
  cases i
  simp [mapI]

theorem pair_count (A B : Air.Table) (a b : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) (hl : a.log t=b.log t)
    (hcols : ∀e∈A.exprs,e.colBound≤A.width) :
    tableBusCount (pair A B).interactions (join A.width a b) t pub bus send msg=
      tableBusCount A.interactions a t pub bus send msg+
      tableBusCount B.interactions b t pub bus send msg := by
  rw [show (pair A B).interactions=A.interactions++(shifted A.width B).interactions from rfl,
    count_append]
  have left := count_map id A.interactions (join A.width a b) a t pub bus send msg rfl
    (by
      intro r i hi e he
      exact join_left_eval a b t r A.width pub e
        (hcols e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩))))
  have right := count_map (expression A.width) B.interactions (join A.width a b) b
    t pub bus send msg hl (by intro r i hi e he; exact join_right_eval a b t r A.width pub hl e)
  have hmap : mapI (expression A.width)=interaction A.width := rfl
  simpa only [hmap,show mapI id=id from funext mapI_id,List.map_id,shifted,mapI,interaction] using (congrArg (fun n=>n+tableBusCount (B.interactions.map (mapI (expression A.width))) (join A.width a b) t pub bus send msg) left).trans (congrArg (fun n=>tableBusCount A.interactions a t pub bus send msg+n) right)

/-- Exact per-bus, per-direction, per-message conservation under full-list fusion. -/
theorem trace_count (clock : Nat→Nat) (xs : List (Air.Table × Trace Fp))
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hclock : ∀ x∈xs,x.2.log t=clock t)
    (hcap : ∀ x∈xs,x.1.maxLog≤22)
    (hcols : ∀ x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width) :
    tableBusCount (fuse (xs.map Prod.fst)).interactions (trace clock xs) t pub bus send msg=
      (xs.map (fun x=>tableBusCount x.1.interactions x.2 t pub bus send msg)).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil,fuse,layout,List.flatMap_nil,table_sum,rowCount,List.sum_nil]
    have hz : ∀ rs : List Nat, (rs.map (fun _=>0)).sum=0 := by
      intro rs
      induction rs <;> simp_all
    exact hz _
  | cons x xs ih =>
    rw [List.map_cons,fuse_cons _ _ (hcap x (by simp))]
    change tableBusCount (pair x.1 (fuse (xs.map Prod.fst))).interactions
      (join x.1.width x.2 (trace clock xs)) t pub bus send msg=_
    rw [pair_count _ _ _ _ _ _ _ _ _
      (by rw [hclock x (by simp),trace_log clock xs t (by intro y hy; exact hclock y (by simp [hy]))])
      (hcols x (by simp))]
    rw [ih (by intro y hy; exact hclock y (by simp [hy]))
      (by intro y hy; exact hcap y (by simp [hy]))
      (by intro y hy; exact hcols y (by simp [hy]))]
    rfl
end ZkFormal.NearV3.Candidates.HorizontalTraffic
