import ZkFormal.NearV3.Candidates.ShaHeight.Trace
import ZkFormal.NearV3.Candidates.HorizontalTraffic
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha ZkFormal.Sha.Gen ZkFormal.Sha.Complete
open HorizontalTraffic

def currentOnly : Expr→Bool
  | .const _ | .pub _ => true
  | .col _ nx => !nx
  | .add a b | .mul a b => currentOnly a && currentOnly b
  | .neg a => currentOnly a
  | _ => false

theorem eval_current (e : Expr) (he : currentOnly e=true) (a b : Trace Fp)
    (t r : Nat) (pub : List Fp) (hc : ∀c,a.cell t r c=b.cell t r c) :
    e.eval a t r pub=e.eval b t r pub := by
  induction e with
  | col i nx => cases nx <;> simp_all [currentOnly,Expr.eval,Expr.evalWith,rowEnv]
  | add x y ix iy =>
    have hh : currentOnly x=true ∧ currentOnly y=true := by
      simpa only [currentOnly,Bool.and_eq_true] using he
    change x.eval a t r pub+y.eval a t r pub=_
    rw [ix hh.1,iy hh.2]; rfl
  | mul x y ix iy =>
    have hh : currentOnly x=true ∧ currentOnly y=true := by
      simpa only [currentOnly,Bool.and_eq_true] using he
    change x.eval a t r pub*y.eval a t r pub=_
    rw [ix hh.1,iy hh.2]; rfl
  | neg x ix => exact congrArg Neg.neg (ix he)
  | const _ => rfl
  | pub _ => rfl
  | _ => simp [currentOnly] at he

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem interactions_current :
    (Sha.Table.interactions 0 1).all (fun i=>i.exprs.all currentOnly)=true := by decide +kernel

theorem current_bus (bb bd : Nat) (i : Interaction) (hi : i∈Sha.Table.interactions bb bd)
    (e : Expr) (he : e∈i.exprs) : currentOnly e=true := by
  have hh : ∃j∈Sha.Table.interactions 0 1,j.exprs=i.exprs := by
    simp only [Sha.Table.interactions,List.mem_append,List.mem_map,List.mem_range,
      List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with ⟨q,hq,rfl⟩|rfl
    · exact ⟨_,Or.inl ⟨q,hq,rfl⟩,rfl⟩
    · exact ⟨_,Or.inr rfl,rfl⟩
  obtain ⟨j,hj,heq⟩ := hh
  rw [← heq] at he
  exact List.all_eq_true.mp (List.all_eq_true.mp interactions_current j hj) e he

theorem row_fixed (msgs : List Gen.Msg) (L t r : Nat) (pub : List Fp)
    (bb bd bus : Nat) (send : Bool) (msg : List Fp) :
    rowCount (Sha.Table.interactions bb bd) (fixedTrace msgs L) t r pub bus send msg=
      rowCount (Sha.Table.interactions bb bd) (honestTrace msgs) t r pub bus send msg := by
  have hh := row_map id (Sha.Table.interactions bb bd) (fixedTrace msgs L) (honestTrace msgs)
    t r pub bus send msg (by
      intro i hi e he
      exact eval_current e (current_bus bb bd i hi e he) _ _ t r pub (fun _=>rfl))
  simpa only [show mapI id=id from funext mapI_id,List.map_id] using hh

theorem pad_mult (msgs : List Gen.Msg) (t r : Nat) (pub : List Fp)
    (bb bd : Nat) (hr : (honestRows msgs).length≤r) (i : Interaction)
    (hi : i∈Sha.Table.interactions bb bd) : i.multNat (honestTrace msgs) t r pub=0 := by
  have hc : ∀c,(honestTrace msgs).cell t r c=0 := by
    intro c
    change Fp.ofNat (honestCell msgs r c)=0
    simp [honestCell,List.getD_eq_getElem?_getD,List.getElem?_eq_none hr,rowCell]
    rfl
  simp only [Sha.Table.interactions,List.mem_append,List.mem_map,List.mem_range,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with ⟨q,hq,rfl⟩|rfl <;>
    simp [Interaction.multNat,Interaction.multNat.go,Sha.Table.E.c,Expr.eval,Expr.evalWith,rowEnv,hc]

theorem pad_count (msgs : List Gen.Msg) (t r : Nat) (pub : List Fp)
    (bb bd bus : Nat) (send : Bool) (msg : List Fp) (hr : (honestRows msgs).length≤r) :
    rowCount (Sha.Table.interactions bb bd) (honestTrace msgs) t r pub bus send msg=0 := by
  unfold rowCount
  have hz : ∀ xs : List Interaction, (∀i∈xs,i.multNat (honestTrace msgs) t r pub=0)→
      (xs.map (fun i=>if i.bus=bus ∧ i.send=send ∧ i.msgVal (honestTrace msgs) t r pub=msg
        then i.multNat (honestTrace msgs) t r pub else 0)).sum=0 := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih => intro h; simp [h i (by simp),ih (by intro j hj; exact h j (by simp [hj]))]
  exact hz _ (pad_mult msgs t r pub bb bd hr)

theorem range_truncate (f : Nat→Nat) (N H : Nat) (h : N≤H)
    (hz : ∀r,N≤r→f r=0) : ((List.range H).map f).sum=((List.range N).map f).sum := by
  rw [show H=N+(H-N) by omega,List.range_add,List.map_append,List.sum_append,List.map_map]
  have he : ((List.range (H-N)).map (fun x=>f (N+x))).sum=0 := by
    have hh : ∀xs : List Nat,(xs.map (fun x=>f (N+x))).sum=0 := by
      intro xs
      induction xs <;> simp_all [hz _ (by omega)]
    exact hh _
  simpa [Function.comp_def,he]

theorem fixed_count (msgs : List Gen.Msg) (L t : Nat) (pub : List Fp)
    (bb bd bus : Nat) (send : Bool) (msg : List Fp)
    (hrows : (honestRows msgs).length≤2^L) :
    tableBusCount (Sha.Table.interactions bb bd) (fixedTrace msgs L) t pub bus send msg=
      tableBusCount (Sha.Table.interactions bb bd) (honestTrace msgs) t pub bus send msg := by
  simp only [table_sum,row_fixed,show (fixedTrace msgs L).height t=2^L from rfl]
  rw [range_truncate _ (honestRows msgs).length _ hrows (pad_count msgs t · pub bb bd bus send msg),
    range_truncate _ (honestRows msgs).length _ (len_le_height msgs t) (pad_count msgs t · pub bb bd bus send msg)]
end ZkFormal.NearV3.Candidates.ShaHeight
