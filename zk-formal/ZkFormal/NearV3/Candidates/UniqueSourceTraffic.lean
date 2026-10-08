import ZkFormal.NearV3.Candidates.UniqueSourceCounter
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficComplete
namespace ZkFormal.NearV3.Candidates.UniqueSourceTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Render.SrcpGen

theorem bool_bound (bs : List SrcpB) (rep : Nat→Bool) (r x : Nat)
    (hx : x∈boolCols) : UniqueSourceRender.cell bs rep r x≤1 := by
  have hh : boolCols.all (fun x=>decide (x≠SrcpV3.sz))=true := by decide +kernel
  have hn : x≠SrcpV3.sz := of_decide_eq_true (List.all_eq_true.mp hh x hx)
  rw [UniqueSourceRender.non_size bs rep r x hn]
  exact DedupRender.cell_bool_bound bs rep r x hx

theorem registers (bs : List SrcpB) (rep : Nat→Bool) (r : Nat) :
    regN (UniqueSourceRender.cell bs rep r)=regN (DedupRender.cell bs rep r) := by
  apply List.map_congr_left
  intro i hi
  apply UniqueSourceRender.non_size
  have hh:=List.mem_range.mp hi
  simp only [SrcpV3.reg,SrcpV3.sz]
  omega

theorem non_size (bs : List SrcpB) (rep : Nat→Bool) (r b : Nat) (sd : Bool) (hb : b≠B_SIZE) :
    DedupRender.rowN (UniqueSourceRender.cell bs rep r) b sd=
      DedupRender.rowN (DedupRender.cell bs rep r) b sd := by
  simp only [DedupRender.rowN,registers,hb,false_and,ite_false]
  simp [UniqueSourceRender.cell,SrcpV3.sz,SrcpV3.sg,SrcpV3.q,SrcpV3.wn,SrcpV3.pw,
    SrcpV3.b,SrcpV3.gD,SrcpV3.cId,SrcpV3.cLen,SrcpV3.rt,SrcpV3.j,SrcpV3.L,
    SrcpV3.dup,DedupTable.repeated]
  rfl

def traffic (bs : List SrcpB) (rep : Nat→Bool) : Traffic :=
  ⟨fun b=>if b=B_SIZE then [[2,UniqueSourceCharge.size bs]] else DedupRender.sourceMsgs bs rep b true,
   fun b=>if b=B_SIZE then [] else DedupRender.sourceMsgs bs rep b false⟩

theorem size_row {bs : List SrcpB} (hn : bs≠[]) (rep : Nat→Bool) (r : Nat) (sd : Bool) :
    DedupRender.rowN (UniqueSourceRender.cell bs rep r) B_SIZE sd=
      if sd=true ∧ r=DedupRender.R bs-1 then [[2,UniqueSourceCharge.size bs]] else [] := by
  have hp:=DedupRender.R_pos hn
  have hg : UniqueSourceRender.cell bs rep r SrcpV3.gz=if r+1=DedupRender.R bs then 1 else 0 := by
    rw [UniqueSourceRender.non_size bs rep r _ (by decide),DedupRender.cell_gz_eq hn]
  by_cases hr : r=DedupRender.R bs-1
  · have he : r+1=DedupRender.R bs := by omega
    simp only [DedupRender.rowN,hg,he,ite_true]
    simp [B_SIZE,B_BYTES,B_DIGEST,B_RCL,B_SRC,hr,UniqueSourceRender.cell,
      UniqueSourceCounter.last_counter bs hn]
  · have he : r+1≠DedupRender.R bs := by omega
    simp [DedupRender.rowN,hg,he,hr,B_SIZE,B_BYTES,B_DIGEST,B_RCL,B_SRC]

theorem size_messages {bs : List SrcpB} (hn : bs≠[]) (rep : Nat→Bool)
    (H : Nat) (hH : DedupRender.R bs≤H) (sd : Bool) :
    (List.range H).flatMap (fun r=>DedupRender.rowN (UniqueSourceRender.cell bs rep r) B_SIZE sd)=
      if sd=true then [[2,UniqueSourceCharge.size bs]] else [] := by
  simp only [size_row hn rep]
  cases sd
  · simp
  · simp only [true_and,ite_true]
    apply flatMap_at
    have hh:=DedupRender.R_pos hn
    omega

theorem messages {bs : List SrcpB} (hn : bs≠[]) (rep : Nat→Bool)
    (H : Nat) (hH : DedupRender.R bs≤H)
    (hs : ∀B∈bs,B.root.length=32 ∧ B.leaf.length=32 ∧
      ∀it∈B.path,it.sib.length=32 ∧ it.acc.length=32) (b : Nat) (sd : Bool) :
    (List.range H).flatMap (fun r=>DedupRender.rowN (UniqueSourceRender.cell bs rep r) b sd)=
      if sd then (traffic bs rep).sends b else (traffic bs rep).recvs b := by
  by_cases hb : b=B_SIZE
  · subst b
    rw [size_messages hn rep H hH]
    cases sd <;> rfl
  · simp only [non_size bs rep _ b sd hb]
    rw [DedupRender.messages hn rep H hH hs]
    cases sd <;> simp [traffic,DedupRender.traffic,hb]
end ZkFormal.NearV3.Candidates.UniqueSourceTraffic
