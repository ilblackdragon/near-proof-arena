import ZkFormal.NearV3.Candidates.ProcDistCmpRows
import ZkFormal.NearV3.Candidates.ProcDistComparisonValid
namespace ZkFormal.NearV3.Candidates.ProcDistCmpInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor
open SchedSetAll
private theorem fp0 : ZkFormal.Algebra.Fp.ofNat 0 ≠ 1 := by decide +kernel
private theorem fp1 : ZkFormal.Algebra.Fp.ofNat 1 = 1 := rfl

def packet (r:Array Nat) : List Cmp :=
  List.replicate (if ZkFormal.Algebra.Fp.ofNat r[Dist.cg]! = 1 then 1 else 0)
    (r[Dist.cx]!,r[Dist.cy]!,r[Dist.cb]!)
def inventory (rows:Array (Array Nat)) : List Cmp := rows.toList.flatMap packet

theorem push (rs:Array (Array Nat))(r:Array Nat) : inventory (rs.push r)=inventory rs++packet r := by
  simp [inventory,Array.toList_push,List.flatMap_append]
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

private theorem cell_yield (I:Input)(R:Run)(i j:Nat)(s:CellAcc)(o:ForInStep CellAcc)
    (h:cellStep I R i j s=.ok o) : ∃t,o=.yield t := by
  unfold cellStep at h
  dsimp only at h
  split at h
  · obtain ⟨u,hu,h⟩:=bind_ok h
    cases h
    exact ⟨_,rfl⟩
  · cases h
    exact ⟨_,rfl⟩
private theorem shard_yield (I:Input)(R:Run)(sd i:Nat)(s:ShardAcc)(o:ForInStep ShardAcc)
    (h:shardStep I R sd i s=.ok o) : ∃t,o=.yield t := by
  unfold shardStep at h
  obtain ⟨u,hu,h⟩:=bind_ok h
  cases h
  exact ⟨_,rfl⟩

theorem shard_step (I:Input)(R:Run)(sd i:Nat)(s:ShardAcc)
    (hs:inventory s.1=s.2.1)(o:ForInStep ShardAcc)(h:shardStep I R sd i s=.ok o) :
    ExceptLoop.StepInv (fun t:ShardAcc=>inventory t.1=t.2.1) o := by
  obtain ⟨t,rfl⟩:=shard_yield I R sd i s o h
  obtain ⟨row,x,y,hr,hc,hx,hy,hb,hg⟩:=ProcDistCmpRows.shard I R sd i s t h
  change inventory t.1=t.2.1
  rw [hr,push,hs,hc]
  simp [packet,hg,hx,hy,hb,fp1]

theorem shard_side (I:Input)(R:Run)(sd:Nat)(s:Array (Array Nat)×List Cmp)
    (hs:inventory s.1=s.2)(o:ForInStep (Array (Array Nat)×List Cmp))
    (h:shardSide I R sd s=.ok o) :
    ExceptLoop.StepInv (fun t=>inventory t.1=t.2) o := by
  unfold shardSide at h
  obtain ⟨t,ht,h⟩:=bind_ok h
  cases h
  exact ExceptLoop.invariant (List.range R.n) (shardStep I R sd) _
    (fun i _ a ha out ho=>shard_step I R sd i a ha out ho) _ t hs ht

theorem cell_step (I:Input)(R:Run)(i j:Nat)(s:CellAcc)
    (hs:inventory s.1=s.2.1)(o:ForInStep CellAcc)(h:cellStep I R i j s=.ok o) :
    ExceptLoop.StepInv (fun t:CellAcc=>inventory t.1=t.2.1) o := by
  obtain ⟨t,rfl⟩:=cell_yield I R i j s o h
  obtain ⟨row,hr,hc,hg⟩:=ProcDistCmpRows.cell I R i j s t h
  change inventory t.1=t.2.1
  rw [hr,push,hs,hc]
  rcases hg with hg|hg <;> simp [packet,hg,fp0,fp1]

theorem header_silent (tv n i r count left:Nat) :
    packet (Gen.setAll Dist.width [(Dist.act,1),(Dist.kGH,1),(Dist.tau,tv),(Dist.nn,n),
      (Dist.a,i),(Dist.b,255),(Dist.r,r),(Dist.N2,count),(Dist.L2,left),(Dist.dlrg,1)])=[] := by
  unfold packet
  rw [cell _ _ _ (by decide)]
  simp [lookup,Dist.cg,Dist.act,Dist.kGH,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.r,Dist.N2,Dist.L2,Dist.dlrg,fp0]

theorem grid_step (I:Input)(R:Run)(i:Nat)(s:GridAcc)
    (hs:inventory s.1=s.2.1)(o:ForInStep GridAcc)(h:gridStep I R i s=.ok o) :
    ExceptLoop.StepInv (fun t:GridAcc=>inventory t.1=t.2.1) o := by
  unfold gridStep at h
  obtain ⟨t,ht,h⟩:=bind_ok h
  cases h
  apply ExceptLoop.invariant (List.range R.n) (cellStep I R i)
    (fun t:CellAcc=>inventory t.1=t.2.1)
    (fun j _ a ha out ho=>cell_step I R i j a ha out ho) _ t _ ht
  simpa only [push,header_silent,List.append_nil] using hs

theorem generated (I:Input)(R:Run)(d:DistOut)(h:distRows I R=.ok d) : inventory d.rows=d.cmps := by
  rw [native_eq] at h
  unfold build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  have hi:=ExceptLoop.invariant [0,1] (shardSide I R) (fun s=>inventory s.1=s.2)
    (fun sd _ s hs o ho=>shard_side I R sd s hs o ho) (#[],[]) a rfl ha
  obtain ⟨b,hb,h⟩:=bind_ok h
  cases h
  exact ExceptLoop.invariant (List.range R.n) (gridStep I R) (fun s:GridAcc=>inventory s.1=s.2.1)
    (fun i _ s hs o ho=>grid_step I R i s hs o ho) _ b hi hb
end ZkFormal.NearV3.Candidates.ProcDistCmpInventory
