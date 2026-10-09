import ZkFormal.NearV3.Candidates.ProcDistQuietRows
import ZkFormal.NearV3.Candidates.ProcDistScanQuiet
namespace ZkFormal.NearV3.Candidates.ProcDistQuietInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor
open SchedSetAll

def Quiet (rows:Array (Array Nat)) := ∀row∈rows.toList,
  ∀col,col=6 ∨col=7 ∨(115≤col ∧col≤118) →row[col]! =0

theorem push (rs:Array (Array Nat))(row:Array Nat)(hs:Quiet rs)
    (hr:∀col,col=6 ∨col=7 ∨(115≤col ∧col≤118) →row[col]! =0) : Quiet (rs.push row) := by
  intro a ha
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at ha
  rcases ha with ha|rfl
  · exact hs a ha
  · exact hr
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
    (hs:Quiet s.1)(o:ForInStep ShardAcc)(h:shardStep I R sd i s=.ok o) :
    ExceptLoop.StepInv (fun t:ShardAcc=>Quiet t.1) o := by
  obtain ⟨t,rfl⟩:=shard_yield I R sd i s o h
  obtain ⟨row,hr,hq⟩:=ProcDistQuietRows.shard I R sd i s t h
  change Quiet t.1
  rw [hr]
  exact push _ _ hs hq

theorem shard_side (I:Input)(R:Run)(sd:Nat)(s:Array (Array Nat)×List Cmp)
    (hs:Quiet s.1)(o:ForInStep (Array (Array Nat)×List Cmp))
    (h:shardSide I R sd s=.ok o) : ExceptLoop.StepInv (fun t=>Quiet t.1) o := by
  unfold shardSide at h
  obtain ⟨t,ht,h⟩:=bind_ok h
  cases h
  exact ExceptLoop.invariant (List.range R.n) (shardStep I R sd) _
    (fun i _ a ha out ho=>shard_step I R sd i a ha out ho) _ t hs ht

theorem cell_step (I:Input)(R:Run)(i j:Nat)(s:CellAcc)
    (hs:Quiet s.1)(o:ForInStep CellAcc)(h:cellStep I R i j s=.ok o) :
    ExceptLoop.StepInv (fun t:CellAcc=>Quiet t.1) o := by
  obtain ⟨t,rfl⟩:=cell_yield I R i j s o h
  obtain ⟨row,hr,hq⟩:=ProcDistQuietRows.cell I R i j s t h
  change Quiet t.1
  rw [hr]
  exact push _ _ hs hq

theorem header (tv n i r count left col:Nat)(hc:col=6 ∨col=7 ∨(115≤col ∧col≤118)) :
    (Gen.setAll Dist.width [(Dist.act,1),(Dist.kGH,1),(Dist.tau,tv),(Dist.nn,n),
      (Dist.a,i),(Dist.b,255),(Dist.r,r),(Dist.N2,count),(Dist.L2,left),(Dist.dlrg,1)])[col]! =0 := by
  rw [cell _ _ _ (by unfold Dist.width;omega)]
  have hcol:col=6 ∨col=7 ∨col=115 ∨col=116 ∨col=117 ∨col=118:=by omega
  rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [lookup,Dist.act,Dist.kGH,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.r,Dist.N2,Dist.L2,Dist.dlrg]

theorem grid_step (I:Input)(R:Run)(i:Nat)(s:GridAcc)
    (hs:Quiet s.1)(o:ForInStep GridAcc)(h:gridStep I R i s=.ok o) :
    ExceptLoop.StepInv (fun t:GridAcc=>Quiet t.1) o := by
  unfold gridStep at h
  obtain ⟨t,ht,h⟩:=bind_ok h
  cases h
  apply ExceptLoop.invariant (List.range R.n) (cellStep I R i)
    (fun t:CellAcc=>Quiet t.1)
    (fun j _ a ha out ho=>cell_step I R i j a ha out ho) _ t _ ht
  exact push _ _ hs (header _ _ _ _ _ _)

theorem generated (I:Input)(R:Run)(d:DistOut)(h:distRows I R=.ok d) : Quiet d.rows := by
  rw [native_eq] at h
  unfold build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  have hi:=ExceptLoop.invariant [0,1] (shardSide I R) (fun s=>Quiet s.1)
    (fun sd _ s hs o ho=>shard_side I R sd s hs o ho) (#[],[]) a
    (by intro row hr;cases hr) ha
  obtain ⟨b,hb,h⟩:=bind_ok h
  cases h
  exact ExceptLoop.invariant (List.range R.n) (gridStep I R) (fun s:GridAcc=>Quiet s.1)
    (fun i _ s hs o ho=>grid_step I R i s hs o ho) _ b hi hb
theorem physical (I:Input)(R:Run)(d:DistOut)(h:distRows I R=.ok d)
    (row:Array Nat)(hr:row∈d.rows.toList)
    (tr:ZkFormal.Air.Trace ZkFormal.Algebra.Fp)(t r:Nat)(pub:List ZkFormal.Algebra.Fp)
    (hrow:∀col,tr.cell t r col=ZkFormal.Algebra.Fp.ofNat row[col]!) :
    ∀e∈Scan.own,e.eval tr t r pub=0 := by
  have hq:=generated I R d h row hr
  have hz (col:Nat)(hc:col=6 ∨col=7 ∨(115≤col ∧col≤118)) :tr.cell t r col=0:=by
    rw [hrow,hq col hc];rfl
  exact ProcDistScanQuiet.physical tr t r pub (hz Scan.kP (by decide))
    (hz Scan.kS (by decide)) (hz Scan.fQ (by decide)) (hz Scan.re (by decide))
    (hz Scan.us0 (by decide)) (hz Scan.us1 (by decide))

end ZkFormal.NearV3.Candidates.ProcDistQuietInventory
