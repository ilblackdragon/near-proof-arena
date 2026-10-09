import ZkFormal.NearV3.Candidates.MemNativeCells
import ZkFormal.NearV3.Candidates.ProcActualMemoryComparisonInventory
namespace ZkFormal.NearV3.Candidates.MemComparisonRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ProcActualMemoryTags

def messages (X : MV) := rowTraffic Mem.interactions ⟨fun _=>22,fun _ _ c=>Fp.ofNat (X.cell c)⟩ 0 0 [] B_SCMP true

theorem eval (X : MV) : messages X=
    List.replicate (if Fp.ofNat X.isRd+Fp.ofNat X.isGr=1 then 1 else 0) [Fp.ofNat X.t,Fp.ofNat (X.tp+1),1]++
    List.replicate (if Fp.ofNat X.isGr=1 then 1 else 0) [Fp.ofNat X.vin,Fp.ofNat X.inc,Fp.ofNat X.sf] := by
  simp [messages,Mem.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    MV.cell,Mem.isRd,Mem.isGr,Mem.t,Mem.tp,Mem.vin,Mem.inc,Mem.sf,B_SOP,B_SFIN,B_SCMP,
    ZkFormal.Near.ofNat_add']
  exact Or.inr ⟨ofNat_add' X.tp 1,rfl⟩

theorem init (g : Gen.Seg) : messages (initV g)=[] := by
  rw [eval]
  simp [show (0:Fp)+(0:Fp)=0 from rfl,initV,show Fp.ofNat 0=(0:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem pad : messages padV=[] := by
  rw [eval]
  simp [show (0:Fp)+(0:Fp)=0 from rfl,padV,show Fp.ofNat 0=(0:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem op (g : Gen.Seg) (i tp : Nat) (o : Gen.MOp) (ho:OpTag o) :
    messages (opV g i tp o)=(ProcActualMemoryComparisonInventory.opRequests tp o).map cmpMsg := by
  rw [eval]
  rcases ho.1 with hop|hop
  all_goals simp [show (0:Fp)+(1:Fp)=1 from rfl,show (1:Fp)+(0:Fp)=1 from rfl,opV,ProcActualMemoryComparisonInventory.opRequests,hop,OP_READ,OP_GRANT,b2n,cmpMsg,
    show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem ops (g : Gen.Seg) (k tp : Nat) (os : List Gen.MOp) (ho:∀o∈os,OpTag o) :
    (opsVs g k tp os).flatMap messages=(ProcActualMemoryComparisonInventory.requests tp os).map cmpMsg := by
  induction os generalizing k tp with
  | nil=>rfl
  | cons o os ih=>
    rw [opsVs,List.flatMap_cons,op g (k+1) tp o (ho o (by simp)),ih (k+1) o.t (fun x hx=>ho x (by simp [hx]))]
    simp [ProcActualMemoryComparisonInventory.requests,List.map_append]

theorem segment (g : Gen.Seg) (hg:ProcActualMemoryTagSegments.SegTag g) :
    (segVs g).flatMap messages=(ProcActualMemoryComparisonInventory.requests 0 g.ops).map cmpMsg := by
  rw [segVs,List.flatMap_cons,init,List.nil_append,ops g 0 0 g.ops hg]
end ZkFormal.NearV3.Candidates.MemComparisonRows
