import ZkFormal.NearV3.Candidates.ProcPriorCodecParameter

/-! Isolated Codec prior-input repair. Original bytes are parsed by RawFrame;
the Codec emits current-layout IDs and queries the exact last-write memory.
This file is only the concrete AIR candidate, not its soundness/completeness. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecActual
open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)
open Sched Sched.Codec

/-- The eight former pre-byte bits hold a sender-ID byte shift register. -/
def idByte (i : Nat) : Nat:=prbit i
def idLo : Expr:=.add (c (idByte 0)) (.add (smul 256 (c (idByte 1))) (smul 65536 (c (idByte 2))))
def idMid : Expr:=.add (c (idByte 3)) (.add (smul 256 (c (idByte 4))) (smul 65536 (c (idByte 5))))
def idHi : Expr:=.add (c (idByte 6)) (smul 256 (c (idByte 7)))

def retiredKind : List Expr:= (List.range 8).map (fun i=>boolC (prbit i)) ++
  [.mul encG (sub (c bpre) (ZkFormal.Chacha.Rng.Table.num prbit 8))]
def retiredRec : List Expr:=
  [.mul (.mul (c fA) (c e2)) (.mul (notE (c hasC)) (c apR)),
   .mul (.mul (c fA) (c e2)) (.mul (notE (c hasC)) (c bigR))]

/-- srcC/useC are now sender/receiver indices; hasC is receiver wrap.
They retain the existing within-record carry constraints. -/
def additions : List Expr:=
  [.mul (c ehp) (n srcC),.mul (c ehp) (n useC),
   .mul (c rs) (sub (c kidx) (.add (.mul (c srcC) (c nn)) (c useC)))] ++
  (isZ (c rs) (sub (c useC) (sub (c nn) (k 1))) ib hasC).take 2 ++
  (isZ (c rs) (c useC) ig2 nzb).take 2 ++
  [.mul (c kR) (.mul (notE (c rs)) (c nzb))] ++
  [mul3 (c rend) (notE (c ekl)) (sub (n srcC) (.add (c srcC) (c hasC))),
   mul3 (c rend) (notE (c ekl)) (sub (n useC) (.mul (notE (c hasC)) (.add (c useC) (k 1)))),
   .mul (c fA) (c bpre),
   .mul (c fS) (sub (c bpost) (c (idByte 0)))] ++
  (List.range 7).map (fun i=>mul3 (c fS) (notE (c e7)) (sub (n (idByte i)) (c (idByte (i+1)))))

def constraints : List Expr:=
  (cKind.filter fun e=>!(retiredKind.contains e)) ++
  (cRec.filter fun e=>!(retiredRec.contains e)) ++ cTrl ++ additions

/-- S0F has one consumer (Codec); its exact presence is relayed on retired SPOST. -/
def presence : Interaction:=
  {bus:=B_SPOST,send:=true,mult:=[c kF],msg:=[c tau,c pres,c vid]}
def publicId : Interaction:=
  {bus:=70,send:=true,mult:=[.mul (c rs) (c nzb)],msg:=[c tau,c srcC,idLo,idMid,idHi]}
def priorRead : Interaction:=
  {bus:=68,send:=false,mult:=[.mul (c fA) (c e2)],msg:=[c tau,c kidx,c apR,c bigR]}
def sanity : Interaction:=
  {bus:=74,send:=false,mult:=[c kZ],msg:=[c tau,c sj,c bpre]}
def grid : Interaction:=
  {bus:=B_SDG,send:=false,mult:=[c rs],msg:=[c tau,c kidx,c al,c gb]}

def interactions : List Interaction:=
  (((ProcPriorCodecParameter.table.interactions.set 0 presence).set 12 grid).set 13 publicId).set 14 priorRead ++ [sanity]

def table : Air.Table:=
  {ProcPriorCodecParameter.table with constraints:=constraints,interactions:=interactions}

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem width_same : table.width=91 := rfl
theorem interaction_count : interactions.length=18 := by decide +kernel
theorem standalone_wf : table.wf ⟨[table],77,202⟩ 8=true := by decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecActual
