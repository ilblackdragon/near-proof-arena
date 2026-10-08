import ZkFormal.NearV3.Candidates.ProcPriorRecordTable
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordLinear
open ZkFormal.Air ZkFormal.Chacha.Table.E ProcPriorRecordTable

def interactions (rb qb ib wb pb : Nat) : List Interaction:=
  (ProcPriorRecordTable.interactions rb qb ib wb pb).take 4 ++
  [{bus:=ib,send:=false,mult:=[.mul (c topLimb) (c sender)],
    msg:=[c tau,queryOrdinal,c senderFound,c senderIndex]},
   {bus:=ib,send:=false,mult:=[.mul (c topLimb) (c receiver)],
    msg:=[c tau,queryOrdinal,c receiverFound,c receiverIndex]}] ++
  (ProcPriorRecordTable.interactions rb qb ib wb pb).drop 5

def table (rb qb ib wb pb : Nat) : Air.Table:=
  {ProcPriorRecordTable.table rb qb ib wb pb with interactions:=interactions rb qb ib wb pb}

theorem constraints (rb qb ib wb pb : Nat) :
    (table rb qb ib wb pb).constraints=ProcPriorRecordTable.constraints := rfl

theorem standalone_wf : (table 0 1 2 3 4).wf ⟨[table 0 1 2 3 4],5,0⟩ 8=true := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorRecordLinear
