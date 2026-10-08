import ZkFormal.NearV3.Candidates.InteractionPairing
namespace ZkFormal.NearV3.Candidates.InteractionTriples
open ZkFormal.Air

/-- Empty binary multiplicity is zero, so padding contributes no bus traffic
and no multiplicity-bit constraints. -/
def dummy (send : Bool) : Interaction:={bus:=0,send:=send,mult:=[],msg:=[]}

def singles (send : Bool) (xs : List Interaction) : List Interaction:=
  xs.flatMap fun x=>[x,dummy send,dummy send]

def pairs (send : Bool) : List Interaction→List Interaction
  | []=>[]
  | [x]=>[x,dummy send,dummy send]
  | x::y::xs=>x::y::dummy send::pairs send xs

def lows (send : Bool) : List Interaction→List Interaction
  | []=>[]
  | [x]=>[x,dummy send,dummy send]
  | [x,y]=>[x,y,dummy send]
  | x::y::z::xs=>x::y::z::lows send xs

def highLow (send : Bool) : List Interaction→List Interaction→List Interaction
  | [],ys=>lows send ys
  | xs,[]=>singles send xs
  | x::xs,y::ys=>x::y::dummy send::highLow send xs ys

def side (send : Bool) (xs : List Interaction) : List Interaction:=
  singles send (xs.filter fun i=>4<i.phiDegree) ++
  pairs send (xs.filter fun i=>i.phiDegree=3) ++
  highLow send (xs.filter fun i=>i.phiDegree=4) (xs.filter fun i=>i.phiDegree≤2)

def reorder (xs : List Interaction) : List Interaction:=
  side true (xs.filter (·.send)) ++ side false (xs.filter fun i=>!i.send)

def table (T : Air.Table) : Air.Table:={T with interactions:=reorder T.interactions}

theorem dummy_phi (s : Bool) : (dummy s).phiDegree=0 := rfl

theorem dummy_mult (s : Bool) : (dummy s).mult=[] := rfl

end ZkFormal.NearV3.Candidates.InteractionTriples
