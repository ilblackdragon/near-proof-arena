import ZkFormal.NearV3.Candidates.CurrentFamily
open ZkFormal.NearV3.Candidates.CurrentFamily ZkFormal.Size
#eval (names.zip (shapes 2))
#eval ((bytes 1,bytes 2,bytes 3), partsS (ZkFormal.V2.G.pg 2) (shapes 2))
#eval tables.map fun T=>(T.interactions.length,T.degree 1,T.degree 2,T.degree 3)
#eval tables.all (ZkFormal.Air.Table.wf air 8)
#eval names.zip (tables.map fun T=>T.interactions.filter (fun i=>i.bus=ZkFormal.Near.B_BYTES && i.send)|>.length)

#eval names.zip ((List.range tables.length).map fun i=> bytes 2 - sizeOfWeq (ZkFormal.V2.G.pg 2) ((shapes 2).eraseIdx i))
#eval (List.range 4).map fun j=>sizeOfWeq (ZkFormal.V2.G.pg 2) ((shapes 2).set 3 { (shapes 2)[3]! with maxLog:=22-j})
#eval (List.range 4).map fun j=>sizeOfWeq (ZkFormal.V2.G.pg 2) ((shapes 2).map fun T=>{T with maxLog:=min T.maxLog (22-j)})
#eval (List.range 4).map fun j=>sizeOfWeq (ZkFormal.V2.G.pg 2) ((shapes 2).drop j)
#eval names.zip (tables.map fun T => ((T.interactions.filter (fun i=>i.send)).length,(T.interactions.filter (fun i=> !i.send)).length))

-- Sensitivities only: these are NOT implemented AIR tables or capacity proofs.
def shaShape (n w q : Nat) := List.replicate n ({w:=w,aux:=9,quot:=q,fin:=9,maxLog:=22}:TShape) ++ (shapes 2).drop 4
#eval ([544,496,352,304,297,246,245]:List Nat).map fun w => (w,sizeOfWeq (ZkFormal.V2.G.pg 2) (shaShape 4 w 5))
#eval ([544,448,400,352,304]:List Nat).map fun w => (w,sizeOfWeq (ZkFormal.V2.G.pg 2) (shaShape 3 w 5))
#eval ([5,6,7]:List Nat).map fun q => (q,sizeOfWeq (ZkFormal.V2.G.pg 2) (shaShape 4 304 q))
#eval ([2,3]:List Nat).map fun n => (n,sizeOfWeq (ZkFormal.V2.G.pg 2) (shaShape n 928 5))

-- Carry packing sensitivity including degree8 quotient cost; not implemented.
#eval sizeOfWeq (ZkFormal.V2.G.pg 2) (shaShape 4 496 7)
