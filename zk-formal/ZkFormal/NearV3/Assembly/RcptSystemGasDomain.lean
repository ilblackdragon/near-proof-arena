import ZkFormal.NearV3.Assembly.RcptKeyNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- The native system branch does not inspect the receipt's gas price. -/
theorem applySystemReceipt_gasPrice (st : Acc) (r : Receipt) (price : Nat) :
    applySystemReceipt st {r with gasPrice:=price}=applySystemReceipt st r := rfl

/-- A runtime-domain probe only: not a complete checkD0a acceptance fixture. -/
def systemHighGasReceipt : Receipt :=
  ⟨AccountId.system,[97,97],List.replicate 32 0,[98,98],⟨0,List.replicate 32 0⟩,Params.u128Max,0⟩
def systemHighGasAccount : Account := ⟨0,0,List.replicate 32 0,0⟩
def systemHighGasState : Acc :=
  ⟨.leaf (accountKeyPath [97,97]) (.val systemHighGasAccount.encode) 0,[],[],0,0⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem systemHighGas_wf : systemHighGasReceipt.wf=true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem systemHighGas_decodes :
    pReceipt systemHighGasReceipt.encode=.ok (systemHighGasReceipt,[]) := by rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem systemHighGas_runs :
    (applySystemReceipt systemHighGasState systemHighGasReceipt).isOk=true := by decide

/-- At block gas price zero the unmasked legacy surplus exceeds u128. -/
theorem systemHighGas_surplus_overflow :
    Params.two128≤Params.G*(systemHighGasReceipt.gasPrice-min systemHighGasReceipt.gasPrice 0) := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
