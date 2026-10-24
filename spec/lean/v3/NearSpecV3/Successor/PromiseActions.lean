import NearSpecV3.D3.FunctionCall
import NearSpecV3.Successor.GlobalCodecs

/-! Successor action-log translation. Raw action payloads are emitted by the enabled host path;
no placeholder action reaches execution. The signed manager and decoder remain unchanged. -/
namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Wasm

/-- Reuse ordinary receipt/dependency/gas-weight construction, then replace the temporary CA
slots with canonical raw actions. Log indices and per-receipt action positions are unchanged. -/
def managerGlobal (log : Array MAct) (ah : Bytes) (height : Nat) :
    Except String (Array MR × List (Nat × Nat) × List (Bytes × Bytes)) := do
  let normalized := log.map fun e => match e.rawAction with
    | some (r, _) => { e with text := s!"CA@{r}", rawAction := none }
    | none => e
  let (rs, idx, resumes) ← D3.manager normalized ah height
  let mut rs := rs
  for j in [0:log.size] do
    if let some (receipt, bytes) := log[j]?.bind (·.rawAction) then
      let some (_, m) := idx.find? (·.1 == receipt)
        | throw (oodE "global action on a non-receipt entry")
      let some cur := rs[m]? | throw (oodE "global receipt index")
      let ordinal := ((log.toList.take j).filter (fun e => actionReceiptOf e == some receipt)).length
      let some (placeholder, none) := cur.acts[ordinal]?
        | throw (oodE "global action position")
      if placeholder != [0] then throw (oodE "global action staging position")
      rs := rs.set! m { cur with acts := cur.acts.set ordinal (ofBA bytes, none) }
  pure (rs, idx, resumes)

/-- Decode canonical tag 9/10/11 bytes along with ordinary actions after unused-gas distribution. -/
def finishActsGlobal (r : MR) : Except String (List Act) :=
  r.acts.mapM fun (raw, fc) => do
    let raw := match fc with
      | some (gas, _, method, args, deposit) =>
        [2] ++ borshBytes method ++ borshBytes args ++ u64 gas ++ u128 deposit
      | none => raw
    match GlobalCodecs.pActGlobal raw with
    | .ok (act, []) => pure act
    | .ok _ => throw "unmodeled: global action re-encoding"
    | .error err => throw err

end NearSpecV3.Successor
