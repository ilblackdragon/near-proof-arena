import NearSpecV3.Wasm.Syntax

/-!
# Wasmtime 45 pooling instance layout, PV86 x86-64 validator build

Source: wasmtime-environ-45.0.0/src/vmoffsets.rs (VMOffsets::from) and
wasmtime-45.0.0/src/runtime/vm/instance.rs (Instance::alloc_layout).
NEAR instrument_v3 adds three function imports and two globals; memory is imported.
The fixed Instance header is 160 bytes in the pinned build (no wmemcheck/debug guest).
This is an explicit runtime environment model, not a portable Rust ABI assertion.
-/
namespace NearSpecV3.Wasm

/-- Distinct original function indices that Wasmtime materializes as VMFuncRef.
All imports escape. Exports, start, global ref.func and element ref.func add defined functions.
Validated body ref.func instructions refer to functions declared in those sections. -/
def escapedFunctions (m : Module) : List Nat :=
  let imports := List.range m.imports.size
  let exports := m.exports.toList.filterMap fun (_, kind, index) =>
    if kind == 0 then some index else none
  let globals := m.globals.toList.filterMap fun g =>
    match g.init with | .refFunc i => some i | _ => none
  let elems := m.elems.toList.flatMap fun e => e.init.toList.filterMap fun c =>
    match c with | .refFunc i => some i | _ => none
  (imports ++ exports ++ m.start.toList ++ globals ++ elems).eraseDups

/-- Pooling allocation for the instrumented module, including 16-byte global alignment.
Tables and function references are metadata only; their element storage lives elsewhere. -/
def instanceAllocationBytes (m : Module) : Nat :=
  let staticVmctx := 48
  let memoryImport := 24
  let functionImports := 32 * (m.imports.size + 3)
  let definedTables := 16 * m.tables.size
  let beforeGlobals := staticVmctx + memoryImport + functionImports + definedTables
  let aligned := ((beforeGlobals + 15) / 16) * 16
  160 + aligned + 16 * (m.globals.size + 2) + 32 * ((escapedFunctions m).length + 3)

def instanceAllocationFits (m : Module) : Bool := instanceAllocationBytes m ≤ 1048576

def instanceLoadingError : String :=
  "LoadingError { msg: \"module instance size does not fit in pooling allocator requirements\" }"

end NearSpecV3.Wasm
