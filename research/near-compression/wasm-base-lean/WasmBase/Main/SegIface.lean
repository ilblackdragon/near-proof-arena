import WasmBase.Main.SegSoundX
import WasmBase.Main.WasmView

/-!
# WasmBase.Main.SegIface — the shared interface of the M4c sub-lanes (E2E M4c)

Predicates the M4c sub-lanes (CUTI side / chaining, memory boundary, segment core) state their
results against, fixed up front so that they compose without renaming:

* `PubDigIs pub b x` — the 18 public limbs at `b` are the limbs of the six 64-bit words whose bytes
  are the 48-byte digest `x` (the form `seg_sound` already gives for `ctx_out`);
* `MemGeom pub s` — the public tree geometry (`D`, `nblk`) is the spec memory's (`WasmView.memDepth`,
  `WasmView.nblkOf`);
* `MembIn tr pub s` — MEMB's in-side productions (space 3, producer time `t_in`) are bytes of `s`
  at in-bounds addresses: the memory part of the in-boundary relation;
* `MemRootIn`/`MemRootOut` — the public memory roots are `memRootOf` of the boundary states.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P

/-- The 18 public limbs at `b` encode the 48-byte digest `x`. -/
def PubDigIs (pub : List F) (b : Nat) (x : ArenaCore.Bytes) : Prop :=
  ∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub b = SegSha.limbsF d ∧ SegSha.wbytes d = x

/-- The public memory-tree geometry is the spec memory's. -/
def MemGeom (pub : List F) (s : St) : Prop :=
  (pub.getD pubDepth 0).toNat = WasmView.memDepth s ∧ (pub.getD pubNblk 0).toNat = WasmView.nblkOf s

/-- **MEMB's in-side productions are bytes of `s`**: every space-3 message the in-boundary block
`initS` gets from MEMB is `encB a (readByte s a) t_in` at an in-bounds address `a`. -/
def MembIn (tr : Trace) (pub : List F) (s : St) : Prop :=
  ∀ x ∈ (part Memb.table tr pub 19 busStk true).map decMsg,
    x.slot < memBytes s ∧ x = encB x.slot (readByte s x.slot).toNat (pub.getD pubTIn 0).toNat

/-- The public in-root is the spec memory root of the in-state. -/
def MemRootIn (pub : List F) (s : St) : Prop := PubDigIs pub pubMemIn (WasmView.memRootOf s)

/-- The public out-root is the spec memory root of the out-state. -/
def MemRootOut (pub : List F) (s : St) : Prop := PubDigIs pub pubMemOut (WasmView.memRootOf s)

end WasmBase
