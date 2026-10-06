import ZkFormal.NearV3.Sched.Tables.Mem
import ZkFormal.NearV3.Sched.Gen.Run

/-!
# ZkFormal.NearV3.Sched.Gen.Mem — honest trace of the scheduler memory `smmV3`

Segments in address order (`Run.segs`: links `l < n²`, then senders, receivers). Per segment:
the INIT row (`fst`, `t = 0`; link: `vin = allowed`, `v = a2`, `inc = w = wp = g2`; budget:
`vin = 0`, `v` = budget after the base grants, `inc = w = 0`), then the ops in time order
(`tp` = previous `t`, `vin` / `wp` = previous `v` / `w`); `lst` on the segment's last row.
Padding rows are all zero (at least one, `isLast · act = 0`).

Expected traffic: `SOP` INIT messages (sent by the codec / distribute tables) and the `SFIN`
finals (received by them), both rendered from the link pass and `processEv`.
-/

namespace ZkFormal.NearV3.Sched.Gen.Mem

open NearSpecV3.Scheduler ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Mem (act fst lst isRd isGr addr tp vin wp w al isL inc ok cc sf width)

def segRows (g : Seg) : Array (Array Nat) := Id.run do
  let nOps := g.ops.length
  let base := (zrow width).set! act 1 |>.set! addr g.addr |>.set! al (b2n g.al) |>.set! isL (b2n g.isL)
  let mut out := #[base.set! fst 1 |>.set! lst (b2n (nOps == 0)) |>.set! vin g.vin0
    |>.set! Mem.v g.v0 |>.set! wp g.w0 |>.set! w g.w0 |>.set! inc g.w0]
  let mut tPrev := 0
  let mut i := 0
  for o in g.ops do
    i := i + 1
    out := out.push (base.set! lst (b2n (i == nOps)) |>.set! isRd (b2n (o.op == OP_READ))
      |>.set! isGr (b2n (o.op == OP_GRANT)) |>.set! Mem.t o.t |>.set! tp tPrev |>.set! vin o.vin
      |>.set! Mem.v o.v |>.set! wp o.wp |>.set! w o.w |>.set! inc o.inc |>.set! ok (b2n o.ok)
      |>.set! cc (b2n o.c) |>.set! sf (b2n o.sf))
    tPrev := o.t
  return out

def rows (R : Run) : Array (Array Nat) := R.segs.foldl (fun acc g => acc ++ segRows g) #[]

def trace (R : Run) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace (rows R) 1 fun _ => zrow width

/-- `SOP` INIT messages `(addr, 0, OP_INIT, vin, v, inc, 0, 0)` from the link pass. -/
def expectedInit (I : Input) (tau : Nat := 0) : List (List Nat) :=
  let n := I.ids.length
  let lp := linkPass n I.p I.allowed (a0Canon n I.prev)
  (List.range (n * n)).map (fun l =>
      let b := b2n I.allowed[l]!
      [addrOf tau 0 l, 0, OP_INIT, b, lp.a2[l]!, lp.g2[l]!, 0, 0]) ++
    (List.range n).map (fun s => [addrOf tau 1 s, 0, OP_INIT, 0, lp.sb[s]!, 0, 0, 0]) ++
    (List.range n).map (fun r => [addrOf tau 2 r, 0, OP_INIT, 0, lp.rb[r]!, 0, 0, 0])

/-- `SFIN` finals `(addr, v, w)`: allowances / grants / budgets after the process phase. -/
def expectedFin (n : Nat) (fin : PState) (tau : Nat := 0) : List (List Nat) :=
  (List.range (n * n)).map (fun l => [addrOf tau 0 l, fin.al[l]!, fin.g[l]!]) ++
    (List.range n).map (fun s => [addrOf tau 1 s, fin.sb[s]!, 0]) ++
    (List.range n).map (fun r => [addrOf tau 2 r, fin.rb[r]!, 0])

end ZkFormal.NearV3.Sched.Gen.Mem
