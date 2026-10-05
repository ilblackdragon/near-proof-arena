import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Sort

/-!
# ZkFormal.Near.Render.Sort — honest rows of the `sort` table

32 rows per receipt id, ids sorted ascending as little-endian 256-bit
integers; `diff = id_t − id_{t−1} − 1` byte-serially with carries; the delay
line `d j` holds the byte `j + 1` rows back (cyclically, so that the wrap-around
row `0` agrees with an active last row).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

def leVal (b : List Nat) : Nat := b.foldr (fun x acc => x + 256 * acc) 0

def insertSorted (x : Nat × List Nat) : List (Nat × List Nat) → List (Nat × List Nat)
  | [] => [x]
  | y :: ys => if leVal x.2 ≤ leVal y.2 then x :: y :: ys else y :: insertSorted x ys

def sortRowsAll (I : Info) : Array Row := Id.run do
  let ids := (I.e.rs.zip (List.range I.e.rs.length)).map fun (rc, r) => (r, toNats rc.receiptId)
  let sorted := ids.foldr insertSorted []
  let mut rows : Array Row := #[]
  let mut prev : Nat := 0
  for ((r, id), t) in sorted.zip (List.range sorted.length) do
    let diff := if t = 0 then 0 else leVal id - prev - 1
    let db := leBytes 32 diff
    let pb := leBytes 32 prev
    let mut cin := 1
    for i in List.range 32 do
      let tot := pb.getD i 0 + db.getD i 0 + cin
      let cout := if t = 0 then 0 else tot / 256
      let mut row := zeroRow Sort.width
      row := row.set! Sort.act 1
      row := row.set! Sort.sf (if i = 0 then 1 else 0)
      row := row.set! Sort.sl (if i = 31 then 1 else 0)
      row := row.set! Sort.ft (if t = 0 then 1 else 0)
      row := row.set! Sort.rr r
      row := row.set! Sort.i i
      row := row.set! Sort.bb (id.getD i 0)
      row := row.set! Sort.cin cin
      row := row.set! Sort.cout cout
      for j in List.range 8 do
        row := row.set! (Sort.dbit j) ((db.getD i 0 / 2 ^ j) % 2)
      rows := rows.push row
      cin := cout
    prev := leVal id
  let padded := padTo rows (zeroRow Sort.width)
  let H := padded.size
  -- delay line: d j (row q) = bb (row q − 1 − j), cyclically
  let bbs := padded.map fun row => row.getD Sort.bb 0
  return (List.range H).toArray.map fun q =>
    (List.range 32).foldl (fun row j =>
      row.set! (Sort.d j) (bbs.getD ((q + 2 * H - 1 - j) % H) 0)) (padded.getD q #[])

end ZkFormal.Near.Render
