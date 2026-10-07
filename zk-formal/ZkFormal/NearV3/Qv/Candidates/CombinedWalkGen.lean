import ZkFormal.NearV3.Qv.Candidates.ValueGen
import ZkFormal.NearV3.Qv.ReadPlan

/-! Honest queue walk data and row generation. Value IDs and provider-use counters
are supplied by the allocator; no ownership or local AIR proof is assumed here. -/
namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec NearSpecV3

inductive Kind where
  | delayed | buffered | yielded | group (shard : Nat)
  deriving DecidableEq

def Kind.code : Kind → Nat
  | .delayed => 0 | .buffered => 1 | .yielded => 2 | .group _ => 3

def Kind.bytes : Kind → Bytes
  | .delayed => [7] | .buffered => [13] | .yielded => [10] | .group s => [16] ++ u64 s

structure Walk where
  kind : Kind
  tau : Nat
  slot : Nat
  count : Nat
  value : Option Bytes
  vid : Nat
  users : Nat
  lastMain : Bool
  final : Bool

def Walk.mode (w : Walk) : Nat :=
  if w.tau=0 then match w.kind with | .buffered => 1 | .group _ => 2 | _ => 0 else 2

def Walk.request (w : Walk) (shards : List Nat) : ReadRequest :=
  ⟨nibbles w.kind.bytes,w.value,
    if w.tau=0 then match w.kind with
      | .buffered => .buffered shards | .group _ => .raw | _ => .empty
    else .raw⟩

def Walk.row (w : Walk) (pos : Nat) (byte : UInt8) : List Nat :=
  let first := pos == 0
  let last := pos+1 == w.kind.bytes.length
  let present := last && w.value.isSome
  let main := w.tau == 0
  let vid := if w.value.isSome then w.vid else 0
  let base := (ValueGen.row ⟨vid,w.tau,w.users,2,0,w.count⟩ 0 0 4 0 0
    ((List.range 8).map fun i => UInt8.ofNat (byte.toNat / 2^i % 2))).set 4 w.mode
  base ++ [1,w.kind.code%2,w.kind.code/2,pos,byte.toNat,w.slot,first.toNat,last.toNat,
    (last && w.final).toNat,(!w.value.isSome).toNat,
    ((w.kind.code==3) && !first).toNat,(present && main && (w.kind.code==1)).toNat,
    main.toNat,w.lastMain.toNat,present.toNat]

def Walk.rows (w : Walk) : List (List Nat) :=
  w.kind.bytes.zipIdx.map fun (b,i) => w.row i b

theorem Walk.rows_length (w : Walk) : w.rows.length = w.kind.bytes.length := by
  simp [Walk.rows]

theorem Walk.row_width (w : Walk) (pos : Nat) (byte : UInt8) : (w.row pos byte).length = 52 := by
  simp [Walk.row,ValueGen.row_width,ValueTable.width]

abbrev Resolve := Nat → Nat → Nat × Nat

def mainWalk (v : MainValues) (K : Nat) (resolve : Resolve)
    (kind : Kind) (slot : Nat) (value : Option Bytes) : Walk :=
  let last := slot+1 == 3+v.shards.length
  ⟨kind,0,slot,v.shards.length,value,(resolve 0 slot).1,(resolve 0 slot).2,last,last && (K==0)⟩

def mainPlan (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) : List Walk :=
  [mainWalk v K resolve .delayed 0 v.delayed,
   mainWalk v K resolve .buffered 1 v.buffered,
   mainWalk v K resolve .yielded 2 v.yielded] ++
  v.shards.zipIdx.map (fun (s,i) => mainWalk v K resolve (.group s) (3+i)
    ((pre.find (keyGroupsData s)).getD none))

def implicitPlan (pres : List PTrie) (resolve : Resolve) : List Walk :=
  pres.zipIdx.map fun (pre,i) =>
    ⟨.delayed,i+1,0,0,(missingRequest pre).value,(resolve (i+1) 0).1,
      (resolve (i+1) 0).2,false,i+1==pres.length⟩

def plan (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) : List Walk :=
  mainPlan pre v pres.length resolve ++ implicitPlan pres resolve

private theorem map_zipIdx_first {α β : Type} (xs : List α) (f : α → β) :
    xs.zipIdx.map (fun x => f x.1) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem mainPlan_requests (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) :
    (mainPlan pre v K resolve).map (fun w => w.request v.shards) = mainRequests pre v := by
  simp [mainPlan,mainRequests,List.map_map,Function.comp_def,mainWalk,Walk.request,
    Kind.bytes,keyDelayedIdx,keyBufferedIdx,keyYieldIdx,keyGroupsData]
  exact map_zipIdx_first v.shards (fun s => (⟨nibbles (16 :: u64 s),
    (pre.find (nibbles (16 :: u64 s))).getD none,.raw⟩ : ReadRequest))

theorem implicitPlan_requests (pres : List PTrie) (resolve : Resolve) (shards : List Nat) :
    (implicitPlan pres resolve).map (fun w => w.request shards) = pres.map missingRequest := by
  simp [implicitPlan,List.map_map,Function.comp_def,Walk.request,Kind.bytes,missingRequest,
    keyDelayedIdx]
  exact map_zipIdx_first pres missingRequest

private theorem sum_map_const {α : Type} (xs : List α) (n : Nat) :
    (xs.map (fun _ => n)).sum = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul]; omega

theorem mainPlan_rows_length (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) :
    ((mainPlan pre v K resolve).flatMap Walk.rows).length = 3+9*v.shards.length := by
  simp [mainPlan,mainWalk,Walk.rows,Kind.bytes,u64,leN_length,List.length_flatMap,
    List.map_map,Function.comp_def,sum_map_const,Nat.mul_comm]
  omega

theorem implicitPlan_rows_length (pres : List PTrie) (resolve : Resolve) :
    ((implicitPlan pres resolve).flatMap Walk.rows).length = pres.length := by
  simp [implicitPlan,Walk.rows,Kind.bytes,List.length_flatMap,List.map_map,Function.comp_def,sum_map_const]

theorem plan_rows_length (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    ((plan pre v pres resolve).flatMap Walk.rows).length = 3+9*v.shards.length+pres.length := by
  simp only [plan,List.flatMap_append,List.length_append,mainPlan_rows_length,implicitPlan_rows_length]

theorem applyNewChunk_plan_reads {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : pre.wf = true) (h : applyNewChunk prims ctx pre rs = .ok out)
    (K : Nat) (resolve : Resolve) :
    ∃ v : MainValues, v.Valid ∧ ∀ w ∈ mainPlan pre v K resolve,
      (w.request v.shards).Holds pre := by
  obtain ⟨v,hv,hr⟩ := applyNewChunk_pre_queue_reads hw h
  refine ⟨v,hv,fun w hw => mainRequests_hold pre v hv hr _ ?_⟩
  rw [← mainPlan_requests pre v K resolve]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
