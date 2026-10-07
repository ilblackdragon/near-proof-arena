import ZkFormal.NearV3.Extract.Ups.PlanDefs
import ZkFormal.NearV3.Extract.Ups.QNodes

/-! Executable instrumentation of the actual PTrie.upsert recursion. Parts contain
ordinary source/output tries; no AIR condition or successful-run equality is an input. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

structure TreePart where
  kind : UKind
  source : PTrie
  output : PTrie
  /-- Branch slot for RDB/RBI, otherwise unused. -/
  slot : Nat := 0

structure TreeRun where
  output : PTrie
  parts : List TreePart
  terminal : UCase
  matched : Nat
  terminalSource : PTrie
  terminalKey : List Nat

structure KidsRun where
  output : Kids
  oldMem : Nat
  newMem : Nat
  inner : TreeRun
  inserted : Bool

def pushPart (run : TreeRun) (part : TreePart) : TreeRun :=
  {run with output := part.output, parts := run.parts++[part]}

def terminalRun (src : PTrie) (key : List Nat) (cs : UCase) (matched : Nat)
    (result : PTrie) (parts : List TreePart) : TreeRun :=
  ⟨result,parts,cs,matched,src,key⟩

def wrapRun (src : PTrie) (path : List Nat) (run : TreeRun) : TreeRun :=
  match path with
  | [] => run
  | _::_ => pushPart run ⟨.WEX,src,wrapExt path run.output,0⟩

def leafSplitRun (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) : TreeRun :=
  let src := PTrie.leaf k s m
  let p := commonPrefix k key
  match k.drop p.length, key.drop p.length with
  | [], y::ys =>
    let fresh := newLeaf ys v
    let branch := PTrie.branch (some s) (kids1 y fresh) (50+valueMem s.len+leafMem ys v.length)
    wrapRun src p (terminalRun src key .LSa p.length branch [⟨.NLF,src,fresh,0⟩,⟨.SPB,src,branch,0⟩])
  | x::xs, [] =>
    let moved := PTrie.leaf xs s (leafMem xs s.len)
    let branch := PTrie.branch (some (.val v)) (kids1 x moved) (50+valueMem v.length+leafMem xs s.len)
    wrapRun src p (terminalRun src key .LSb p.length branch [⟨.MVL,src,moved,0⟩,⟨.SPB,src,branch,0⟩])
  | x::xs, y::ys =>
    let moved := PTrie.leaf xs s (leafMem xs s.len)
    let fresh := newLeaf ys v
    let branch := PTrie.branch none (kids2 x moved y fresh) (50+leafMem xs s.len+leafMem ys v.length)
    wrapRun src p (terminalRun src key .LSc p.length branch [⟨.MVL,src,moved,0⟩,⟨.NLF,src,fresh,0⟩,⟨.SPB,src,branch,0⟩])
  | [], [] => terminalRun src key .LP 0 (newLeaf key v) [⟨.RLP,src,newLeaf key v,0⟩]

def extSplitRun (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) : TreeRun :=
  let src := PTrie.ext k c m
  let p := commonPrefix k key
  let cm := m-extOwnMem k
  match k.drop p.length with
  | [] => terminalRun src key .ESl1 p.length src []
  | x::xs =>
    let sub := match xs with | [] => c | _::_ => PTrie.ext xs c (extOwnMem xs+cm)
    let subMem := match xs with | [] => cm | _::_ => extOwnMem xs+cm
    let moved := match xs with | [] => [] | _::_ => [TreePart.mk .MVE src sub 0]
    match key.drop p.length with
    | [] =>
      let branch := PTrie.branch (some (.val v)) (kids1 x sub) (50+valueMem v.length+subMem)
      wrapRun src p (terminalRun src key (if xs.isEmpty then .ESl1 else .ESl0) p.length branch
        (moved++[⟨.SPB,src,branch,0⟩]))
    | y::ys =>
      let fresh := newLeaf ys v
      let branch := PTrie.branch none (kids2 x sub y fresh) (50+subMem+leafMem ys v.length)
      wrapRun src p (terminalRun src key (if xs.isEmpty then .ESn1 else .ESn0) p.length branch
        (moved++[⟨.NLF,src,fresh,0⟩,⟨.SPB,src,branch,0⟩]))

mutual
def traceUpsert : PTrie → List Nat → Bytes → Option TreeRun
  | .hash _, _, _ => none
  | .leaf k s m, key, v =>
    if k=key then some (terminalRun (.leaf k s m) key .LP 0 (newLeaf k v) [⟨.RLP,.leaf k s m,newLeaf k v,0⟩])
    else some (leafSplitRun k s m key v)
  | .ext k c m, key, v =>
    if isPrefix k key then
      match c.mem?, traceUpsert c (key.drop k.length) v with
      | some cm, some run => some (pushPart run ⟨if k.isEmpty then .PT else .RDE,.ext k c m,qRDE k m run.output cm,0⟩)
      | _, _ => none
    else some (extSplitRun k c m key v)
  | .branch bv cs m, [], v =>
    let result := PTrie.branch (some (.val v)) cs (m+valueMem v.length-(match bv with | some s => valueMem s.len | none => 0))
    some (terminalRun (.branch bv cs m) [] (if bv.isSome then .BR else .BV) 0 result
      [⟨if bv.isSome then .RBR else .RBV,.branch bv cs m,result,0⟩])
  | .branch bv cs m, n::key, v =>
    (traceKids (.branch bv cs m) (n::key) cs n key v).map fun run =>
      pushPart run.inner ⟨if run.inserted then .RBI else .RDB,.branch bv cs m,
        .branch bv run.output (m+run.newMem-run.oldMem),n⟩
def traceKids (source : PTrie) (wholeKey : List Nat) : Kids → Nat → List Nat → Bytes → Option KidsRun
  | .nil, _, _, _ => none
  | .none rest, 0, key, v =>
    let fresh := newLeaf key v
    some ⟨.some fresh rest,0,leafMem key v.length,
      terminalRun source wholeKey .BI 0 fresh [⟨.NLF,source,fresh,0⟩],true⟩
  | .some c rest, 0, key, v =>
    match c.mem?, traceUpsert c key v with
    | some cm, some run => some ⟨.some run.output rest,cm,run.output.memD,run,false⟩
    | _, _ => none
  | .none rest, i+1, key, v =>
    (traceKids source wholeKey rest i key v).map fun run => {run with output := .none run.output}
  | .some c rest, i+1, key, v =>
    (traceKids source wholeKey rest i key v).map fun run => {run with output := .some c run.output}
end

end ZkFormal.NearV3.Render.UpsGen
