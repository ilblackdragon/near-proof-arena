import ZkFormal.NearV3.Rcpt.Tables.Rcpt
import ZkFormal.NearV3.Public.Boundary
import ZkFormal.NearV3.Rcpt.Render.BndRender
import ZkFormal.NearV3.Rcpt.Link.OwnIntervals

namespace ZkFormal.NearV3.RcptLink.RoutingAlias
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec
open RcptV3

/-- 65*q aliases public boundary row2 while receipt position is0. -/
def aliasQ : Nat := 1796452668

theorem key_alias : aliasQ<P ∧ ((65*aliasQ:Nat):Fp)=(2:Fp) ∧ 65*aliasQ≠2 := by decide

def layout : NearSpecV3.Layout := ⟨[[122,122]],[0,1],[(0,0),(1,1)]⟩

theorem native_wrong_route :
    AccountId.valid [97,97]=true ∧ AccountId.valid [122,122]=true ∧
    NearSpecV3.ownIntervals layout 1=[(some [122,122],none)] ∧
    layout.shardOf [97,97]=0 ∧
    NearSpecV3.inIntervals (NearSpecV3.ownIntervals layout 1) [97,97]=false := by decide

theorem public_suffix_record :
    Public.boundaryRow [(some [122,122],none)] 2=[0,0,1] := by decide

/-- Only the routing subsystem fixture is asserted; other receipt constraints
and whole-AIR acceptance are not claimed by this example. -/
def cells (r c : Nat) : Nat :=
  if c=q then aliasQ else
  if c=Lv then 2 else
  if c=sV then if r<2 then 1 else 0 else
  if c=sRID then if r=2 then 1 else 0 else
  if c=fs then if r=0 ∨ r=2 then 1 else 0 else
  if c=b ∨ c=vB then if r<2 then 97 else 0 else
  if c=idx ∨ c=iB then r else
  if c=eqL ∨ c=gBd ∨ c=hnB then if r=0 then 1 else 0 else
  if c=iL then if r=0 then 1556648908 else 0 else
  if c=iH then if r=0 then 456617013 else 0 else
  if 158≤c ∧ c<167 then if r=0 then (352/2^(c-158))%2 else 0 else
  if 167≤c ∧ c<176 then if r=0 then (158/2^(c-167))%2 else 0 else 0

def trace : Trace Fp := ⟨fun _ => 2,fun _ r c => Fp.ofNat (cells r c)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem route_constraints_pass :
    ([0,1,2].all fun r => cRoute.all fun e => decide (e.eval trace 0 r []=0))=true := by decide

set_option maxRecDepth 4096 in
theorem boundary_request_alias :
    ((bndMsg (.const 0)).map fun e => e.eval trace 0 0 [])=[2,0,0,1,0] := by decide

/-- Syntactic dependency audit for every actual receipt constraint. -/
def readsQ : Expr → Bool
  | .col c _ => c==q
  | .add a b | .mul a b => readsQ a || readsQ b
  | .neg a => readsQ a
  | _ => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem only_q_constraint :
    constraints.filter readsQ=
      [Dsl.mul3 rowE (Dsl.not (Dsl.c rl)) (Dsl.sub (Dsl.n q) (Dsl.c q))] := by decide

def providers : List BndE := (List.range 65).map fun i =>
  ⟨i,if i<2 then 122 else 0,0,1,if i=2 then 1 else 0⟩

def bndTrace : Trace Fp := ⟨fun _ => 7,fun _ r c => Fp.ofNat (Render.BndGen.cell providers r c)⟩

theorem bnd_local (pub : List Fp) : TableLocal BndV3.table bndTrace 0 pub := by
  apply Render.bnd_render_local_at providers bndTrace 0 pub BndV3.maxLog
  · decide
  · intro r c hr hc
    rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem public_records_match :
    (providers.map (fun e => e.rec4.toFp))=
      (List.range 65).map (fun i => [Fp.ofNat i]++
        (Public.boundaryRow [(some [122,122],none)] i).map (fun b => Fp.ofNat b.toNat)) := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem bnd_counter_balance :
    ((providers.map (fun (e : BndE) => (e.rec4++[0]).toFp))++[[2,0,0,1,1]]).Perm
      ((providers.map (fun (e : BndE) => (e.rec4++[e.U]).toFp))++[[2,0,0,1,0]]) := by decide

end ZkFormal.NearV3.RcptLink.RoutingAlias
