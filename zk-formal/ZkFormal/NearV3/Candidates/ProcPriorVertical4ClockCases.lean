import ZkFormal.NearV3.Candidates.ProcPriorVertical4Eval
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockCases
open ZkFormal.Air ZkFormal.Algebra
open ProcPriorVertical4Linear

def flag (b : Bool) : Fp:=if b then 1 else 0

def cell (data : Nat→Fp) (s : Nat) (f l : Bool) (c : Nat) : Fp:=
  if c<23 then data c else
  if c<27 then flag (decide (c=23+s)) else
  if c=27 then flag f else
  if c=28 then flag l else 0

def markerEnv (s sn : Nat) (f l fn gf gl : Bool) : Env Fp:=
  ProcPriorCells.env (cell (fun _=>0) s f l) (cell (fun _=>0) sn fn false)
    (flag gf) (flag gl) (flag (!gl))

def Valid (s sn : Nat) (f l fn gf gl : Bool) : Prop:=
  (gf=true→s=0 ∧ f=true) ∧ (gl=true→s=3 ∧ l=true) ∧
  (gl=false→fn=l ∧ (if l then s<3 ∧ sn=s+1 else sn=s))
instance (s sn : Nat) (f l fn gf gl : Bool) : Decidable (Valid s sn f l fn gf gl) :=
  inferInstanceAs (Decidable ((gf=true→s=0 ∧ f=true) ∧ (gl=true→s=3 ∧ l=true) ∧
    (gl=false→fn=l ∧ (if l then s<3 ∧ sn=s+1 else sn=s))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem checked_cases : ∀s sn : Fin 4,∀f l fn gf gl : Bool,
    Valid s.val sn.val f l fn gf gl→
    windows.all (fun e=>decide (e.evalWith (markerEnv s.val sn.val f l fn gf gl)=0))=true := by
  decide +kernel

theorem marker_constraints (s sn : Nat) (hs:s<4) (hn:sn<4) (f l fn gf gl : Bool)
    (hv:Valid s sn f l fn gf gl) : ∀e∈windows,e.evalWith (markerEnv s sn f l fn gf gl)=0 :=
  fun e he=>of_decide_eq_true (List.all_eq_true.mp (checked_cases ⟨s,hs⟩ ⟨sn,hn⟩ f l fn gf gl hv) e he)
end ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockCases
