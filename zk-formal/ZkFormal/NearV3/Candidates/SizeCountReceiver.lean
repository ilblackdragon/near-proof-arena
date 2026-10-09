import ZkFormal.NearV3.Candidates.TrieCountComplete
import ZkFormal.NearV3.Rcpt.Render.SizeRender
namespace ZkFormal.NearV3.Candidates.SizeCountReceiver
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount HorizontalTraffic

/-- Exactly the two charged store record counts. Source messages have no store
record headers; their structural overhead is paid in the public overhead. -/
structure Counts where
  nodes : Nat
  values : Nat

def countAt (ns : Counts) : Nat → Nat
  | 0 => ns.nodes
  | 1 => ns.values
  | _ => 0

def totalAt (ns : Counts) : Nat → Nat
  | 0 => ns.nodes
  | 1 => ns.nodes+ns.values
  | 2 => ns.nodes+ns.values
  | _ => 0

/-- Final slack pays four bytes for every retained store-record length prefix. -/
def slack (pub : List Fp) (v : SizeV) (ns : Counts) : Nat → Nat
  | 1 => 3000000-(v.x0+v.x1)
  | 2 => 8388608-ovhNat pub-(v.x0+v.x1+v.x2)-4*(ns.nodes+ns.values)
  | _ => 0

def cell (pub : List Fp) (v : SizeV) (ns : Counts) (r c : Nat) : Nat :=
  if c=count then countAt ns r
  else if c=countTotal then totalAt ns r
  else if 7≤c ∧ c<31 then (slack pub v ns r / 2^(c-7))%2
  else SizeGen.cell pub v r c

def trace (pub : List Fp) (v : SizeV) (ns : Counts) : Trace Fp :=
  ⟨fun _=>2,fun _ r c=>Fp.ofNat (cell pub v ns r c)⟩

structure Valid (pub : List Fp) (v : SizeV) (ns : Counts) : Prop where
  base : v.x0+v.x1≤3000000
  total : ovhNat pub+v.x0+v.x1+v.x2+4*(ns.nodes+ns.values)≤8388608

def messages (v : SizeV) (ns : Counts) : List Near.Msg :=
  [[0,v.x0,ns.nodes],[1,v.x1,ns.values],[2,v.x2,0]]

def traffic (v : SizeV) (ns : Counts) : Traffic :=
  ⟨fun _=>[],fun b=>if b=B_SIZE then messages v ns else []⟩

/-- All actual SIZE receiver traffic, including silent row3 and all other buses. -/
theorem receiver_traffic (pub : List Fp) (v : SizeV) (ns : Counts) (t : Nat) :
    TableTraffic sizeTable.interactions (trace pub v ns) t pub (traffic v ns) := by
  intro b m
  simp only [table_sum]
  change _ = 0 ∧ _ = _
  have hf : (List.range ((trace pub v ns).height t))=[0,1,2,3] := rfl
  rw [hf]
  by_cases hb : b=B_SIZE
  all_goals simp [hb,show (B_SIZE=b)=(b=B_SIZE) from propext eq_comm,SizeRender.ofNat0,SizeRender.ofNat1,rowCount,sizeTable,SizeV3.table,SizeV3.interactions,withCount,Dsl.recv,
    Interaction.msgVal,Interaction.multNat,Interaction.multNat.go,
    Dsl.c,Expr.eval,Expr.evalWith,rowEnv,trace,cell,count,countTotal,
    SizeGen.cell,SizeGen.xAt,SizeV3.width,SizeV3.act,SizeV3.t,SizeV3.x,
    countAt,traffic,messages,Near.Msg.toFp,List.count_cons]
  all_goals omega

/-- The final slack is small enough for the existing 24-bit decomposition. -/
theorem slack_bound (pub : List Fp) (v : SizeV) (ns : Counts) (r : Nat) :
    slack pub v ns r<2^24 := by
  unfold slack
  split <;> omega

theorem final_accounting (pub : List Fp) (v : SizeV) (ns : Counts) (h : Valid pub v ns) :
    slack pub v ns 2+ovhNat pub+v.x0+v.x1+v.x2+4*(ns.nodes+ns.values)=8388608 := by
  have := h.total
  simp only [slack]
  omega
end ZkFormal.NearV3.Candidates.SizeCountReceiver
