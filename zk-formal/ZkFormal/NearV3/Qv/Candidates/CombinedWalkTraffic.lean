import ZkFormal.NearV3.Qv.Candidates.CombinedWalkBits
import ZkFormal.NearV3.Qv.Candidates.NaturalTraffic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

/-- The walk suffix excludes the five parser-provider interactions. -/
def walkInteractions : List Interaction := CombinedTable.interactions.drop 5

/-- A generated walk marker emits no parser traffic, including raw-empty rows.
No local-acceptance or bus-balance premise is needed. -/
theorem Walk.parser_silent (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0))
    (bus : Nat) (sd : Bool) :
    rowTraffic CombinedTable.interactions tr t r pub bus sd =
      rowTraffic walkInteractions tr t r pub bus sd := by
  have h0 : Fp.ofNat 0 = 0 := rfl
  have h1 : Fp.ofNat 1 = 1 := rfl
  have hz : (0 : Fp) ≠ 1 := by decide
  have hcancel : (1 : Fp) + -1 = 0 := by grind
  simp [rowTraffic,CombinedTable.interactions,walkInteractions,Dsl.send,Dsl.recv,
    Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,Dsl.c,Dsl.not,Dsl.sub,Dsl.k,ValueTable.headerEnd,ValueTable.gb,ValueTable.vf,
    ValueTable.shard,ValueTable.header,ValueTable.sel,CombinedTable.walk,hc,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul,h0,h1,hz,hcancel]


def keyInteractions : List Interaction := (CombinedTable.interactions.drop 5).take 4

theorem key_traffic_filter (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic CombinedTable.interactions tr t r pub B_KEYNIB true =
      rowTraffic keyInteractions tr t r pub B_KEYNIB true := by
  simp [rowTraffic,CombinedTable.interactions,keyInteractions,Dsl.send,Dsl.recv,
    B_KEYNIB,B_VBYTES,B_QSH,B_FINAL,ValueTable.B_QVC]

theorem Walk.key_nat_bits (w : Walk) (pos : Nat) (b : UInt8) :
    ∀ i ∈ keyInteractions, (∀ e ∈ i.mult,
      rowNatExpr e=true ∧ rowNatEval (w.row pos b) e≤1) ∧
      (∀ e ∈ i.msg, rowNatExpr e=true) := by
  simp [keyInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,
    rowNatExpr,rowNatEval,CombinedTable.wid,CombinedTable.nibble,
    CombinedTable.wf,CombinedTable.wl,CombinedTable.walk,ValueTable.reg,
    Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,List.range_succ]
  constructor
  · cases (pos == 0) <;> decide
  · cases (pos+1 == w.kind.bytes.length) <;> decide

theorem Walk.key_field_traffic (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0)) :
    rowTraffic CombinedTable.interactions tr t r pub B_KEYNIB true =
      (natRowTraffic keyInteractions (w.row pos b) B_KEYNIB true).map Msg.toFp := by
  rw [key_traffic_filter]
  exact rowTraffic_nat _ _ _ _ _ _ hc (w.key_nat_bits pos b) _ _


def Walk.keyMessages (w : Walk) (pos : Nat) (b : UInt8) : List Msg :=
  let wid := W_QV+w.tau+64*w.slot
  (if pos=0 then [[wid,0,SYM_START,0]] else []) ++
  [[wid,2*pos+1,b.toNat/16,0],[wid,2*pos+2,b.toNat%16,0]] ++
  (if pos+1=w.kind.bytes.length then [[wid,2*pos+3,SYM_END,1]] else [])

theorem Walk.key_messages (w : Walk) (pos : Nat) (b : UInt8) :
    natRowTraffic keyInteractions (w.row pos b) B_KEYNIB true = w.keyMessages pos b := by
  have hi := w.high_nibble pos b
  have lo := w.low_nibble pos b
  simp only [keyInteractions,CombinedTable.interactions,List.drop,List.take,
    natRowTraffic,List.flatMap_cons,List.flatMap_nil,Dsl.send,Dsl.recv,
    natMultBits,List.map_cons,List.map_nil]
  simp [CombinedTable.wf,CombinedTable.wl,CombinedTable.walk,CombinedTable.wp,
    CombinedTable.wid,CombinedTable.slot,ValueTable.tau,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,
    rowNatEval,Walk.keyMessages] at hi lo ⊢
  by_cases hf : pos=0
  · subst pos
    by_cases hl : 1=w.kind.bytes.length
    · simp [← hl,Walk.high_nibble,Walk.low_nibble,Nat.add_assoc]
    · simp [hl,Walk.high_nibble,Walk.low_nibble,Nat.add_assoc]
  · by_cases hl : pos+1=w.kind.bytes.length <;> simp [hf,hl,hi,lo,Nat.add_assoc]


theorem Walk.key_field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0)) :
    rowTraffic CombinedTable.interactions tr t r pub B_KEYNIB true =
      (w.keyMessages pos b).map Msg.toFp := by
  rw [w.key_field_traffic pos b tr t r pub hc,w.key_messages]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen



