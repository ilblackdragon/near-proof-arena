import ZkFormal.NearV3.Qv.Candidates.CombinedWalkTraffic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

/-- FINAL plus the request-side QVC counter step. -/
def terminalInteractions : List Interaction := (CombinedTable.interactions.drop 9).take 3

theorem Walk.terminal_filter (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0))
    (bus : Nat) (hb : bus=B_FINAL ∨ bus=ValueTable.B_QVC) (sd : Bool) :
    rowTraffic CombinedTable.interactions tr t r pub bus sd =
      rowTraffic terminalInteractions tr t r pub bus sd := by
  rw [w.parser_silent pos b tr t r pub hc]
  rcases hb with rfl | rfl <;>
    simp [rowTraffic,walkInteractions,terminalInteractions,CombinedTable.interactions,
      Dsl.send,Dsl.recv,B_KEYNIB,B_QSH,B_FINAL,ValueTable.B_QVC]

theorem Walk.terminal_nat_bits (w : Walk) (pos : Nat) (b : UInt8) :
    ∀ i ∈ terminalInteractions, (∀ e ∈ i.mult,
      rowNatExpr e=true ∧ rowNatEval (w.row pos b) e≤1) ∧
      (∀ e ∈ i.msg, rowNatExpr e=true) := by
  simp [terminalInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,
    rowNatExpr,rowNatEval,CombinedTable.wid,CombinedTable.readMode,
    CombinedTable.wl,CombinedTable.present,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum]
  cases (pos+1 == w.kind.bytes.length) <;> cases w.value.isSome <;> decide

def Walk.finalMessages (w : Walk) (pos : Nat) : List Msg :=
  if pos+1=w.kind.bytes.length then
    [[W_QV+w.tau+64*w.slot,w.tau,(!w.value.isSome).toNat,
      if w.value.isSome then w.vid else 0]] else []

def Walk.counterMessages (w : Walk) (pos : Nat) (sd : Bool) : List Msg :=
  if pos+1=w.kind.bytes.length ∧ w.value.isSome=true then
    [[w.vid,w.tau,w.mode,if sd then w.users+1 else w.users]] else []

theorem Walk.final_nat_messages (w : Walk) (pos : Nat) (b : UInt8) :
    natRowTraffic terminalInteractions (w.row pos b) B_FINAL false = w.finalMessages pos := by
  simp [natRowTraffic,terminalInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,
    natMultBits,rowNatEval,CombinedTable.wid,CombinedTable.wl,CombinedTable.absent,
    CombinedTable.slot,ValueTable.tau,ValueTable.vid,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,
    B_FINAL,ValueTable.B_QVC,Walk.finalMessages,Nat.add_assoc]
  by_cases h : pos+1=w.kind.bytes.length <;> simp [h]

theorem Walk.counter_nat_messages (w : Walk) (pos : Nat) (b : UInt8) (sd : Bool) :
    natRowTraffic terminalInteractions (w.row pos b) ValueTable.B_QVC sd =
      w.counterMessages pos sd := by
  cases sd <;> cases hv : w.value.isSome <;>
    simp [natRowTraffic,terminalInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,
      natMultBits,rowNatEval,CombinedTable.readMode,CombinedTable.present,ValueTable.len,
      ValueTable.users,ValueTable.tau,ValueTable.vid,Dsl.c,Dsl.k,B_FINAL,ValueTable.B_QVC,
      Walk.counterMessages,hv]
  all_goals by_cases h : pos+1=w.kind.bytes.length <;> simp [h]

theorem Walk.final_field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0)) :
    rowTraffic CombinedTable.interactions tr t r pub B_FINAL false =
      (w.finalMessages pos).map Msg.toFp := by
  rw [w.terminal_filter pos b tr t r pub hc _ (Or.inl rfl),
    rowTraffic_nat _ _ _ _ _ _ hc (w.terminal_nat_bits pos b),w.final_nat_messages]

theorem Walk.counter_field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0)) (sd : Bool) :
    rowTraffic CombinedTable.interactions tr t r pub ValueTable.B_QVC sd =
      (w.counterMessages pos sd).map Msg.toFp := by
  rw [w.terminal_filter pos b tr t r pub hc _ (Or.inr rfl),
    rowTraffic_nat _ _ _ _ _ _ hc (w.terminal_nat_bits pos b),w.counter_nat_messages]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
