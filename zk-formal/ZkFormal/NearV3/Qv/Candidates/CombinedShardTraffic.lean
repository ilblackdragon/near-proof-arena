import ZkFormal.NearV3.Qv.Candidates.CombinedTerminalTraffic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

private theorem cast_sub (a b : Nat) (h : b≤a) :
    Fp.ofNat a + -Fp.ofNat b = Fp.ofNat (a-b) := by
  have he := Nat.sub_add_cancel h
  have hc := @Lean.Grind.Semiring.natCast_add Fp _ (a-b) b
  change Fp.ofNat ((a-b)+b) = Fp.ofNat (a-b)+Fp.ofNat b at hc
  rw [he] at hc
  grind

def Walk.shardMessages (w : Walk) (pos : Nat) (b : UInt8) : List Msg :=
  (if w.kind.code=3 ∧ pos≠0 then [[w.tau,w.slot-3,pos-1,b.toNat]] else []) ++
  (if pos+1=w.kind.bytes.length ∧ w.value.isSome=true ∧ w.tau=0 ∧ w.kind.code=1
    then [[w.tau,0,8,w.count]] else [])

theorem Walk.shard_field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0))
    (hs : w.kind.code=3 → 3≤w.slot) :
    rowTraffic CombinedTable.interactions tr t r pub B_QSH false =
      (w.shardMessages pos b).map Msg.toFp := by
  rw [w.parser_silent pos b tr t r pub hc]
  have h0 : Fp.ofNat 0 = 0 := rfl
  have h1 : Fp.ofNat 1 = 1 := rfl
  have hz : (0 : Fp) ≠ 1 := by decide
  have h3 : @Nat.cast Fp Lean.Grind.Semiring.natCast 3 = Fp.ofNat 3 := rfl
  have h8 : @Nat.cast Fp Lean.Grind.Semiring.natCast 8 = Fp.ofNat 8 := rfl
  by_cases hg : w.kind.code=3 <;> by_cases hp : pos=0 <;>
    by_cases hl : pos+1=w.kind.bytes.length <;> cases hv : w.value.isSome <;>
    by_cases ht : w.tau=0 <;> by_cases hb : w.kind.code=1
  all_goals simp [rowTraffic,walkInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,
    Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,Dsl.c,Dsl.not,Dsl.sub,Dsl.k,CombinedTable.groupByte,CombinedTable.countRead,
    CombinedTable.slot,CombinedTable.wp,CombinedTable.wb,ValueTable.tau,ValueTable.count,
    B_QSH,B_KEYNIB,B_FINAL,ValueTable.B_QVC,hc,Walk.shardMessages,Msg.toFp,
    Bool.toNat,hg,hp,hl,hv,ht,hb,h0,h1,h3,h8,hz,Lean.Grind.Semiring.natCast_zero,
    Lean.Grind.Semiring.natCast_one]
  all_goals try omega
  all_goals first
    | exact ⟨cast_sub w.slot 3 (hs hg), by simpa only [h1] using cast_sub pos 1 (by omega)⟩
    | split <;> simp [h0,h1,hz,Msg.toFp]


theorem mainPlan_group_slot (pre : NearSpec.PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) :
    ∀ w ∈ mainPlan pre v K resolve, w.kind.code=3 → 3≤w.slot := by
  simp [mainPlan,mainWalk,Kind.code]
  intro a x i _ he
  subst a
  simp

theorem implicitPlan_group_slot (pres : List NearSpec.PTrie) (resolve : Resolve) :
    ∀ w ∈ implicitPlan pres resolve, w.kind.code=3 → 3≤w.slot := by
  simp [implicitPlan,Kind.code]
  intro w x i _ he
  subst w
  simp

theorem plan_group_slot (pre : NearSpec.PTrie) (v : MainValues)
    (pres : List NearSpec.PTrie) (resolve : Resolve) :
    ∀ w ∈ plan pre v pres resolve, w.kind.code=3 → 3≤w.slot := by
  intro w hw
  rcases List.mem_append.mp hw with hm | hi
  · exact mainPlan_group_slot pre v pres.length resolve w hm
  · exact implicitPlan_group_slot pres resolve w hi

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

