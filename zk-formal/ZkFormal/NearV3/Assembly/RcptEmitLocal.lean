import ZkFormal.NearV3.Assembly.RcptEmitRules

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def emissionGateExpr : Expr→Bool
  | .const n=>n==1
  | .col c false=>c==hr
  | _=>false

set_option maxRecDepth 4096 in
theorem emits_gate_forms : emits.all (fun p=>p.2.all (fun em=>emissionGateExpr em.2.2.2))=true := by decide

theorem emissionGate_eval (base : Trace Fp) (pub : List Fp) (t pos : Nat)
    (hhr : base.cell t pos hr=0 ∨ base.cell t pos hr=1)
    (g : Expr) (hg : emissionGateExpr g=true) :
    g.eval base t pos pub=0 ∨ g.eval base t pos pub=1 := by
  cases g with
  | const n => simp only [emissionGateExpr,beq_iff_eq] at hg;subst n;exact Or.inr rfl
  | col c nx =>
    cases nx with
    | true => cases hg
    | false => simp only [emissionGateExpr,beq_iff_eq] at hg;subst c;exact hhr
  | pub | isFirst | isLast | isTransition | add | mul | neg => cases hg

theorem emissionValues_gate_bool (base : Trace Fp) (pub : List Fp) (t pos state slot : Nat)
    (hhr : base.cell t pos hr=0 ∨ base.cell t pos hr=1) :
    (emissionValues base pub t pos state slot).gate=0 ∨
    (emissionValues base pub t pos state slot).gate=1 := by
  unfold emissionValues
  cases hm : emits.find? (fun p=>p.1==state) with
  | none => exact Or.inl rfl
  | some entry =>
    rcases entry with ⟨s,ems⟩
    dsimp only
    have hmem := List.mem_of_find?_eq_some hm
    have hall := List.all_eq_true.mp emits_gate_forms (s,ems) hmem
    cases he : ems[slot]? with
    | none => exact Or.inl rfl
    | some em =>
      rcases em with ⟨id,p,v,g⟩
      exact emissionGate_eval base pub t pos hhr g (List.all_eq_true.mp hall _ (List.mem_of_getElem? he))

/-- All 189 unchanged cEmit constraints on the emission-extended trace. The
only inputs are actual row state/control values and the Boolean refund flag. -/
theorem emissionPatch_cEmit (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos : Nat)
    (hstate : ∀s∈states,base.cell t pos s=if s=stateAt t pos then 1 else 0)
    (hact : base.cell t pos act=if stateAt t pos=0 then 0 else 1)
    (hhr : base.cell t pos hr=0 ∨ base.cell t pos hr=1) :
    ∀e∈cEmit,e.eval (emissionPatch base pub stateAt) t pos pub=0 := by
  intro e he
  rw [cEmit_parts] at he
  simp only [List.mem_append,or_assoc] at he
  rcases he with he|he|he
  · obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp he
    have hs' := List.mem_range.mp hs
    have hg := (emissionPatch_slot base pub stateAt t pos slot hs').2.2.2
    have hb := emissionValues_gate_bool base pub t pos (stateAt t pos) slot hhr
    simp only [eval_bool,eval_c]
    rw [hg]
    rcases hb with hb|hb <;> rw [hb] <;> grind only
  · obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp he
    have hs' := List.mem_range.mp hs
    simp only [eval_mul,eval_not,eval_c]
    rw [emissionPatch_other base pub stateAt t pos act (by decide),hact]
    by_cases hz : stateAt t pos=0
    · rw [(emissionPatch_slot base pub stateAt t pos slot hs').2.2.2,hz]
      simp only [emissionValues,emits_zero_lookup]
      change _*(0:Fp)=0
      grind only
    · simp [hz]
      grind only
  · exact emissionPatch_rules base pub stateAt t pos hstate e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
