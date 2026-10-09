import ZkFormal.NearV3.Assembly.RcptEmitCatalog

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def emissionRules : List Expr := emits.flatMap fun (s,ems)=>
  (List.range 3).flatMap fun slot=>match ems[slot]? with
  | some (id,p,v,g)=>
    [.mul (c s) (sub (c (eId slot)) id),.mul (c s) (sub (c (ePos slot)) p),
      .mul (c s) (sub (c (eV slot)) v),.mul (c s) (sub (c (eG slot)) g)]
  | none=>[.mul (c s) (c (eG slot))]

theorem cEmit_parts : cEmit=
    (List.range 3).map (fun e=>bool (c (eG e)))++
    (List.range 3).map (fun e=>.mul (not (c act)) (c (eG e)))++emissionRules := rfl

theorem emits_states : ∀p∈emits,p.1∈states := by decide

theorem emissionPatch_state (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos s : Nat) (hs : s∈states) : (emissionPatch base pub stateAt).cell t pos s=base.cell t pos s := by
  apply emissionPatch_other
  have hh := states_limits hs
  simp [emissionColumn]
  omega

/-- Every catalog emission equation on the same emission-extended trace.
State one-hotness is ordinary constructor data; byte/hash ownership is separate. -/
theorem emissionPatch_rules (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos : Nat)
    (hstate : ∀s∈states,base.cell t pos s=if s=stateAt t pos then 1 else 0) :
    ∀e∈emissionRules,e.eval (emissionPatch base pub stateAt) t pos pub=0 := by
  intro e he
  obtain ⟨⟨s,ems⟩,hs,he⟩ := List.mem_flatMap.mp he
  obtain ⟨slot,hslot,he⟩ := List.mem_flatMap.mp he
  have hslot' := List.mem_range.mp hslot
  have hstates := emits_states (s,ems) hs
  have hst : (emissionPatch base pub stateAt).cell t pos s=if s=stateAt t pos then 1 else 0 :=
    (emissionPatch_state base pub stateAt t pos s hstates).trans (hstate s hstates)
  obtain ⟨hid,hpos,hv,hg⟩ := emissionPatch_slot base pub stateAt t pos slot hslot'
  by_cases hsel : s=stateAt t pos
  · cases hm : ems[slot]? with
    | none =>
      simp only [hm,List.mem_singleton] at he
      subst e
      simp only [eval_mul,eval_c]
      rw [hg,←hsel,emissionValues_none base pub t pos s slot ems hs hm]
      change _*(0:Fp)=0
      grind only
    | some em =>
      rcases em with ⟨id,p,v,g⟩
      have hvals := emissionValues_some base pub t pos s slot ems hs id p v g hm
      obtain ⟨hidi,hpi,hvi,hgi⟩ := emission_noSelf s ems hs id p v g (List.mem_of_getElem? hm)
      simp only [hm,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl|rfl
      all_goals simp only [eval_mul,eval_sub,eval_c]
      · rw [hid,←hsel,hvals,emissionPatch_eval base pub stateAt t pos id hidi];grind only
      · rw [hpos,←hsel,hvals,emissionPatch_eval base pub stateAt t pos p hpi];grind only
      · rw [hv,←hsel,hvals,emissionPatch_eval base pub stateAt t pos v hvi];grind only
      · rw [hg,←hsel,hvals,emissionPatch_eval base pub stateAt t pos g hgi];grind only
  · have hz : (emissionPatch base pub stateAt).cell t pos s=0 := by simp [hst,hsel]
    cases hm : ems[slot]? with
    | none =>
      simp only [hm,List.mem_singleton] at he
      subst e
      simp only [eval_mul,eval_c,hz]
      grind only
    | some em =>
      rcases em with ⟨id,p,v,g⟩
      simp only [hm,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl|rfl <;>
        simp only [eval_mul,eval_sub,eval_c,hz] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
