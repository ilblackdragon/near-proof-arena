import ZkFormal.NearV3.Assembly.RoutingFrameCells

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem frame_natcast (n : Nat) : Fp.ofNat n=(n:Fp) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem frame_route_constraints (f : RouteFrame) (hf : f.Ordered) (pub : List Fp) :
    ∀e∈cRoute,e.eval (frameTrace f) 0 0 pub=0 := by
  have hl := frame_lower_bits f pub
  have hu := frame_upper_bits f pub
  have hil := frame_diff_inverse f.value f.lower
  have hiu := frame_diff_inverse f.upper f.value
  have hbl : f.equalLower=true → f.value≠f.lower →
      frameBit (f.value.toNat+255-f.lower.toNat) 8=1 := by
    intro he hn
    unfold frameBit
    rw [frame_diff_high _ _ (hf.lower he) hn]
    rfl
  have hbu : f.equalUpper=true → f.upper≠f.value →
      frameBit (f.upper.toNat+255-f.value.toNat) 8=1 := by
    intro he hn
    unfold frameBit
    rw [frame_diff_high _ _ (hf.upper he) hn]
    rfl
  have hend : f.atEnd=true → f.equalUpper=true → f.upper≠f.value := by
    intro he hh hn
    have := hf.strictEnd he hh
    rw [hn] at this
    omega
  have hzero := hf.endZero
  have hzcast : f.atEnd=true → (f.value.toNat:Fp)=0 := by
    intro he; rw [hzero he]; rfl
  have hfirstL := hf.firstLower
  have hfirstU := hf.firstUpper
  intro e he
  simp only [cRoute,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he <;> subst e
  all_goals simp only [eval_sub,eval_c,eval_add,eval_mul,eval_mul3,eval_not,eval_k,eval_n,rwE,orE,hl,hu]
  all_goals dsimp only [frameTrace,Trace.height]
  all_goals simp only [Nat.one_mod, Nat.reducePow, Nat.reduceAdd, ↓reduceIte,
frame_cell_0,frame_cell_1,frame_cell_2,frame_cell_3,frame_cell_4,frame_cell_5,frame_cell_6,frame_cell_7,frame_cell_8,frame_cell_9,frame_cell_10,frame_cell_11,frame_cell_12,frame_cell_13,frame_cell_14,frame_cell_15,frame_cell_16,frame_cell_17,frame_cell_18,frame_cell_19,frame_next_lower,frame_next_upper]
  all_goals try simp only [frame_next_lower,frame_next_upper]
  all_goals try unfold frameInverse

  all_goals try simp only [frame_natcast]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hiu hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hbl hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbu hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hend hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]
  · clear hf hl hu hil hiu hbl hbu hzero hzcast hfirstL hfirstU
    grind only [frameNext,eqL,eqH]

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
