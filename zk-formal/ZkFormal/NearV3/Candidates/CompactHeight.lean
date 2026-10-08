import ZkFormal.NearV3.Render.Ups.CompactAllocated
import ZkFormal.NearV3.Render.Ups.CompactExtract.KindSteps
import ZkFormal.NearV3.Render.Ups.Local
namespace ZkFormal.NearV3.Candidates.CompactHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render
open ZkFormal.NearV3 ZkFormal.NearV3.Render ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near.Dsl ZkFormal.NearV3.UpsRows ZkFormal.NearV3.UpsV3


section
variable {C D : URow} (ok : Extract.RowOk C D) (hC : ∀ x, C x < ZkFormal.Algebra.P) (hD : ∀ x, D x < ZkFormal.Algebra.P)
include ok hC

theorem bit01 {x : Nat} (hx : x ∈ rowBools) : uev C D (c x) = 0 ∨ uev C D (c x) = 1 := by
  rcases Extract.rowBool ok hC hx with h | h
  · left; show Fp.ofNat (C x) = 0; rw [h]; rfl
  · right; show Fp.ofNat (C x) = 1; rw [h]; rfl

/-- `mS + mK ≤ 1`: the modes are bits and so is the drain flag `wk − mS − mK − mB`. -/
theorem modes01 : C mS + C mK ≤ 1 := by
  have b := fun {x} (hx : x ∈ rowBools) => Extract.rowBool ok hC hx
  have bS := b (x := mS) (by simp [rowBools])
  have bK := b (x := mK) (by simp [rowBools])
  have bB := b (x := mB) (by simp [rowBools])
  have bW := b (x := wk) (by simp [rowBools])
  have h := Extract.fact ok (e := Dsl.bool mDE) (by unfold compactConstraints cBool; simp)
  simp only [uev, Expr.evalWith, uEnv, Dsl.bool, Dsl.sub, Dsl.k, Dsl.c, mDE, if_false,
    Bool.false_eq_true] at h
  rcases bS with hS | hS <;> rcases bK with hK | hK <;> rcases bB with hB | hB <;> rcases bW with hW | hW <;>
    rw [hS, hK, hB, hW] at h <;> first | omega | exact absurd h (by decide)

end

/-- Every interaction gate of `upsV3` is a bit on a row satisfying the constraints. -/
theorem gates01 {C D : URow} (ok : Extract.RowOk C D) (hC : ∀ x, C x < ZkFormal.Algebra.P) (hD : ∀ x, D x < ZkFormal.Algebra.P) :
    ∀ i ∈ UpsV3.interactions, ∀ g ∈ i.mult, uev C D g = 0 ∨ uev C D g = 1 := by
  intro i hi g hg
  simp only [UpsV3.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
  have K := Extract.kinds ok hC hD
  obtain ⟨hact, hsum, -⟩ := K
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_singleton] at hg <;> subst hg
  all_goals first
    | exact bit01 ok hC (by simp [rowBools])
    | skip
  · -- vb + qb
    have : C vb + C qb ≤ 1 := by
      have := Extract.rowBool ok hC (x := wk) (by simp [rowBools]); omega
    show Fp.ofNat (C vb) + Fp.ofNat (C qb) = 0 ∨ Fp.ofNat (C vb) + Fp.ofNat (C qb) = 1
    rcases (show (C vb = 0 ∧ C qb = 0) ∨ (C vb = 1 ∧ C qb = 0) ∨ (C vb = 0 ∧ C qb = 1) by
      have := Extract.rowBool ok hC (x := vb) (by simp [rowBools])
      have := Extract.rowBool ok hC (x := qb) (by simp [rowBools]); omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rw [a, b] <;> decide
  all_goals
    have hm := modes01 ok hC
    show Fp.ofNat (C mS) + Fp.ofNat (C mK) = 0 ∨ Fp.ofNat (C mS) + Fp.ofNat (C mK) = 1
    rcases (show (C mS = 0 ∧ C mK = 0) ∨ (C mS = 1 ∧ C mK = 0) ∨ (C mS = 0 ∧ C mK = 1) by
      have := Extract.rowBool ok hC (x := mS) (by simp [rowBools])
      have := Extract.rowBool ok hC (x := mK) (by simp [rowBools]); omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rw [a, b] <;> decide

def trace (insts : List UpsInst) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>(compactCell insts r c : Fp)⟩

theorem constraints (insts : List UpsInst) (h : CompactGroupOk insts (2^22) compactConstraints)
    (t : Nat) (pub : List Fp) (r : Nat) (hr : r<(trace insts).height t) :
    ∀e∈compactConstraints,e.eval (trace insts) t r pub=0 := by
  intro e he
  rw [EvI.ev_sound (C:=compactCell insts r) (D:=compactCell insts ((r+1)%2^22))
    (by intros; rfl) (by intros; rfl) e]
  exact h r hr _ _ _ (by intros; rfl) (by intros; rfl) e he

theorem trace_local (insts : List UpsInst) (h : CompactGroupOk insts (2^22) compactConstraints)
    (t : Nat) (pub : List Fp) : TableLocal compactTable (trace insts) t pub := by
  have hcon := constraints insts h t pub
  refine ⟨by change 1≤22; decide,by change 22≤22; decide,hcon,?_⟩
  intro r hr i hi g hg
  have hi' : i∈UpsV3.interactions := by
    rcases List.mem_append.mp hi with hi|hi
    · exact List.mem_of_mem_take hi
    · exact List.mem_of_mem_drop hi
  have ok : Extract.RowOk (rowC (trace insts) t r) (rowC (trace insts) t ((r+1)%(trace insts).height t)) := by
    intro e he hp
    rw [← eval_pure (trace insts) t r pub e hp]
    exact hcon r hr e he
  have hp : g.pure=true := by
    have hh := List.all_eq_true.mp interactions_pure i hi'
    simp only [Bool.and_eq_true] at hh
    have h1 := hh.1
    unfold pureGate at h1
    split at h1
    · rename_i g' hgm
      rw [hgm] at hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact h1
    · exact absurd h1 (by simp)
  rw [eval_pure (trace insts) t r pub g hp]
  exact gates01 ok (fun x=>rowC_lt _ _ _ x) (fun x=>rowC_lt _ _ _ x) i hi' g hg

open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly UpsGen in
theorem accepted_trace {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ (us : List SchedulerUpsertWitness) (insts : List UpsInst),
      1≤us.length ∧ us.length≤32 ∧ insts.length=us.length ∧ compactR insts+1≤2^22 ∧
      (∀tau u I,us[tau]?=some u → insts[tau]?=some I →
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) ∧
      ∀t pub,TableLocal compactTable (trace insts) t pub ∧ (trace insts).log t=22 := by
  obtain ⟨us,insts,hpos,hlen,hl,hcap,ha,hG⟩:=checkD0a_compact_constraints hk hw h baseI base
  exact ⟨us,insts,hpos,hlen,hl,hcap,ha,fun t pub=>⟨trace_local insts hG t pub,rfl⟩⟩
end ZkFormal.NearV3.Candidates.CompactHeight
