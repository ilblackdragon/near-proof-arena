import ZkFormal.NearV3.Candidates.ShaHeight.Families
import ZkFormal.NearV3.Candidates.ShaHeight.Current
import ZkFormal.NearV3.Candidates.ShaHeight.Steps
import ZkFormal.Near.Extract.Common
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha ZkFormal.Sha.Complete ZkFormal.Sha.Gen ZkFormal.Sha.Layout

/-- Native SHA rows at an explicit physical clock. Padding is the native `.pad`
row, with validity of the cyclic boundary proved by `step_at_height`. -/
def fixedTrace (msgs : List Gen.Msg) (L : Nat) : Trace Fp :=
  ⟨fun _=>L,fun _ r c=>Fp.ofNat (honestCell msgs r c)⟩

def fenv (msgs : List Gen.Msg) (L r : Nat) (pub : List Fp) : ZEnv :=
  renv (rowAt msgs r) (rowAt msgs ((r+1)%2^L))
    (if r=0 then 1 else 0) (if r+1=2^L then 1 else 0)
    (fun i=>(pub.getD i 0).toNat)

theorem eval_fixed (msgs : List Gen.Msg) (L t r : Nat) (pub : List Fp) :
    ∀ e : Expr, e.eval (fixedTrace msgs L) t r pub = ((zev (fenv msgs L r pub) e : Int) : Fp)
  | .const c => by rw [Ev.eval_const]; simp only [zev]; rw [intCast_ofNat]
  | .col c nx => by
    cases nx
    · rw [Ev.eval_col]; simp only [zev, Bool.false_eq_true, ite_false]; rw [intCast_ofNat]; rfl
    · rw [Ev.eval_colNext]; simp only [zev, ite_true]; rw [intCast_ofNat]; rfl
  | .pub i => by
    show (pub.getD i 0) = (((pub.getD i 0).toNat : Int) : Fp)
    rw [intCast_ofNat, Fp.ofNat_toNat]
  | .isFirst => by
    rw [Ev.eval_isFirst]
    show _ = (((if r = 0 then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isLast => by
    show (if r + 1 = (fixedTrace msgs L).height t then 1 else 0 : Fp) =
      (((if r + 1 = (fixedTrace msgs L).height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isTransition => by
    show (if r + 1 = (fixedTrace msgs L).height t then 0 else 1 : Fp) =
      (((1 - if r + 1 = (fixedTrace msgs L).height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .add a b => by
    rw [Ev.eval_add, eval_fixed msgs L t r pub a, eval_fixed msgs L t r pub b]; simp only [zev]
    rw [intCast_add]
  | .mul a b => by
    rw [Ev.eval_mul, eval_fixed msgs L t r pub a, eval_fixed msgs L t r pub b]; simp only [zev]
    rw [intCast_mul]
  | .neg a => by
    rw [Ev.eval_neg, eval_fixed msgs L t r pub a]; simp only [zev]; rw [intCast_neg]


theorem fixed_local (msgs : List Gen.Msg) (hok : MsgsOk msgs) (L t : Nat) (pub : List Fp)
    (bb bd : Nat) (hL : 1≤L ∧ L≤22) (hrows : (honestRows msgs).length≤2^L) :
    TableLocal (Table.table bb bd) (fixedTrace msgs L) t pub := by
  refine ⟨hL.1,hL.2,?_,?_⟩
  · intro r hr e he
    rw [eval_fixed]
    change ((zev (fenv msgs L r pub) e):Fp)=((0:Int):Fp)
    apply congrArg (fun z : Int=>(z:Fp))
    have hs := step_at_height msgs hok (2^L) r hrows hr
    have hf : (if r=0 then 1 else 0 : Int)=0 ∨ rowAt msgs r=.pad ∨ ∃id,rowAt msgs r=.start id := by
      by_cases h:r=0
      · right; subst r; exact row0 msgs
      · left; simp [h]
    simp only [Table.table,Sha.Table.constraints,List.mem_append] at he
    rcases he with ((((((he|he)|he)|he)|he)|he)|he)|he
    · exact family_bool _ _ _ _ _ e he
    · exact family_kind _ _ hs _ _ _ hf e he
    · exact family_iv _ _ _ _ _ e he
    · exact family_round _ _ hs _ _ _ e he
    · exact family_sched _ _ hs _ _ _ e he
    · exact family_help _ _ hs _ _ _ e he
    · exact family_digest _ _ hs _ _ _ e he
    · exact family_frame _ _ hs _ _ _ e he
  · intro r hr i hi b hb
    rw [eval_fixed]
    have key : ∃x,b=Sha.Table.E.c x ∧ rowCell (rowAt msgs r) x≤1 := by
      simp only [Table.table,Sha.Table.interactions,List.mem_append,List.mem_map,List.mem_range,
        List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with ⟨q,hq,rfl⟩|rfl
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        exact ⟨colF q,hb,rowCell_bool _ _ (by unfold colF; omega)⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        exact ⟨colDmult,hb,cell_Dmult_le _⟩
    obtain ⟨x,rfl,hx⟩ := key
    change ((rowCell (rowAt msgs r) x : Int):Fp)=0 ∨ ((rowCell (rowAt msgs r) x : Int):Fp)=1
    rcases (show rowCell (rowAt msgs r) x=0 ∨ rowCell (rowAt msgs r) x=1 by omega) with hz|ho
    · left; rw [hz]; rfl
    · right; rw [ho]; rfl
end ZkFormal.NearV3.Candidates.ShaHeight
