import ZkFormal.NearV3.Render.Ups.CompactConstants
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen
set_option maxHeartbeats 1000000

theorem compactRows_old {C D P : Nat→Int} {fst lst trn : Int}
    (hv : C vb=0) (hw : C wt3=0)
    (hh : ∀e∈UpsV3.cRows,((ev C D fst lst trn P e : Int):Fp)=0) :
    ∀e∈compactRows,((ev C D fst lst trn P e : Int):Fp)=0 := by
  intro e he
  simp only [compactRows,List.mem_append] at he
  rcases he with (he|he)|he
  · exact hh e (List.mem_of_mem_take he)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply cast0 <;> simp [ev,Dsl.c,hv,hw]
  · exact hh e (List.mem_of_mem_drop he)

theorem compactRows_w3 {I : UpsInst} {C D P : Nat→Int} {st ix fl wi u : Nat}
    (hC : ∀x,x<200 → C x=WC I 3 x)
    (hD : ∀x,x<200 → D x=QC I (part I 0) 0 0 st ix fl wi u x) :
    ∀e∈compactRows,((ev C D 0 0 1 P e : Int):Fp)=0 := by
  intro e he
  simp only [compactRows,List.mem_append] at he
  simp only [UpsV3.cRows,List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,
    List.mem_cons,List.not_mem_nil,or_false,or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC,hD] <;> cellsimp <;> rclose
end ZkFormal.NearV3.Render.UpsRelay
