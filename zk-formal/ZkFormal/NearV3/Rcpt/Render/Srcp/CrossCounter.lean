import ZkFormal.NearV3.Rcpt.Render.Srcp.CounterEnd

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

theorem cross_q {bs : List SrcpB} (h : SrcpWf bs) (i z : Nat) (hi : i + 1 < bs.length) :
    (rootFrame (bs.getD (i + 1) default) z).q = (bs.getD i default).lastQ := by
  have hp : i < bs.length := by omega
  simp only [rootFrame, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hp, Option.getD_some]
  rw [h.qnext i hi]
  omega

theorem cross_j {bs : List SrcpB} (h : SrcpWf bs) (i : Nat) (hi : i + 1 < bs.length) :
    (bs.getD (i + 1) default).j = (bs.getD i default).j + 1 := by
  have hp : i < bs.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hp, h.j i hp, h.j (i + 1) hi]

set_option maxRecDepth 4096 in
theorem counter_padding (C D P : Nat → Int) (fst lst trn : Int)
    (hRt : C SrcpV3.rt = 0) (hSl : C SrcpV3.sl = 0)
    (n : Nat) (hi : n ∈ counterIndices) :
    ev C D fst lst trn P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  simp only [counterIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi
  all_goals subst n
  all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n,
    Dsl.k, hRt, hSl]

end ZkFormal.NearV3.Render.SrcpGen
