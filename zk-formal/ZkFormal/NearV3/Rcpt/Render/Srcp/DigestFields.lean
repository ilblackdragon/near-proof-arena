import ZkFormal.NearV3.Rcpt.Render.Srcp.LookupGate

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

def digestIndices : List Nat := [59, 60, 61, 62, 63, 64]

theorem item_predecessor {bs : List SrcpB} (h : SrcpWf bs) (B : SrcpB) (hB : B ∈ bs)
    (i : Nat) (hi : i < B.path.length) :
    (B.path.getD i default).pq + 1 = (B.path.getD i default).q := by
  have hh := h.items B hB i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Digest addresses and lengths match the root, leaf and predecessor loads. -/
theorem digest_polynomials (B : SrcpB) (z : Nat) (k : Kind) (g : Bool)
    (hk : k ∈ kinds B)
    (hq : ∀ i, i < B.path.length →
      (B.path.getD i default).pq + 1 = (B.path.getD i default).q)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ digestIndices) :
    ev (fun x => (({ frame B z k with gz := g }).cell x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hk' := (mem_kinds B k).mp hk
  cases k with
  | root =>
    simp only [digestIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn | hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c, Dsl.not,
      Dsl.mid, Dsl.smul, Dsl.k, msgId, frame, rootFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.cId, SrcpV3.cLen, SrcpV3.qe, SrcpV3.le, SrcpV3.wf,
      SrcpV3.lf, SrcpV3.aw, SrcpV3.j, SrcpV3.L, SrcpV3.q, SrcpV3.pl]
    all_goals omega
  | leaf p =>
    by_cases hp : p = 0
    all_goals simp only [digestIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    all_goals rcases hn with hn | hn | hn | hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c, Dsl.not,
      Dsl.mid, Dsl.smul, Dsl.k, msgId, frame, leafFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.cId, SrcpV3.cLen, SrcpV3.qe, SrcpV3.le, SrcpV3.wf,
      SrcpV3.lf, SrcpV3.aw, SrcpV3.j, SrcpV3.L, SrcpV3.q, SrcpV3.pl, hp]
    all_goals omega
  | path i o =>
    have hi : i < B.path.length := (show i < B.path.length ∧ o < 64 by simpa using hk').1
    have hqi := hq i hi
    simp only [List.getD_eq_getElem?_getD] at hqi
    cases hd : (B.path.getD i default).dir <;> by_cases hw : 32 ≤ o <;>
      by_cases hf : o % 32 = 0
    all_goals simp only [List.getD_eq_getElem?_getD] at hd
    all_goals simp only [digestIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    all_goals rcases hn with hn | hn | hn | hn | hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c, Dsl.not,
      Dsl.mid, Dsl.smul, Dsl.k, msgId, frame, pathFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.cId, SrcpV3.cLen, SrcpV3.qe, SrcpV3.le, SrcpV3.wf,
      SrcpV3.lf, SrcpV3.aw, SrcpV3.j, SrcpV3.L, SrcpV3.q, SrcpV3.pl, hd, hw, hf]
    all_goals omega

end ZkFormal.NearV3.Render.SrcpGen
