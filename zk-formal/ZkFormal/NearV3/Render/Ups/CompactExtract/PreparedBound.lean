import ZkFormal.NearV3.Assembly.PrepFacts
import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsChain
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec NearSpecV3 Sched Assembly
private theorem index_bound {c : Claim} {blks : List Blk} {i : Nat} {b : Blk}
    (hc : check (decide (c.blocks.length ≤ 32)) "out of domain (c.segment)" = .ok ())
    (hm : c.blocks.mapM decodeBlk = .ok blks) (hi : blks[i]? = some b) :
    ((blks.take i).reverse).length < 32 := by
  have hb : c.blocks.length ≤ 32 := of_decide_eq_true (check_ok hc)
  have hl := mapM_length decodeBlk c.blocks blks hm
  have hx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [List.length_reverse,List.length_take]
  omega
set_option maxHeartbeats 4000000 in
 theorem prepClaim_K_lt32 {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    pc.hdr.K < 32 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact index_bound (by assumption) (by assumption) (by assumption)
 theorem prepD0_K_lt32 {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepD0 cb hint = .ok p) : p.hdr.K < 32 := by
  unfold prepD0 at h
  obtain ⟨pc,hc,hb⟩:=bind_ok h
  rw [(prepBody_shape hb).1]
  exact prepClaim_K_lt32 hc
open ZkFormal.Near UpsV3 UpsRows in
 theorem prepared_tauBound {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) {hds : List HeadE} {v : List UpsSeg} {r0 rK : List Nat}
    (hc : RootChain hds (v.map upsE) p.hdr.K r0 rK) :
    ∀s∈v,s.row 0 tau<32 := by
  intro s hs
  have := ups_tauBound hc s hs
  have := prepD0_K_lt32 hp
  omega
 theorem prepared_relay_bound {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) : ∀t∈List.range (p.hdr.K+1),t<32 := by
  intro t ht
  have := List.mem_range.mp ht
  have := prepD0_K_lt32 hp
  omega
end ZkFormal.NearV3.Render.UpsRelay.Extract
