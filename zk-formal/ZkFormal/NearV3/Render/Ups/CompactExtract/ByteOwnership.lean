import ZkFormal.NearV3.Render.Ups.CompactExtract.LayoutMain
import ZkFormal.NearV3.Render.Ups.RelayFreshTraffic
import ZkFormal.NearV3.Extract.Ups.UpsBus
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec Assembly ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows UpsGen

/-- The unchanged instance/job domain needed to prevent SHA identifier aliases.
This is an explicit global allocation obligation, not a byte or hash assumption. -/
def CompactIdBound (v : List UpsSeg) : Prop :=
  ∀s∈v, s.row 0 tau<32 ∧ ∀ps fls ws,UpsLayout s ps fls ws → ps.length<512

/-- Every compact BYTES send belongs to a positive-index node job, on any
satisfying extracted view. This does not assume an honest native upsert witness. -/
theorem byte_ownership {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v) :
    ∀m∈(upsTraffic v).sends B_BYTES, ∃tau j,
      tau<32 ∧ 1≤j ∧ j<512 ∧ m.head?=some (upsertJobId tau j) := by
  intro m hm
  obtain ⟨s,hs,i,hi,hm⟩:=mem_upsSends.mp hm
  obtain ⟨ps,fls,ws,hL⟩:=ups_layout hw s hs
  obtain ⟨ht,hparts⟩:=hb s hs
  have hps:=hparts ps fls ws hL
  rcases Nat.lt_or_ge i 4 with h4|h4
  · rw [hL.msgsW i h4 B_BYTES true] at hm
    simp [B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_EDGE,B_BMAP] at hm
  · rw [hL.msgsQ i h4 hi B_BYTES true] at hm
    simp only [B_BYTES,B_DIGEST,B_UPB,B_MEMD] at hm
    simp at hm
    subst m
    obtain ⟨k,hk,hlo,hhi⟩:=consec_find ps 4 hL.consec i h4 (by rw [hL.cover]; exact hi)
    have hj : s.row i j=k+1 := by
      have hc:=((hL.part k hk).2.rows (i-ps[k].1) (by omega)).2.2.2.2 j (by decide)
      rw [show ps[k].1+(i-ps[k].1)=i by omega] at hc
      exact hc.trans (hL.part k hk).1
    refine ⟨s.row 0 tau,k+1,ht,by omega,by omega,?_⟩
    simp only [List.head?_cons,Option.some.injEq]
    rw [hL.segc i hi tau (by decide),hj,upsIdN_val (by omega) (by omega)]
    rfl
end ZkFormal.NearV3.Render.UpsRelay.Extract
