import ZkFormal.NearV3.Candidates.ProcPriorRoutedRootChain
import ZkFormal.NearV3.Render.Ups.CompactExtract.ByteOwnership
import ZkFormal.NearV3.Render.Ups.CompactExtract.Plan
namespace ZkFormal.NearV3.Candidates.ProcPriorCompactUpsByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.UpsV3 ZkFormal.NearV3.UpsRows
open ZkFormal.NearV3.Render.UpsRelay.Extract

/-- Tag separation needs only the actual physical part-count bound, not the
stronger allocation premise that each instance has fewer than512 parts. -/
theorem byte_tag {v:List UpsSeg} (hw:Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map upsE) K r0 rK) (hK:K<33) :
    ∀m∈(upsTraffic v).sends B_BYTES,∃a,m.head?=some a ∧ a<P ∧ a%16=12 := by
  intro m hm
  obtain ⟨s,hs,i,hi,hm⟩:=mem_upsSends.mp hm
  obtain ⟨ps,fls,ws,hL⟩:=ups_layout hw s hs
  have ht:s.row 0 tau<33:=by have:=Render.UpsRelay.Extract.ups_tauBound hchain s hs;omega
  have hparts:=psLe hw hs hL
  have hrows:=lenLe hw hs
  rcases Nat.lt_or_ge i 4 with h4|h4
  · rw [hL.msgsW i h4 B_BYTES true] at hm
    simp [B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_EDGE,B_BMAP] at hm
  · rw [hL.msgsQ i h4 hi B_BYTES true] at hm
    simp only [B_BYTES,B_DIGEST,B_UPB,B_MEMD] at hm
    simp at hm
    subst m
    obtain ⟨k,hk,hlo,hhi⟩:=consec_find ps 4 hL.consec i h4 (by rw [hL.cover];exact hi)
    have hj:s.row i j=k+1:=by
      have hc:=((hL.part k hk).2.rows (i-ps[k].1) (by omega)).2.2.2.2 j (by decide)
      rw [show ps[k].1+(i-ps[k].1)=i by omega] at hc
      exact hc.trans (hL.part k hk).1
    have hsmall:12+16*(512*s.row 0 tau+(k+1))<P:=by unfold P;omega
    refine ⟨12+16*(512*s.row 0 tau+(k+1)),?_,hsmall,by omega⟩
    simp only [List.head?_cons,Option.some.injEq]
    rw [hL.segc i hi tau (by decide),hj]
    change (12+16*(512*s.row 0 tau+(k+1)))%P=_
    exact Nat.mod_eq_of_lt hsmall
theorem source_tag {tr:Trace Fp} {pub:List Fp} {v:List UpsSeg}
    (hw:Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map upsE) K r0 rK) (hK:K<33)
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v))
    {r:Nat} (hr:r<tr.height 0) {i:Interaction} (hi:i∈Render.UpsRelay.compactInteractions)
    (hb:i.bus=B_BYTES) (hsend:i.send=true)
    (hm:i.multNat (ProcPriorRoutedUpsView.ups tr) 0 r pub≠0) :
    (i.msgVal (ProcPriorRoutedUpsView.ups tr) 0 r pub)[0]!.toNat%16=12 := by
  have hr':r<(ProcPriorRoutedUpsView.ups tr).height 0:=hr
  have hp:=ZkFormal.Chacha.tableBusCount_pos hr' hi hm
  rw [hb,hsend,(hU _ _).1] at hp
  obtain ⟨m,hm,he⟩:=List.mem_map.mp (List.count_pos_iff.mp (Nat.pos_of_ne_zero hp))
  obtain ⟨a,ha,haP,htag⟩:=byte_tag hw hchain hK m hm
  cases m with
  | nil=>simp at ha
  | cons x xs=>
    simp only [List.head?_cons,Option.some.injEq] at ha
    subst x
    rw [←he]
    change (Fp.ofNat a).toNat%16=12
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt haP]
    exact htag
end ZkFormal.NearV3.Candidates.ProcPriorCompactUpsByteTag
