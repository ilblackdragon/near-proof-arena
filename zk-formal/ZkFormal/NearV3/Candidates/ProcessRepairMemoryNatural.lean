import ZkFormal.NearV3.Candidates.ProcessRepairReceiptIndexed
import ZkFormal.NearV3.Candidates.ProcessRepairAccountUnique
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptCanon
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryNatural
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Link RcptV3Proof

theorem canon {pub:List Fp} {rs:RcptVs} {as:List AcctV}
    (hlen:rs.length≤2^22) (hs:∀x∈rs,x.kslot<P ∧ x.tprev<P)
    (hc:∀x∈rs,∀b∈x.raw,b<P) (ha:as=[] ∨ AcctWf as):
    (∀m∈memW pub rs as,Canon m) ∧ (∀m∈memR pub rs as,Canon m):=by
  have hac:∀a∈as,AcctWf as:=by
    intro a ham
    rcases ha with rfl|ha
    · simp at ham
    · exact ha
  have hp:∀a∈as,∀b∈a.pre,b<P:=fun a ham b hb=>(hac a ham).canon a ham b (List.mem_append_left _ hb)
  have hpo:∀a∈as,∀b∈a.post,b<P:=fun a ham b hb=>(hac a ham).canon a ham b (List.mem_append_right _ hb)
  have hlane:∀a∈as,∀l:List Nat,(∀b∈l,b<P)→∀i,∀b∈acctLane a l i,b<P:=by
    intro a ham l hl i b hb
    simp only [acctLane,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl
    · exact getD_lt hl i
    · exact getD_lt (hp a ham) _
    · split
      · exact getD_lt (hp a ham) _
      · decide
  constructor
  · intro m hm
    rcases mem_memW.mp hm with ⟨r,hr,i,hi,rfl⟩|⟨a,ham,i,hi,rfl⟩
    · intro b hb
      simp only [wrMsg,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl
      · exact (hs _ (List.getElem_mem hr)).1
      · unfold P;omega
      · unfold P;omega
      all_goals exact getD_lt (fun b hb=>hc _ (List.getElem_mem hr) b (by simp [RcptV.raw,hb])) i
    · intro b hb
      simp only [awMsg,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with (rfl|rfl|rfl)|hb
      · exact ((hac a ham).len a ham).2.2.1
      · decide
      · unfold P;omega
      · exact hlane a ham _ (hp a ham) i b hb
  · intro m hm
    rcases mem_memR hm with ⟨r,hr,i,hi,rfl⟩|⟨a,ham,i,hi,rfl⟩
    · intro b hb
      simp only [rdMsg,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl
      · exact (hs _ (List.getElem_mem hr)).1
      · exact (hs _ (List.getElem_mem hr)).2
      · unfold P;omega
      all_goals exact getD_lt (fun b hb=>hc _ (List.getElem_mem hr) b (by simp [RcptV.raw,hb])) i
    · intro b hb
      simp only [arMsg,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with (rfl|rfl|rfl)|hb
      · exact ((hac a ham).len a ham).2.2.1
      · exact ((hac a ham).len a ham).2.2.2
      · unfold P;omega
      · exact hlane a ham _ (hpo a ham) i b hb

theorem permutation {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {as:List AcctV} (hwa:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    let rs:=(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV
    (memW pub rs as).Perm (memR pub rs as):=by
  let rs:=(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV
  have hfield:=ProcessRepairReceiptMemProvider.permutation view hpub ha hc
  rw [ProcessRepairReceiptIndexed.sends,ProcessRepairReceiptIndexed.receives] at hfield
  have hameq:acctV3Sends as B_MEM=acctSends as B_MEM:=by simp [acctV3Sends,acctSends];rfl
  rw [hameq] at hfield
  have hlen:rs.length≤2^22:=by simpa only [rs,List.length_map] using ProcessRepairReceiptWf.count_bound view hc
  obtain ⟨toks,_,_,hws,_⟩:=ProcessRepairReceiptWf.tokens view hpub hc
  have hsmall:∀x∈rs,x.kslot<P ∧ x.tprev<P:=by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
    obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hy
    exact ⟨(hws r hr).small.1,(hws r hr).small.2.1⟩
  have hraw:∀x∈rs,∀b∈x.raw,b<P:=by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
    obtain ⟨L,hL,hy⟩:=List.mem_flatMap.mp hy
    obtain ⟨B,hB,rfl⟩:=List.mem_map.mp hL
    change y∈B.receipts.map (rcptOf (ProcPriorRoutedReceiptView.receipt tr) 0) at hy
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hy
    exact Assembly.ReceiptCandidateProof.raw_canon_of
      (Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view))
      ((hc.blocks B hB).layouts z hz)
  have haw:as=[] ∨ AcctWf as:=hwa.imp id (·.v1)
  obtain ⟨hW,hR⟩:=canon hlen hsmall hraw haw
  exact perm_nat hW hR hfield
end ZkFormal.NearV3.Candidates.ProcessRepairMemoryNatural
