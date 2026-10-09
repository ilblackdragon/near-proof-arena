import ZkFormal.NearV3.Qv.Extract.ImplicitReadSequence

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- Compose actual queue constraints, both complete lookup bus balances,
authenticated trie/root views and parser evidence into native queue reads.
Global table isolation and physical parser extraction supply the displayed
premises; this theorem does not assume the native read conclusions. -/
theorem assemble_native_queue_reads {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (vs : List NodeS3) (es : List ValE) (hs : List HeadE) (ws : List WalkR)
    {us : List UpsE} {K : Nat} {r0 rK : List Nat}
    (C : RootChain hs us K r0 rK)
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hs ws)
    (hv : ValWf es) (ls : RcptV3Vs) (hn : (flatR ls).length≤W_AK)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hj : 1<q.segs.length) (hc : cv tr tt (q.segs[1]'hj).1 Candidates.ValueTable.count=ss.length)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false), m∈Parser.nativeShardMessages htau ss)
    (others : List (List Fp))
    (hkey : ((List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) ++
      (rcptSends3 pub ls B_KEYNIB).map Msg.toFp).Perm ((walkRecvs3 ws B_KEYNIB).map Msg.toFp))
    (hfinal : ((walkSends3 ws B_FINAL).map Msg.toFp).Perm
      ((List.range (tr.height tt)).flatMap
        (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false) ++ others))
    (he : ∀ j∈[0,2], cv tr tt (q.segs.getD j (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD j (0,0)).1 Candidates.ValueTable.vid ∧
        EmptyQueue (some (toBytes e.bytes)))
    (hb : cv tr tt (q.segs.getD 1 (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD 1 (0,0)).1 Candidates.ValueTable.vid ∧
        BufferedValue (some (toBytes e.bytes)) ss)
    (ha : cv tr tt (q.segs.getD 1 (0,0)).1 absent≠0 → ss=[]) :
    (queueMainValues vs es tr tt q ss).Valid ∧
    (queueMainValues vs es tr tt q ss).Reads
      (queueTree vs es hs 0) (queueTree vs es hs 0) (queueTree vs es hs 0) ∧
    (∀ t, 1≤t → t≤(kPublic.eval tr tt 0 pub).toNat →
      (missingRequest (queueTree vs es hs t)).Holds (queueTree vs es hs t)) := by
  have hL := Candidates.KeyTrafficRepair.local_to_base h
  have hread : ∀ i (hi : i<q.segs.length),
      (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau)).find
        (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
        some (queueValue vs es tr tt (q.segs[i]'hi).1) := by
    intro i hi
    obtain ⟨w,hw,hk,hf⟩ := balanced_queue_lookup h q i hi ls hn hK G.walk others hkey hfinal
    exact queue_root_read hL q i hi C G hw hk hf
  exact ⟨main_queue_valid vs hv tr tt q ss he hb ha,
    main_queue_reads hL q vs es hs ss htau hlen hj hc hrequests hread,
    implicit_queue_reads hL q vs es hs hread⟩

end ZkFormal.NearV3.Qv.Extract
