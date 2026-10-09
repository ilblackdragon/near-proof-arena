import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowBalance
import ZkFormal.NearV3.Candidates.NodeUseTraffic

namespace ZkFormal.NearV3.Candidates.PhysicalWindowRequests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

def keys (tr : Trace Fp) (t : Nat) : List Msg :=
  (physicalWindowRows tr t).map (physicalWindowKey tr t)

/-- The provider counter input is the complete physical read multiset, retaining
repeated keys in their actual row order. -/
theorem count (tr : Trace Fp) (t : Nat) (key : Msg) :
    (keys tr t).count key=physicalWindowUsers tr t key := by
  unfold keys physicalWindowRows physicalWindowUsers selectedWindow
  generalize List.range (tr.height t)=rs
  induction rs with
  | nil => simp
  | cons r rs ih =>
    by_cases hd : tr.cell t r UpsV3.rd=1 <;>
      by_cases hk : physicalWindowKey tr t r=key <;> simp [hd,hk,ih]

theorem length (tr : Trace Fp) (t : Nat) : (keys tr t).length≤tr.height t := by
  simpa [keys,physicalWindowRows] using
    List.length_filter_le (fun r=>decide (tr.cell t r UpsV3.rd=1)) (List.range (tr.height t))

theorem field_bound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal Render.UpsRelay.compactTable tr t pub) : (keys tr t).length<P := by
  have hh:=length tr t
  have hl : tr.log t≤22:=h.log_le
  have hp:=Nat.pow_le_pow_right (n:=2) (by decide) hl
  change 2^tr.log t≤2^22 at hp
  change (keys tr t).length≤2^tr.log t at hh
  unfold P;omega

/-- Native node providers receive exactly the terminal counters counted from
actual compact read rows. No abstract counter assignment remains here. -/
theorem providers (tr : Trace Fp) (tu : Nat) (pub : List Fp)
    (hl : TableLocal Render.UpsRelay.compactTable tr tu pub)
    (q : UseRequests) (vs : List NodeS3) (hn : Render.NodeOk vs)
    (he : q.edges.length<P) (hb : q.bmaps.length<P)
    (hq : q.windows=keys tr tu) (tn : Nat) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions
      (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_UPB false msg=
    (((vs.zip (List.range vs.length)).flatMap fun (s,n)=>
      (List.range (s.v.ser false).length).map fun p=>
        windowKey n p s++[physicalWindowUsers tr tu (windowKey n p s)]).map Msg.toFp).count msg := by
  have hu : q.windows.length<P := by rw [hq];exact field_bound hl
  rw [NodeUseTraffic.windows q vs hn he hb hu tn pub msg]
  simp only [hq,count]

end ZkFormal.NearV3.Candidates.PhysicalWindowRequests
