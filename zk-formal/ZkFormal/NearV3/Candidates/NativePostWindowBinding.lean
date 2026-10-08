import ZkFormal.NearV3.Candidates.NativeBoundPost
import ZkFormal.NearV3.Candidates.NodeUseTraffic

namespace ZkFormal.NearV3.Candidates.NativePostWindowBinding
open NearSpec NearSpecV3 ZkFormal.Near Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Whole-forest payload equality binds every indexed provider to the actual
post tree at the same global occurrence index. -/
theorem serialization_at {ns : List NodeS3} {ts : List PTrie}
    (h : ns.map (fun s=>s.v.ser true)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat))
    {n : Nat} {s : NodeS3} {t : PTrie}
    (hs : ns[n]?=some s) (ht : ts[n]?=some t) :
    s.v.ser true=(nodeEnc t).map UInt8.toNat := by
  have he:=congrArg (fun xs=>xs[n]?) h
  simpa only [List.getElem?_map,hs,ht,Option.map_some,Option.some.injEq] using he

/-- A window key uses the exact native post byte, retaining the same global
provider id, pre-serialization length, depth and child occurrence id. -/
theorem window_at {ns : List NodeS3} {ts : List PTrie}
    (h : ns.map (fun s=>s.v.ser true)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat))
    {n : Nat} {s : NodeS3} {t : PTrie}
    (hs : ns[n]?=some s) (ht : ts[n]?=some t) (p : Nat) :
    windowKey n p s=[msgId K_NPOST n,p,((nodeEnc t).map UInt8.toNat).getD p 0,
      (s.v.ser false).length,s.depth,s.ucid.getD p 0] := by
  unfold windowKey
  rw [serialization_at h hs ht]

/-- Native payload selected by global occurrence index. -/
def nativeWindowKey (ts : List PTrie) (n p : Nat) (s : NodeS3) : ZkFormal.Near.Msg :=
  [msgId K_NPOST n,p,((ts.map (fun t=>(nodeEnc t).map UInt8.toNat)).getD n []).getD p 0,
    (s.v.ser false).length,s.depth,s.ucid.getD p 0]

theorem native_key_at {ns : List NodeS3} {ts : List PTrie}
    (h : ns.map (fun s=>s.v.ser true)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat))
    {n : Nat} {s : NodeS3} (hs : ns[n]?=some s) (p : Nat) :
    windowKey n p s=nativeWindowKey ts n p s := by
  simp only [windowKey,nativeWindowKey,← h,List.getD_eq_getElem?_getD,
    List.getElem?_map,hs,Option.map_some,Option.getD_some]

private theorem flat_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

/-- The physical UPB provider count uses exact native post bytes, with full
request multiplicities and the original renderer's metadata columns. -/
theorem physical_windows (q : UseRequests) (ns : List NodeS3) (ts : List PTrie)
    (hn : NodeOk ns)
    (h : ns.map (fun s=>s.v.ser true)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat))
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P)
    (hu : q.windows.length<Algebra.P) (clock : Nat) (pub : List Algebra.Fp)
    (msg : List Algebra.Fp) :
    Air.tableBusCount SizeCount.nodeTable.interactions
      (TrieCountHeight.node (assignList q 0 ns) pub) clock pub B_UPB false msg=
    (((ns.zip (List.range ns.length)).flatMap fun (s,n)=>
      (List.range (s.v.ser false).length).map fun p=>
        nativeWindowKey ts n p s++[q.windows.count (nativeWindowKey ts n p s)]).map Msg.toFp).count msg := by
  rw [NodeUseTraffic.windows q ns hn he hb hu clock pub msg]
  congr 2
  apply flat_congr
  intro pair hp
  have hs : ns[pair.2]?=some pair.1 := by
    apply List.mem_zipIdx_iff_getElem?.mp
    simpa only [List.zipIdx_eq_zip_range',← List.range_eq_range'] using hp
  apply List.map_congr_left
  intro p _
  rw [native_key_at h hs p]

theorem assign_idempotent (q : UseRequests) (ns : List NodeS3) (n : Nat) :
    assignList q n (assignList q n ns)=assignList q n ns := by
  induction ns generalizing n with
  | nil => rfl
  | cons s ss ih =>
    simp only [assignList,ih]
    rfl

end ZkFormal.NearV3.Candidates.NativePostWindowBinding
