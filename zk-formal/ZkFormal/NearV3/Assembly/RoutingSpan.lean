import ZkFormal.NearV3.Assembly.RoutingFrameTransport

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- One coherent receiver-byte/end-marker span. Remaining rows only supply the
post-span prefix cells; they are not claimed to be complete receipt padding. -/
def routeSpan (acct : Bytes) (iv : Option Bytes×Option Bytes) (log : Nat) : Trace Fp :=
  ⟨fun _=>log,fun _ pos c=>if pos≤acct.length then frameCell (frameOf acct iv pos) c
    else frameNext (frameOf acct iv acct.length) c⟩

theorem routeSpan_current (acct : Bytes) (iv : Option Bytes×Option Bytes) (log pos : Nat)
    (hpos : pos≤acct.length) :
    ∀c,(routeSpan acct iv log).cell 0 pos c=frameCell (frameOf acct iv pos) c := by
  intro c
  exact if_pos hpos

theorem routeSpan_next (acct : Bytes) (iv : Option Bytes×Option Bytes) (log pos : Nat)
    (hheight : acct.length+1<2^log) (hpos : pos≤acct.length) :
    ∀c,c=eqL ∨ c=eqH →
      (routeSpan acct iv log).cell 0 ((pos+1)%(routeSpan acct iv log).height 0) c=
        frameNext (frameOf acct iv pos) c := by
  intro c hc
  have hmod : (pos+1)%(routeSpan acct iv log).height 0=pos+1 := by
    apply Nat.mod_eq_of_lt
    change pos+1<2^log
    omega
  rw [hmod]
  by_cases hp : pos+1≤acct.length
  · rw [routeSpan_current acct iv log (pos+1) hp]
    rcases hc with rfl|rfl
    · exact frame_prefix_lower acct iv pos
    · exact frame_prefix_upper acct iv pos
  · have he : pos=acct.length := by omega
    subst pos
    exact if_neg (by omega)

theorem routeSpan_constraints (acct : Bytes) (iv : Option Bytes×Option Bytes) (log : Nat)
    (hheight : acct.length+1<2^log) (hv : inInterval acct iv=true)
    (hu : ∀b∈iv.2.getD [],0<b.toNat) (pub : List Fp) :
    ∀pos,pos≤acct.length → ∀e∈cRoute,e.eval (routeSpan acct iv log) 0 pos pub=0 := by
  intro pos hp
  exact frame_route_transport _ _ _ pub _ (frameOf_ordered _ _ _ hp hv hu)
    (routeSpan_current acct iv log pos hp) (routeSpan_next acct iv log pos hheight hp)

/-- Native accepted receipt bytes need at most 66 rows including the continuation
prefix row, so a log-7 span suffices with no extra receipt-size premise. -/
theorem applied_receipt_route_span {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeStateWitness bs=.ok w) {r : Receipt} (hr : r∈appliedReceipts k w)
    (pub : List Fp) :
    ∃q,selectInterval k.L k.H.shardId r.receiverId=some q ∧ q<128 ∧
      ∀pos,pos≤r.receiverId.length →
        routeKey (boundedPrep p k.L k.H.shardId).bnds q pos∈
          Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
        ∀e∈cRoute,e.eval (routeSpan r.receiverId
          ((boundedIntervals k.L k.H.shardId).getD q (none,none)) 7) 0 pos pub=0 := by
  obtain ⟨q,hq,hlt,hiv,hkeys⟩ := applied_receipt_selection hp hk hw hr
  have hwf := appliedReceipts_wf hw r hr
  have hlen : r.receiverId.length≤64 := by
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hwf
    grind only
  refine ⟨q,hq,hlt,?_⟩
  intro pos hpos
  refine ⟨hkeys pos hpos,?_⟩
  exact routeSpan_constraints _ _ 7 (by omega) hiv
    (normalized_endpoint_positive hk (selectInterval_valid _ _ _ hq).1) pub pos hpos

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
