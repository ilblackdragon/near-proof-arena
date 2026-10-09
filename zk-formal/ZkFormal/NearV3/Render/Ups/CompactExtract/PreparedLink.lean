import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsLink
import ZkFormal.NearV3.Render.Ups.CompactExtract.PreparedBound
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
/-- Native preprocessing fixes the instance range, so the compact sound theorem
requires no separately assumed instance cap or relay-index cap. The remaining
hypotheses are authenticated views, bus balances and scheduler length binding. -/
theorem prepared_link {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
    {othersU : List Msg} {ws : List WalkR} {prov : List Msg} {r0 rK : List Nat}
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep : NearSpecV3.prepD0 cb hint = .ok p)
    -- views
    (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hw : Wf v) (hW : WalkWf3 ws)
    (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21)
    -- balances
    (hb : Link3.ParentBal vs hds) (hvb : Link3.VParentBal vs es) (hupb : UpbBal vs v)
    (hE : WalkBal vs hds ws v B_EDGE) (hB : WalkBal vs hds ws v B_BMAP) (hKn : Link3.KeynibOk ws prov)
    (hbytesU : ∀ m, shaR B_BYTES m = cnt ((List.range (p.hdr.K+1)).flatMap (fun t => relayValueMsgs t (sv t)) ++ (upsTraffic v).sends B_BYTES ++ othersU) m)
    (hothU : ∀ m ∈ othersU, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdigU : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (hmemd : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
    (hROOT : (([[0] ++ r0] ++ (upsTraffic v).sends B_ROOT).map Msg.toFp).Perm
      ((headRecvs hds B_ROOT ++ [[p.hdr.K + 1] ++ rK]).map Msg.toFp))
    (hMID : ((headSends hds B_MIDROOT).map Msg.toFp).Perm (((upsTraffic v).recvs B_MIDROOT).map Msg.toFp))
    (hlen : hds.length < P)
    -- SHA
    (hsha : Link3.ShaHyp vs hds es others shaS shaR)
    -- interfaces
    (hvpost : Link3.VPostOk others pv)
    (hvpostLen : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    (hsched : SchedLength v sv) :
    ∀ τ, τ ≤ p.hdr.K →
      (∃ Q, (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).upsert UpsSpec.key (sv τ) = some Q ∧
        (upsAt (v.map upsE) τ).post = Q.hashOf.map UInt8.toNat ∧ Link3.toB (upsAt (v.map upsE) τ).post = Q.hashOf ∧
        (τ < p.hdr.K → (headAt hds (τ + 1)).pre = Q.hashOf.map UInt8.toNat) ∧ (τ = p.hdr.K → rK = Q.hashOf.map UInt8.toNat)) ∧
      (∃ s ∈ v, s.row 0 tau = τ ∧ s.msgs B_S0F true = [[τ, s.row 0 pres, s.row 0 vid]] ∧
        ((s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key =
            some (some (valOf (Vpost vs es pv) (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
         (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
            (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key = some none))) := by
  have hk := prepD0_K_lt32 hprep
  exact upsV3_linkB hN hhw hvw hw hW hWr hb hvb hupb hE hB hKn
    (prepared_relay_bound hprep) hbytesU hothU hdigU hmemd
    (by have := P_gt; omega) hk hr0 hrK hROOT hMID hlen hsha hvpost hvpostLen hsched
end ZkFormal.NearV3.Render.UpsRelay.Extract
