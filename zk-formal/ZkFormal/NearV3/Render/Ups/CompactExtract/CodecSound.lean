import ZkFormal.NearV3.Render.Ups.CompactExtract.PreparedLink
import ZkFormal.NearV3.Render.Ups.CodecRelayBalance
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
/-- Compact UPS semantic soundness with its fresh scheduler value derived from
the actual candidate Codec table. Public SPAR and global SPLEN balance establish
identity and length; the actual per-table BYTES decomposition supplies SHA.
Residual global BYTES ownership remains explicit. -/
theorem codec_prepared_link {AP : ZkFormal.V2.AirP} {tr : Trace Fp} {pub : List Fp} {tc tu : Nat} {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} 
    {othersU : List Msg} {ws : List WalkR} {prov : List Msg} {r0 rK : List Nat}
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep : NearSpecV3.prepD0 cb hint = .ok p)
    (hH : ZkFormal.V2.HoldsP AP pub tr) (O : CodecLengthOwn AP tc)
    (hu : tu<AP.tables.length)
    (hTraffic : TableTraffic AP.tables[tu]!.interactions tr tu pub (upsTraffic v))
    (SO : Sched.SparOwn AP) (I : ZkFormal.V2.PubIdx AP pub Fp.ofNat) {fwd : List (Nat×Nat)}
    (hpub : I.recs Sched.B_SPAR true=(Sched.render (p.sched.map Sched.instOf) fwd).par)
    -- views
    (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hw : Wf v) (hW : WalkWf3 ws)
    (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21)
    -- balances
    (hb : Link3.ParentBal vs hds) (hvb : Link3.VParentBal vs es) (hupb : UpbBal vs v)
    (hE : WalkBal vs hds ws v B_EDGE) (hB : WalkBal vs hds ws v B_BMAP) (hKn : Link3.KeynibOk ws prov)
    (hbytes : ∀m,shaR B_BYTES m =
      tableBusCount codecTable.interactions tr tc pub B_BYTES true m +
      tableBusCount AP.tables[tu]!.interactions tr tu pub B_BYTES true m + cnt othersU m)
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
    :
    ∀ τ, τ ≤ p.hdr.K →
      (∃ Q, (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).upsert UpsSpec.key ((relaySchedValue tr tc) τ) = some Q ∧
        (upsAt (v.map upsE) τ).post = Q.hashOf.map UInt8.toNat ∧ Link3.toB (upsAt (v.map upsE) τ).post = Q.hashOf ∧
        (τ < p.hdr.K → (headAt hds (τ + 1)).pre = Q.hashOf.map UInt8.toNat) ∧ (τ = p.hdr.K → rK = Q.hashOf.map UInt8.toNat)) ∧
      (∃ s ∈ v, s.row 0 tau = τ ∧ s.msgs B_S0F true = [[τ, s.row 0 pres, s.row 0 vid]] ∧
        ((s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key =
            some (some (valOf (Vpost vs es pv) (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
         (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
            (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key = some none))) := by
  have hn : (p.sched.map Sched.instOf).length≤32 := by
    simp only [List.length_map]
    have hc:=Assembly.prepD0_sched_count hprep
    have hk:=prepD0_K_lt32 hprep
    omega
  have hl : Sched.Codec.CLocal tr tc pub := by
    have h:=Chacha.local_of_holdsP hH O.lt
    rw [O.tab] at h
    exact h
  have hh : tr.height tc≤2^22 := Sched.height_le hH O.lt O.tab rfl
  have hs:=codecRelay_spar_supply hH O.lt O.tab SO I hpub
  obtain ⟨hbytes,hother⟩:=codecRelay_global_bytes hl hh hs hn hTraffic hbytes hothU
  have hlenSV:=codecRelay_schedLength_of_holds hH O hu hTraffic SO I hpub (by omega)
  have hk:=prepD0_K_lt32 hprep
  exact upsV3_linkB hN hhw hvw hw hW hWr hb hvb hupb hE hB hKn
    (relayTaus_bound hl hh hs hn) hbytes hother hdigU hmemd
    (by have := P_gt;omega) hk hr0 hrK hROOT hMID hlen hsha hvpost hvpostLen hlenSV
end ZkFormal.NearV3.Render.UpsRelay.Extract
