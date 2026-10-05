import ZkFormal.Near.Link.Receipts
import ZkFormal.Near.Link.Mem

/-!
# ZkFormal.Near.Link.Digests — the consumed digests, by consumer

`sha_ok` applied to each digest the NEAR tables consume: touched values
(`VPRE/VPOST`), `PEO`, `RID`, `RF`.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-- The touched-value windows of a node segment. -/
def _root_.ZkFormal.Near.NodeV.vwin : NodeV → Option (List Nat × List Nat)
  | .leaf _ (.touched pre po) _ => some (pre, po)
  | .branch (some (.touched pre po)) _ _ => some (pre, po)
  | _ => none

theorem vwin_of_touched {v : NodeV} (h : v.touched = true) : ∃ pre po, v.vwin = some (pre, po) := by
  match v, h with
  | .leaf _ (.touched pre po) _, _ => exact ⟨pre, po, rfl⟩
  | .branch (some (.touched pre po)) _ _, _ => exact ⟨pre, po, rfl⟩

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem vwin_recv {n : Nat} (hn : n < vs.length) {pre po : List Nat}
    (hw : vs[n].v.vwin = some (pre, po)) :
    digMsg (msgId K_VPRE n) 72 pre ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST ∧
    digMsg (msgId K_VPOST n) 72 po ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
  have key : ∀ m, m ∈ (match vs[n].v with
       | .leaf _ (.touched pre po) _ | .branch (some (.touched pre po)) _ _ =>
         [digMsg (msgId K_VPRE n) 72 pre, digMsg (msgId K_VPOST n) 72 po]
       | _ => []) → m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    intro m hm
    rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_left
    unfold nodeRecvs; dsimp only; rw [if_pos rfl]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨(vs[n], n), mem_zip_range.mpr ⟨hn, rfl⟩, List.mem_append_right _ hm⟩
  rcases hv : vs[n].v with ⟨k, sl, mb⟩ | ⟨k, kid, mb⟩ | ⟨sv, kids, mb⟩
  · cases sl with
    | ref => rw [hv] at hw; simp [NodeV.vwin] at hw
    | touched pre' po' =>
      rw [hv] at hw; simp only [NodeV.vwin, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rw [hv] at key; exact ⟨key _ (by simp), key _ (by simp)⟩
  · rw [hv] at hw; simp [NodeV.vwin] at hw
  · rcases sv with _ | sl
    · rw [hv] at hw; simp [NodeV.vwin] at hw
    · cases sl with
      | ref => rw [hv] at hw; simp [NodeV.vwin] at hw
      | touched pre' po' =>
        rw [hv] at hw; simp only [NodeV.vwin, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        rw [hv] at key; exact ⟨key _ (by simp), key _ (by simp)⟩

/-- Touched values: the acct bytes are bytes and hash to the node's windows. -/
theorem acct_digests {a : AcctV} (ha : a ∈ as) :
    ∃ hk : a.k < vs.length, ∃ pre po, vs[a.k].v.vwin = some (pre, po) ∧
      Bytes8 a.pre ∧ pre = (sha256 (toBytes a.pre)).map UInt8.toNat ∧
      Bytes8 (a.post ++ a.pre.drop 16) ∧
      po = (sha256 (toBytes (a.post ++ a.pre.drop 16))).map UInt8.toNat := by
  obtain ⟨hnd, hslot, -⟩ := vslot h
  obtain ⟨hk, ht⟩ := hslot a ha
  obtain ⟨pre, po, hw⟩ := vwin_of_touched ht
  obtain ⟨h1, h2⟩ := vwin_recv h hk hw
  have hlt := vs_length_lt h.node
  have hl := h.acct.len a ha
  have e1 := encOf_vpre (publicOf c) vs rs as mv a.k
  have e2 := encOf_vpost (publicOf c) vs rs as mv a.k
  rw [acctOf_eq hnd ha] at e1 e2
  simp only [Option.map_some, Option.getD_some] at e1 e2
  obtain ⟨b1, d1⟩ := sha_ok c vs ws rs as mv ids shaS shaR h _ 72 pre
    (by unfold msgId K_VPRE; omega) (by rw [e1, hl.1]) h1
  obtain ⟨b2, d2⟩ := sha_ok c vs ws rs as mv ids shaS shaR h _ 72 po
    (by unfold msgId K_VPOST; omega) (by rw [e2]; simp [hl.1, hl.2.1]) h2
  rw [e1] at b1 d1; rw [e2] at b2 d2
  exact ⟨hk, pre, po, hw, b1, d1, b2, d2⟩

omit h in
theorem rcpt_mem_digest {r : Nat} (hr : r < rs.length) {m : Msg}
    (hm : m ∈ (if rs[r].hr then [digMsg (msgId K_RID r) 48 rs[r].rfid] else []) ++
      [digMsg (msgId K_PEO r) rs[r].peo.length rs[r].peoh]) :
    m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
  rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_right
  unfold rcptRecvs; dsimp only; rw [if_pos rfl]
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩, hm⟩

/-- `PEO(r)`: bytes, and `peoh = sha256 peo`. -/
theorem peo_digest {r : Nat} (hr : r < rs.length) :
    Bytes8 rs[r].peo ∧ rs[r].peoh = (sha256 (toBytes rs[r].peo)).map UInt8.toNat := by
  have hrl := rs_length_le h
  have e := encOf_peo (publicOf c) vs rs as mv r
  rw [List.getElem?_eq_getElem hr] at e; simp only [Option.map_some, Option.getD_some] at e
  have := sha_ok c vs ws rs as mv ids shaS shaR h (msgId K_PEO r) rs[r].peo.length rs[r].peoh
    (by unfold msgId K_PEO P; omega) (by rw [e])
    (rcpt_mem_digest (c := c) (vs := vs) (ws := ws) (as := as) (mv := mv) (ids := ids) hr (List.mem_append_right _ (List.mem_singleton_self _)))
  rwa [e] at this

/-- `RID(r)` (refund receipts): `rfid = sha256 (rid ‖ height ‖ 0)`. -/
theorem rid_digest {r : Nat} (hr : r < rs.length) (hhr : rs[r].hr = true) :
    Bytes8 (ridMsg (publicOf c) rs[r]) ∧
      rs[r].rfid = (sha256 (toBytes (ridMsg (publicOf c) rs[r]))).map UInt8.toNat := by
  have hrl := rs_length_le h
  obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
  have e := encOf_rid (publicOf c) vs rs as mv r
  rw [List.getElem?_eq_getElem hr] at e; simp only [Option.map_some, Option.getD_some] at e
  have := sha_ok c vs ws rs as mv ids shaS shaR h (msgId K_RID r) 48 rs[r].rfid
    (by unfold msgId K_RID P; omega) (by rw [e, ridMsg_length w])
    (rcpt_mem_digest (c := c) (vs := vs) (ws := ws) (as := as) (mv := mv) (ids := ids) hr (List.mem_append_left _ (by simp [hhr])))
  rwa [e] at this

/-- The `RF` digest. -/
theorem rf_digest : Bytes8 (rfMsg (publicOf c) rs) ∧
    c.1.refundsCommitment = sha256 (toBytes (rfMsg (publicOf c) rs)) := by
  have hmem : digMsg K_RF (rfOffs rs rs.length) (pubBytes (publicOf c) PV_RFC 32) ∈
      nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_right
    unfold rcptRecvs; dsimp only; rw [if_pos rfl]; simp
  have hlen : rfOffs rs rs.length = (encOf (publicOf c) vs rs as mv K_RF).length := by
    rw [encOf_rf, rfOffs_eq rs _ (Nat.le_refl _), List.take_length, rfMsg_eq]
    simp [pubBytes_length]; try omega
  obtain ⟨hb, hd⟩ := sha_ok c vs ws rs as mv ids shaS shaR h K_RF _ _ (by unfold K_RF P; omega)
    hlen hmem
  rw [encOf_rf] at hb hd
  rw [pub_rfc (hdr_of c h.rcpt)] at hd
  exact ⟨hb, map_toNat_inj hd⟩

end Hyp

end Link

end ZkFormal.Near
