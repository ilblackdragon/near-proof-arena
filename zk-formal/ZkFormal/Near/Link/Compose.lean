import ZkFormal.Near.Link.Statements

/-!
# ZkFormal.Near.Link.Compose — `LinkStmt` from the sub-statements
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

theorem cnt_append (l₁ l₂ : List Msg) (m : List Fp) : cnt (l₁ ++ l₂) m = cnt l₁ m + cnt l₂ m := by
  simp [cnt, List.map_append, List.count_append]

/-- The balance equation of `LinkStmt` in `nearSends`/`nearRecvs` form. -/
theorem linkHyp_of {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs}
    {as : List AcctV} {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
    (hN : NodeWf vs) (hW : WalkWf ws) (hR : RcptWf (publicOf c) rs) (hA : AcctWf as)
    (hM : MrkWf (publicOf c) mv) (hS : SortWf ids) (hSha : ShaFacts shaS shaR)
    (hbal : ∀ b m,
      shaS b m + cnt ((nodeTraffic vs (publicOf c)).sends b) m + cnt ((walkTraffic ws).sends b) m +
        cnt ((rcptTraffic (publicOf c) rs).sends b) m + cnt ((acctTraffic as).sends b) m +
        cnt ((mrkTraffic (publicOf c) mv).sends b) m + cnt ((sortTraffic ids).sends b) m =
      shaR b m + cnt ((nodeTraffic vs (publicOf c)).recvs b) m + cnt ((walkTraffic ws).recvs b) m +
        cnt ((rcptTraffic (publicOf c) rs).recvs b) m + cnt ((acctTraffic as).recvs b) m +
        cnt ((mrkTraffic (publicOf c) mv).recvs b) m + cnt ((sortTraffic ids).recvs b) m) :
    LinkHyp c vs ws rs as mv ids shaS shaR := by
  refine ⟨hN, hW, hR, hA, hM, hS, hSha, fun b m => ?_⟩
  have := hbal b m
  simp only [nearSends, nearRecvs, cnt_append]
  omega

theorem link_of (hC : ClaimStmt) (hRc : ReceiptsStmt) (hNd : NodupStmt) (hT : TrieStmt)
    (hW : WalksStmt) (hRun : RunStmt) (hP : PostStmt) (hO : OutStmt) (hRf : RefundsStmt) :
    LinkStmt := by
  intro c vs ws rs as mv ids shaS shaR _ hN hWw hR hA hM hS hSha hbal
  have h := linkHyp_of hN hWw hR hA hM hS hSha hbal
  obtain ⟨pv, chain, n_pos, n_le, gas_limit, gas_total, len⟩ := hC _ _ _ _ _ _ _ _ _ h
  obtain ⟨inSlice, rcCommit⟩ := hRc _ _ _ _ _ _ _ _ _ h
  obtain ⟨shape, nodes_wf, vals_len, vals_v1, preRoot, size⟩ := hT _ _ _ _ _ _ _ _ _ h
  obtain ⟨rcpt_ok, tokens⟩ := hRun _ _ _ _ _ _ _ _ _ h
  obtain ⟨refundCount, rfCommit⟩ := hRf _ _ _ _ _ _ _ _ _ h
  exact ⟨linkExt vs as rs, pv, chain, n_pos, n_le, gas_limit, gas_total, len, inSlice,
    hNd _ _ _ _ _ _ _ _ _ h, rcCommit, shape, nodes_wf, vals_len, vals_v1, preRoot, size,
    hW _ _ _ _ _ _ _ _ _ h, rcpt_ok, hP _ _ _ _ _ _ _ _ _ h, hO _ _ _ _ _ _ _ _ _ h, refundCount,
    rfCommit, tokens⟩

end ZkFormal.Near
