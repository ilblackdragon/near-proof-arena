import ZkFormal.NearV3.Assembly.NativePrepared
import ZkFormal.NearV3.Assembly.CanonicalReplay

/-! Precise remaining semantic completeness obligation. This module does not
prove FactorComplete: it derives every GoodV3 field except the original bound
on rebuilt post-state bytes, which remains an explicit premise. -/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem checkD0a_good_except_unfolded {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m steps p, let x := nativeExecutionViews k w m steps
      unfoldBytes cb (witnessOfV3 k x) ≤ B → GoodV3 B cb k (nativeHint k w m) p x := by
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hsize := nativeExecutionViews_witness_size hd hm hv hcount hf hcap hepoch hinner hhash
  have hi := executionViews_implicit (w := w)
    (dictionary := sourceDictionarySeeds (sourceKeysV3 k) w.entries) hv hf hcap
  rw [List.map_fst_zip (by omega : k.implicitBlks.length ≤ w.implicit.length)] at hi
  obtain ⟨pc,hpc⟩ := checkD0a_prepClaim_exists hk hw h
  have hh := checkD0_header_of_trace hk hw hc hm ht
  have hr := (relD0a_iff B cb wb).mpr h
  have hg : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1,hk,decide_eq_true_eq] using hr.2.1
  obtain ⟨p,hp,hheader⟩ := prepD0_native_success hpc hk hm hh hd hg
  let x := nativeExecutionViews k w m steps
  have hap : x.applied = appliedReceipts k w := executionViews_applied hd
  obtain ⟨hguards,htx,hcong⟩ := checkD0_claim_guards hk hw hc
  refine ⟨m,steps,p,?_⟩
  dsimp only
  intro hunfold
  refine {
    walk := hk
    prepared := hp
    shape := nativeExecutionViews_shape hk hd hraw hm hv hcount hf hcap hepoch (Nat.le_trans hsize hraw)
    witnessBytes := Nat.le_trans hsize hraw
    mainStoreBytes := nativeExecutionViews_main_payload hm hf hcap
    source := checkD0a_source_semantics hk hw h m steps
    receiptCount := ?_
    receiptIds := ?_
    mainTxRoot := htx
    ownCongestion := ?_
    executions := ⟨m,last,executionViews_main hm hd hf hcap,hi,hheader⟩
    gasLimit := hg
    canonicalScheduler := checkD0a_native_canonical hk hw h hm hv hcount hf hcap
    unfoldedBytes := hunfold
    distinctRequests := ?_ }
  · change (appliedReceipts k w).length = x.applied.length
    rw [hap]
  · change (x.applied.map Receipt.receiptId).Nodup
    rw [hap]
    exact checkD0_applied_nodup hk hw hc
  · simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using hcong
  · have ha8 : k.blks.all (fun b => b.slots.all fun (_,ci) =>
        decide (ci.bwRequests.map (·.toShard)).Nodup) = true := by
      simpa only [a8,hk] using hr.2.2.2.2.2
    intro b hb s ci hslot
    have ht := List.all_eq_true.mp (List.all_eq_true.mp ha8 b hb) (s,ci) hslot
    simpa only [decide_eq_true_eq] using ht

/-- All semantic constructor obligations are derived from acceptance except the
original A7 bound on the reconstructed witness. This implication is deliberately
not named FactorComplete and does not discharge that remaining bound. -/
theorem accepted_good_except_unfolded {B : Nat} {cb wb : Bytes}
    (h : checkD0a B cb wb = .ok ()) :
    ∃ k hint p x, unfoldBytes cb (witnessOfV3 k x) ≤ B → GoodV3 B cb k hint p x := by
  have ha := ((relD0a_iff B cb wb).mpr h).2.2.1
  unfold a2 at ha
  cases hk : walkD0 cb with
  | error err => simp only [hk,Bool.false_eq_true] at ha
  | ok k =>
    cases hw : decodeW wb with
    | error err => simp only [hk,hw,Bool.false_eq_true] at ha
    | ok w =>
      obtain ⟨m,steps,p,hgood⟩ := checkD0a_good_except_unfolded hk hw h
      exact ⟨k,nativeHint k w m,p,nativeExecutionViews k w m steps,hgood⟩

end ZkFormal.NearV3.Assembly
