import M5T1.RxSem
import NearSpecV3.Successor.StorageExecution

/-!
# M5T1.SpecLink — the spec's receipt step computes the `RX` row's values

Under `RxRel v` (`RxSem.lean`), for an action receipt carrying ONE `FunctionCall` action, the
spec's own functions compute exactly the row's numbers:

* `consts` — every `M5T1` constant is the spec's (`Fees.*`, `Lim.*`, `Params.*`);
* `actExec_fc`, `prepaid_fc` — the exec fee of the call and the prepaid sums of `[act]`;
* `refunds_fc` — `D2.refunds` returns exactly the one gas-refund receipt of `v.rf`, charge 0;
* `stake_fc` — `storageStakeOk` of the account the call leaves accepts;
* `merge_fc` — the merge (`Successor.StorageExecution.actionLoop`) `add64`s of `res0` (NAR exec)
  and the call's `ar1` (`functionCallRecordedF`: exec fee + VM burnt / used / compute);
* `burnt_fc` — step 8 of `applyActionReceipt` (burnt amount, receiver reward, `tx_burnt`);
* `totals_fc` — the receipt state's totals (`processWithTotals`, step 8's `add128`s);
* `validBase_fc`, `validActs_fc` — the `FunctionCall` part of `validReceipt`.
-/

namespace M5T1.SpecLink

open NearSpec NearSpecV3 NearSpecV3.D2

theorem two64_eq : two64 = U64 := rfl
theorem two128_eq : two128 = U128 := rfl

theorem add64_of {a b c : Nat} (h : a + b < U64) (hc : a + b = c) : add64 a b = some c := by
  unfold add64; rw [ite_eq_left (show a + b < two64 from h), hc]

theorem add128_of {a b c : Nat} (h : a + b < U128) (hc : a + b = c) : add128 a b = some c := by
  unfold add128; rw [ite_eq_left (show a + b < two128 from h), hc]

theorem narE : Fees.nar.exec = NAR_EXEC := rfl
theorem narC : Fees.nar.execCompute = NAR_EXEC := rfl

/-! ## 1. Constants -/

theorem consts :
    NAR_EXEC = Fees.nar.exec ∧ NAR_EXEC = Fees.nar.execCompute ∧
    FC_BASE_EXEC = Fees.fcBase.exec ∧ FC_BASE_EXEC = Fees.fcBase.execCompute ∧
    FC_BYTE_EXEC = Fees.fcByte.exec ∧ FC_BYTE_EXEC = Fees.fcByte.execCompute ∧
    CREATE_ACCOUNT_EXEC = Fees.createAccount.exec ∧
    STORAGE_PER_BYTE = Params.storageAmountPerByte ∧
    ZERO_BALANCE_LIMIT = Params.zeroBalanceStorageLimit ∧
    MAX_METHOD_NAME = Lim.maxMethodName ∧ MAX_ARGS = Lim.maxArgs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. The exec fee and the prepaid sums of the one-action list -/

/-- The exec fee of the call (gas = compute). -/
def fcxOf (m a : Bytes) : Nat := FC_BASE_EXEC + FC_BYTE_EXEC * (m.length + a.length)

theorem actExec_fc (recv raw m a : Bytes) (g d : Nat) :
    actExec recv (.base ⟨raw, .fcall m a g d⟩) = ⟨fcxOf m a, fcxOf m a⟩ := rfl

theorem prepaidExec_fc (recv raw m a : Bytes) (g d : Nat) (h : fcxOf m a < two64) :
    prepaidExec recv [.base ⟨raw, .fcall m a g d⟩] = some ⟨fcxOf m a, fcxOf m a⟩ := by
  have e : prepaidExec recv [.base ⟨raw, .fcall m a g d⟩] =
      Cost.add ⟨fcxOf m a, fcxOf m a⟩ Cost.zero := rfl
  rw [e]; unfold Cost.add
  simp [Cost.zero, h]

theorem totalPrepaidGas_fc (raw m a : Bytes) (g d : Nat) (h : g < two64) :
    totalPrepaidGas [.base ⟨raw, .fcall m a g d⟩] = some g := by
  simp [totalPrepaidGas, optAll, sumNat64, add64, Base.prepaidGas, h]

theorem prepaidSend_fc (raw m a : Bytes) (g d : Nat) :
    prepaidSend [.base ⟨raw, .fcall m a g d⟩] = some Cost.zero := by
  simp [prepaidSend, optAll, sumCosts, Cost.add, Cost.zero, two64, Params.two64]

theorem totalDeposit_fc (raw m a : Bytes) (g d : Nat) (h : d < two128) :
    totalDeposit [.base ⟨raw, .fcall m a g d⟩] = some d := by
  simp [totalDeposit, optAll, sumNat128, add128, Base.deposit, h]

/-! ## 3. Refunds -/

/-- The gas-refund receipt `rs2` of `D2.refunds`. -/
def refundRcpt (signer : Bytes) (pk : PublicKey) (amount : Nat) : Rcpt :=
  ⟨AccountId.system, signer, zero32, .action false ⟨false, signer, none, pk, 0, [], [],
    [.base ⟨[3] ++ u128 amount, .transfer amount⟩]⟩⟩

theorem ok?_some {α : Type} (x : α) (e : String) : ok? (some x) e = .ok x := rfl

theorem eok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem refunds_fc (v : RxVals) (hv : RxRel v) (r : Rcpt) (a : ActionR) (res : AR)
    (raw m args : Bytes)
    (hacts : a.actions = [.base ⟨raw, .fcall m args v.gas v.dep⟩])
    (hm : m.length = v.lm) (ha : args.length = v.la)
    (hok : res.ok = true) (hgu : res.gasUsed = v.gu) (hgb : res.gasBurnt = v.gb) :
    refunds r a res v.gp v.burn false = .ok ([refundRcpt a.signer a.signerPk v.rf], 0) := by
  have hfx : fcxOf m args = v.fcx := by rw [fcxOf, hm, ha, hv.fcx]
  have hdep := totalDeposit_fc raw m args v.gas v.dep (by rw [two128_eq]; exact hv.dep_lt')
  have hpg' : totalPrepaidGas [.base ⟨raw, .fcall m args v.gas v.dep⟩] = some v.gas :=
    totalPrepaidGas_fc raw m args v.gas v.dep (by rw [two64_eq]; exact hv.gas_lt)
  have hps := prepaidSend_fc raw m args v.gas v.dep
  have hpe := prepaidExec_fc r.recv raw m args v.gas v.dep
    (by rw [hfx, two64_eq]; exact hv.fcx_lt)
  rw [hfx] at hpe
  have h1 : add64 v.gas Cost.zero.gas = some v.gas :=
    add64_of (by have := hv.gas_lt; simp only [Cost.zero]; omega) (by simp [Cost.zero])
  have h2 : add64 v.fcx Fees.nar.exec = some v.pexec := by
    have := hv.pexec_lt; have := hv.pexec
    exact add64_of (by rw [narE]; omega) (by rw [narE]; omega)
  have h3 : add64 v.gas v.pexec = some v.tot := by
    have := hv.tot_lt; have := hv.tot
    exact add64_of (by omega) (by omega)
  have hgross : v.tot - v.gu = v.gross := by have := hv.gross; omega
  have hnlt : ¬ v.tot < v.gu := by have := hv.gross; omega
  have hunu : ¬ v.gp * v.gross ≥ two128 := by
    rw [two128_eq, ← hv.unu]; have := hv.unu_lt; omega
  have hsub : v.gp - v.burn = v.gpb := by have := hv.gpb; omega
  have hsur : ¬ v.gpb * v.gb ≥ two128 := by
    rw [two128_eq, ← hv.sur]; have := hv.sur_lt; omega
  have hbc : ¬ v.burn * Fees.createAccount.exec ≥ two128 := by
    rw [two128_eq, show Fees.createAccount.exec = CREATE_ACCOUNT_EXEC from rfl, ← hv.bc]
    have := hv.bc_lt; omega
  have h4 : add128 (v.gp * v.gross) (v.gpb * v.gb) = some v.rf := by
    rw [← hv.unu, ← hv.sur]
    exact add128_of (by rw [← hv.rf]; exact hv.rf_lt) hv.rf.symm
  have hrf : v.rf > 0 := hv.rf_pos
  unfold refunds
  rewrite [hacts, hdep, hpg', hps, hpe]
  rewrite [ok?_some, eok_bind, ok?_some, eok_bind, ok?_some, eok_bind, h1, ok?_some, eok_bind,
    ok?_some, eok_bind, h2, ok?_some, eok_bind, h3, ok?_some, eok_bind]
  simp only [hok, hgu, hgb, ite_true, hnlt, ite_false, hgross]
  simp only [hunu, hsub, hsur, hbc, ite_false, Bool.false_eq_true, Nat.sub_zero]
  rewrite [h4, ok?_some, eok_bind, ite_eq_right (Nat.lt_irrefl 0),
    ite_eq_left hrf]
  rfl

/-! ## 4. Storage stake -/

theorem stake_fc (v : RxVals) (hv : RxRel v) (c : Contract) :
    storageStakeOk ⟨v.vbal, v.lck, v.vus, c, false⟩ v.vbal = some true := by
  have hreq : Params.storageAmountPerByte * v.vus = v.req := hv.req.symm
  have := hv.req_lt; have := hv.bal_lt; have hs := hv.stake
  simp only [storageStakeOk, hreq, two128_eq]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [Option.some.injEq, Bool.or_eq_true, decide_eq_true_eq]
  rcases hs with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## 5. The merge -/

/-- `res0` (NAR exec) merged with the call's `ar1` (`functionCallRecordedF`: `gasBurnt := ex.gas +
burnt`, `gasFC := 0 + burnt`, `gasUsed := ex.gas + used`, `compute := ex.compute + computeUsage`;
`tokensBurnt := 0`, `subsidized := 0 + s.subsidized`). -/
theorem merge_fc (v : RxVals) (hv : RxRel v) :
    add64 Fees.nar.exec (v.fcx + v.vb) = some v.gb ∧
    add64 0 (0 + v.vb) = some v.vb ∧
    add64 Fees.nar.exec (v.fcx + v.vu) = some v.gu ∧
    add64 Fees.nar.execCompute (v.fcx + v.vc) = some v.cu ∧
    add128 0 0 = some 0 ∧
    add128 0 (0 + v.vsub) = some v.vsub ∧
    0 + v.vb ≤ v.fcx + v.vb ∧
    v.fcx + v.vb ≤ v.fcx + v.vu := by
  have := hv.gb; have := hv.gb_lt; have := hv.gu; have := hv.gu_lt; have := hv.cu
  have := hv.cu_lt; have := hv.vb_lt; have := hv.vsub_lt; have := hv.vb_le
  rw [narE, narC]
  refine ⟨add64_of (by omega) (by omega), add64_of (by omega) (by omega),
    add64_of (by omega) (by omega), add64_of (by omega) (by omega),
    add128_of (by simp [U128]) rfl, add128_of (by omega) (by omega), by omega, by omega⟩

/-! ## 6. Burnt amounts and the receiver reward (step 8 of `applyActionReceipt`) -/

theorem burnt_fc (v : RxVals) (hv : RxRel v) :
    v.burn = min v.gp v.egp ∧
    v.burn * v.gb < two128 ∧
    (add128 (v.burn * v.gb) 0 >>= fun x => add128 x 0) = some v.tb ∧
    v.vb * 3 < two64 ∧
    v.burn * (v.vb * 3 / 10) = v.rew ∧
    v.rew < two128 ∧
    v.rew ≤ v.tb ∧
    v.vbal + v.rew < two128 ∧
    v.tb - v.rew = v.txb := by
  have htb : v.burn * v.gb = v.tb := hv.tb.symm
  have := hv.tb_lt; have := hv.fc3_lt; have := hv.rew_lt; have := hv.txb
  have := hv.amt2; have := hv.amt2_lt
  refine ⟨hv.burn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htb, two128_eq]; exact hv.tb_lt
  · rw [htb, add128_of (c := v.tb) (by have := hv.tb_lt; omega) (by omega)]
    exact add128_of (by have := hv.tb_lt; omega) (by omega)
  · rw [two64_eq]; omega
  · rw [hv.rew, hv.q10, Nat.mul_comm 3]
  · rw [two128_eq]; exact hv.rew_lt
  · omega
  · rw [two128_eq]; omega
  · omega

/-! ## 7. Totals -/

theorem totals_fc (v : RxVals) (hv : RxRel v) :
    add64 v.gin v.gb = some v.gout ∧
    add64 v.cin v.cu = some v.cout ∧
    add128 v.tbin v.txb = some v.tbout ∧
    add128 v.sbin v.vsub = some v.sbout ∧
    add128 0 v.vsub = some v.vsub ∧
    v.wgin + v.vb = v.wgout := by
  have := hv.gout; have := hv.gout_lt; have := hv.cout; have := hv.cout_lt
  have := hv.tbout; have := hv.tbout_lt; have := hv.sbout; have := hv.sbout_lt
  have := hv.vsub_lt
  exact ⟨add64_of (by omega) (by omega), add64_of (by omega) (by omega),
    add128_of (by omega) (by omega), add128_of (by omega) (by omega),
    add128_of (by omega) (by omega), hv.wgout.symm⟩

/-! ## 8. `validReceipt`: the FunctionCall part -/

theorem validBase_fc (v : RxVals) (hv : RxRel v) (m args : Bytes)
    (hm : m.length = v.lm) (ha : args.length = v.la) :
    validBase (.fcall m args v.gas v.dep) = true := by
  have := hv.gas_ne; have := hv.lm_le; have := hv.la_le
  simp only [MAX_METHOD_NAME, MAX_ARGS] at *
  simp [validBase, Lim.maxMethodName, Lim.maxArgs, hm, ha]
  omega

/-- The action list check of `validReceipt false`; `RxRel` does not bound the prepaid gas by
`Lim.maxTotalPrepaidGas`, so that bound is a hypothesis. -/
theorem validActs_fc (v : RxVals) (hv : RxRel v) (raw m args : Bytes)
    (hm : m.length = v.lm) (ha : args.length = v.la) (hg : v.gas ≤ Lim.maxTotalPrepaidGas) :
    validActs false [.base ⟨raw, .fcall m args v.gas v.dep⟩] = true := by
  have hb := validBase_fc v hv m args hm ha
  have hpg : totalPrepaidGas [.base ⟨raw, .fcall m args v.gas v.dep⟩] = some v.gas :=
    totalPrepaidGas_fc raw m args v.gas v.dep (by rw [two64_eq]; exact hv.gas_lt)
  simp only [validActs, hpg, List.all_cons, List.all_nil, hb]
  simp [deleteLast, isDeleteAccount, Lim.maxActions, hg]

end M5T1.SpecLink

#print axioms M5T1.SpecLink.consts
#print axioms M5T1.SpecLink.actExec_fc
#print axioms M5T1.SpecLink.prepaidExec_fc
#print axioms M5T1.SpecLink.totalPrepaidGas_fc
#print axioms M5T1.SpecLink.prepaidSend_fc
#print axioms M5T1.SpecLink.totalDeposit_fc
#print axioms M5T1.SpecLink.refunds_fc
#print axioms M5T1.SpecLink.stake_fc
#print axioms M5T1.SpecLink.merge_fc
#print axioms M5T1.SpecLink.burnt_fc
#print axioms M5T1.SpecLink.totals_fc
#print axioms M5T1.SpecLink.validBase_fc
#print axioms M5T1.SpecLink.validActs_fc
