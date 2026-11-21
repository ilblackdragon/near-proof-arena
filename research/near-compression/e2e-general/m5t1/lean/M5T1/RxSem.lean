import M5T1.Ids

/-!
# M5T1.RxSem — what one `RX` row says, over the naturals

`RxVals` are the numbers an `RX` row carries (each the little-endian value of its byte group;
`lm`, `la` field elements below `2^24`). `RxRel v` is the conjunction of the equations and bounds
the row's constraints enforce (`RxField.rx_rel_of_row` derives it from the row's constraints and
its byte / bit ranges). `SpecLink` proves that under `RxRel` the spec's own functions
(`D2.refunds`, `actExec`, `storageStakeOk`, the merge's `add64`s, the burnt amounts) compute
exactly these values.

Naming (the `RX` byte groups): `gp` receipt gas price (`purchase`), `egp` chunk gas price, `gas`,
`dep` the action's prepaid gas and deposit, `lm`/`la` method / args lengths, `amt`/`lck` the
receiver's balance / locked before the call, `vb`/`vu`/`vc` the VM's burnt / used gas and compute,
`vbal`/`vus`/`vsub` the VM's final balance, storage usage, subsidized amount; the rest computed.
-/

namespace M5T1

structure RxVals where
  lm : Nat
  la : Nat
  gp : Nat
  egp : Nat
  gas : Nat
  dep : Nat
  amt : Nat
  lck : Nat
  vb : Nat
  vu : Nat
  vc : Nat
  vbal : Nat
  vus : Nat
  vsub : Nat
  fcx : Nat
  gb : Nat
  gu : Nat
  cu : Nat
  req : Nat
  burn : Nat
  pexec : Nat
  tot : Nat
  gross : Nat
  unu : Nat
  gpb : Nat
  sur : Nat
  bc : Nat
  rf : Nat
  tb : Nat
  q10 : Nat
  rew : Nat
  amt2 : Nat
  txb : Nat
  glim : Nat
  gin : Nat
  cin : Nat
  tbin : Nat
  sbin : Nat
  wgin : Nat
  gout : Nat
  cout : Nat
  tbout : Nat
  sbout : Nat
  wgout : Nat
  deriving Repr, DecidableEq

def U64 : Nat := 2 ^ 64
def U128 : Nat := 2 ^ 128

/-- The relations an `RX` row enforces. -/
structure RxRel (v : RxVals) : Prop where
  -- byte widths of the inputs and of the totals in
  gp_lt : v.gp < U128
  egp_lt : v.egp < U128
  gas_lt : v.gas < U64
  dep_lt' : v.dep < U128
  amt_lt : v.amt < U128
  lck_lt : v.lck < U128
  vb_lt : v.vb < U64
  vu_lt : v.vu < U64
  vc_lt : v.vc < U64
  vbal_lt : v.vbal < U128
  vus_lt : v.vus < U64
  vsub_lt : v.vsub < U128
  glim_lt : v.glim < U64
  gin_lt : v.gin < U64
  cin_lt' : v.cin < U64
  tbin_lt : v.tbin < U128
  sbin_lt : v.sbin < U128
  wgin_lt : v.wgin < U128
  wgout_lt : v.wgout < U128
  -- `actExec` of the FunctionCall, and the merge (`add64`, `ar.gasBurnt ≤ ar.gasUsed`)
  fcx : v.fcx = FC_BASE_EXEC + FC_BYTE_EXEC * (v.lm + v.la)
  fcx_lt : v.fcx < U64
  gb : v.gb = NAR_EXEC + v.fcx + v.vb
  gb_lt : v.gb < U64
  gu : v.gu = NAR_EXEC + v.fcx + v.vu
  gu_lt : v.gu < U64
  cu : v.cu = NAR_EXEC + v.fcx + v.vc
  cu_lt : v.cu < U64
  vb_le : v.vb ≤ v.vu
  -- the deposit does not overflow the balance; a V1 account (`amount ≠ u128::MAX`)
  dep_lt : v.amt + v.dep < U128
  amt_ne : v.amt ≠ U128 - 1
  -- storage stake of the account the call leaves
  req : v.req = STORAGE_PER_BYTE * v.vus
  req_lt : v.req < U128
  bal_lt : v.vbal + v.lck < U128
  stake : v.req ≤ v.vbal + v.lck ∨ v.vus ≤ ZERO_BALANCE_LIMIT
  -- prices
  burn : v.burn = min v.gp v.egp
  -- refunds (`D2.refunds`: prepaid = gas, prepaid exec = fcx + nar)
  pexec : v.pexec = v.fcx + NAR_EXEC
  pexec_lt : v.pexec < U64
  tot : v.tot = v.gas + v.pexec
  tot_lt : v.tot < U64
  gross : v.gu + v.gross = v.tot
  unu : v.unu = v.gp * v.gross
  unu_lt : v.unu < U128
  gpb : v.burn + v.gpb = v.gp
  sur : v.sur = v.gpb * v.gb
  sur_lt : v.sur < U128
  bc : v.bc = v.burn * CREATE_ACCOUNT_EXEC
  bc_lt : v.bc < U128
  rf : v.rf = v.unu + v.sur
  rf_lt : v.rf < U128
  rf_pos : 0 < v.rf
  -- burnt amounts and the receiver reward
  tb : v.tb = v.burn * v.gb
  tb_lt : v.tb < U128
  fc3_lt : 3 * v.vb < U64
  q10 : v.q10 = 3 * v.vb / 10
  rew : v.rew = v.burn * v.q10
  rew_lt : v.rew < U128
  amt2 : v.amt2 = v.vbal + v.rew
  amt2_lt : v.amt2 < U128
  txb : v.rew + v.txb = v.tb
  -- the receipt state's totals
  tbout : v.tbout = v.tbin + v.txb
  tbout_lt : v.tbout < U128
  sbout : v.sbout = v.sbin + v.vsub
  sbout_lt : v.sbout < U128
  wgout : v.wgout = v.wgin + v.vb
  gout : v.gout = v.gin + v.gb
  gout_lt : v.gout < U64
  cout : v.cout = v.cin + v.cu
  cout_lt : v.cout < U64
  -- the receipt is processed, not delayed; `validReceipt` of the action
  cin_lt : v.cin < v.glim
  gas_ne : v.gas ≠ 0
  lm_le : v.lm ≤ MAX_METHOD_NAME
  la_le : v.la ≤ MAX_ARGS

end M5T1
