import ZkFormal.Chacha.Shuffle.Link
import ZkFormal.Chacha.Complete.All
import ZkFormal.Chacha.Rng.Complete.All

/-!
# ZkFormal.Chacha.Statements — lane v3-chacha top-level statements

The statements the scheduler lane consumes, in L5/L6 style.  Each `…Stmt` is a `Prop`; the
theorem below it proves it.

* `ChachaBlockStmt` — row constraints ⇒ `NearSpecV3.chachaBlock` (`Sound.ff_block`);
* `ChachaContractStmt` — every provided `busChacha` message is the spec output
  (`Sound.chacha_contract`);
* `RngStreamStmt` — the words drawn from `Rng.ofSeed seed` are `streamWord (leWords seed)`
  (spec side, `rng_stream`); `RngContractStmt` — each word drawn by `genV3` is that stream word
  (`Rng.rng_contract`);
* `GenIndexContractStmt` — every provided `busGen` message is a `genIndex 64` result
  (`Rng.genIndex_contract`; in a v2 AIR: `genIndex_sound`);
* `ShuffleContractStmt` — every `shufV3` instance outputs `NearSpecV3.shuffle` of its inputs
  (`Shuffle.shuffle_contract`; in a v2 AIR the hypotheses come from `genRecv_of_holdsP` and
  `memBal_of_holdsP`);
* `ChachaCompleteStmt` — `Complete.chacha_complete`; `GenCompleteStmt` — `Rng.Complete.gen_complete`.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.Algebra NearSpecV3

def ChachaBlockStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, Sound.ChLocal tr t pub → ∀ f j, f < tr.height t → j < 4 →
    Sound.nv tr t f (Table.colF j) = 1 →
    Sound.KOk tr t f ∧ ∀ kk, kk < 4 →
      Sound.xw tr t f kk = (chachaBlock (Sound.keyOf tr t f) (Sound.kw tr t f 8))[4 * kk + j]!

theorem chachaBlockStmt : ChachaBlockStmt :=
  fun _ _ _ hL _ _ hf hj hF => Sound.ff_block hL hf hj hF

def ChachaContractStmt : Prop :=
  ∀ (tr : Trace Fp) t pub busChacha, Sound.ChLocal tr t pub → ∀ r, r < tr.height t →
    ∀ i ∈ Table.interactions busChacha, i.multNat tr t r pub ≠ 0 →
      ∃ key ctr idx, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ ctr < 2 ^ 26 ∧ idx < 16 ∧
        i.bus = busChacha ∧ i.send = true ∧
        i.msgVal tr t r pub = Sound.chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!)

theorem chachaContractStmt : ChachaContractStmt :=
  fun _ _ _ busChacha hL _ hr _ hi hm => Sound.chacha_contract hL busChacha hr hi hm

def RngStreamStmt : Prop :=
  ∀ (seed : List UInt8) (n : Nat),
    draws n (Rng.ofSeed seed) = ((List.range n).map (streamWord (leWords seed)), rngAt (leWords seed) n)

theorem rngStreamStmt : RngStreamStmt := rng_stream

def RngContractStmt : Prop :=
  ∀ (tr : Trace Fp) t pub busChacha busGen, Rng.GLocal tr t pub →
    Rng.ChachaRecv tr t pub busChacha busGen → ∀ r, r < tr.height t → cv tr t r Rng.Table.colA = 1 →
      Rng.vv tr t r = streamWord (Rng.keyOf tr t r) (Rng.kv tr t r)

theorem rngContractStmt : RngContractStmt :=
  fun _ _ _ _ _ hL hW _ hr ha => (Rng.rng_contract hL hW hr ha).1

def GenIndexContractStmt : Prop :=
  ∀ (tr : Trace Fp) t pub busChacha busGen, Rng.GLocal tr t pub →
    Rng.ChachaRecv tr t pub busChacha busGen → ∀ r, r < tr.height t → cv tr t r Rng.Table.colAcc = 1 →
      ∃ key kstart n j kend, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ 1 ≤ n ∧ n < 2 ^ 14 ∧
        kstart < 2013265921 ∧ kend < 2 ^ 30 + 1 ∧
        genAt 64 n key kstart = some (j, kend) ∧
        genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend) ∧
        (Rng.Table.interactions busChacha busGen)[1]!.msgVal tr t r pub = Rng.genMsg key kstart n j kend

theorem genIndexContractStmt : GenIndexContractStmt :=
  fun _ _ _ _ _ hL hW _ hr hacc => Rng.genIndex_contract hL hW hr hacc

def ShuffleContractStmt : Prop :=
  ∀ (tr : Trace Fp) t pub (B : Shuffle.Buses), B.ok → Shuffle.SLocal tr t pub → Shuffle.GenRecv tr t pub →
    tr.height t ≤ 2 ^ 20 → Shuffle.MemBal B tr t pub → ∀ f, f < tr.height t →
    cv tr t f Shuffle.Table.colFin = 1 →
    ∃ L, 1 ≤ L ∧ L ≤ f + 1 ∧ L < 2 ^ 14 + 1 ∧ cv tr t f Shuffle.Table.colL = L ∧
      (∀ x, x < L → cv tr t (f - x) Shuffle.Table.colA = 1 ∧ cv tr t (f - x) Shuffle.Table.colQ = x ∧
        cv tr t (f - x) Shuffle.Table.colLid = cv tr t f Shuffle.Table.colLid) ∧
      ∃ l', shuffle ((List.range L).map fun x => tr.cell t (f - x) Shuffle.Table.colV0)
          (rngAt (Shuffle.skey tr t f) (cv tr t f Shuffle.Table.colKs)) =
            some (l', rngAt (Shuffle.skey tr t f) (cv tr t f Shuffle.Table.colKq)) ∧
        ∀ x, x < L → l'[x]? = some (Shuffle.Table.outE.eval tr t (f - x) pub)

theorem shuffleContractStmt : ShuffleContractStmt :=
  fun _ _ _ B hB hL hG hH hM _ hf hfin => Shuffle.shuffle_contract B hB hL hG hH hM hf hfin

/-- **Shuffle soundness inside a v2 AIR**: tables `tc` (ChaCha), `tg` (stream), `ts` (shuffle);
ChaCha is the only sender on `busChacha`, the stream table the only sender on `busGen`, and the
memory bus is private to the shuffle table. -/
theorem shuffle_sound {AP : V2.AirP} {pub : List Fp} {tr : Trace Fp} (hH : V2.HoldsP AP pub tr)
    {tc tg ts busChacha : Nat} {B : Shuffle.Buses} (hB : B.ok) (hcg : busChacha ≠ B.gen)
    (htc : tc < AP.tables.length) (hTc : AP.tables[tc]! = Table.table busChacha)
    (htg : tg < AP.tables.length) (hTg : AP.tables[tg]! = Rng.Table.table busChacha B.gen)
    (hts : ts < AP.tables.length)
    (hTs : AP.tables[ts]! = Shuffle.Table.table B.bin B.bout B.mem B.gen B.shuf)
    (honlyC : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = busChacha → i.send = false)
    (hpubC : ∀ seg ∈ AP.pubSegs, seg.bus = busChacha → seg.send = false)
    (honlyG : ∀ t, t < AP.tables.length → t ≠ tg → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = B.gen → i.send = false)
    (hpubG : ∀ seg ∈ AP.pubSegs, seg.bus = B.gen → seg.send = false)
    (honlyM : ∀ u, u < AP.tables.length → u ≠ ts → ∀ i ∈ AP.tables[u]!.interactions, i.bus ≠ B.mem)
    (hpubM : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B.mem) (hlog : tr.log ts ≤ 20)
    {f : Nat} (hf : f < tr.height ts) (hfin : cv tr ts f Shuffle.Table.colFin = 1) :
    ∃ L, 1 ≤ L ∧ L ≤ f + 1 ∧ L < 2 ^ 14 + 1 ∧ cv tr ts f Shuffle.Table.colL = L ∧
      (∀ x, x < L → cv tr ts (f - x) Shuffle.Table.colA = 1 ∧ cv tr ts (f - x) Shuffle.Table.colQ = x ∧
        cv tr ts (f - x) Shuffle.Table.colLid = cv tr ts f Shuffle.Table.colLid) ∧
      ∃ l', shuffle ((List.range L).map fun x => tr.cell ts (f - x) Shuffle.Table.colV0)
          (rngAt (Shuffle.skey tr ts f) (cv tr ts f Shuffle.Table.colKs)) =
            some (l', rngAt (Shuffle.skey tr ts f) (cv tr ts f Shuffle.Table.colKq)) ∧
        ∀ x, x < L → l'[x]? = some (Shuffle.Table.outE.eval tr ts (f - x) pub) := by
  have hL : Shuffle.SLocal tr ts pub := by
    have := local_of_holdsP hH hts; rw [hTs] at this; exact this
  exact Shuffle.shuffle_contract B hB hL
    (genRecv_of_holdsP hH hcg htc hTc htg hTg hts hTs honlyC hpubC honlyG hpubG)
    (Nat.pow_le_pow_right (by decide) hlog) (memBal_of_holdsP hH hts hTs honlyM hpubM) hf hfin

def ChachaCompleteStmt : Prop :=
  ∀ (reqs : List Gen.Req), (∀ R ∈ reqs, Gen.ReqOk R) → 86 * reqs.length ≤ 2 ^ Table.maxLog →
    ∀ busChacha t pub, Sound.ChLocal (Gen.honestTrace reqs) t pub ∧
      ∀ m, tableBusCount (Table.interactions busChacha) (Gen.honestTrace reqs) t pub busChacha true m =
        (Gen.expected reqs).count m

theorem chachaCompleteStmt : ChachaCompleteStmt :=
  fun reqs hok hrows busChacha t pub =>
    ⟨Complete.chLocal_honest reqs hok hrows t pub,
     fun m => ((Complete.chacha_complete reqs hok hrows busChacha).2.2.2 t pub m).1⟩

def GenCompleteStmt : Prop :=
  ∀ (calls : List Rng.Gen.Call), (∀ C ∈ calls, Rng.Gen.CallOk C) →
    (Rng.Gen.honestRows calls).length ≤ 2 ^ Rng.Table.maxLog →
    ∀ busChacha busGen t pub, busChacha ≠ busGen → Rng.GLocal (Rng.Gen.honestTrace calls) t pub ∧
      ∀ m, tableBusCount (Rng.Table.interactions busChacha busGen) (Rng.Gen.honestTrace calls) t pub
          busChacha false m = (Rng.Gen.expectedWords calls).count m ∧
        tableBusCount (Rng.Table.interactions busChacha busGen) (Rng.Gen.honestTrace calls) t pub
          busGen true m = (Rng.Gen.expectedGen calls).count m

theorem genCompleteStmt : GenCompleteStmt :=
  fun calls hok hrows busChacha busGen t pub hne =>
    ⟨Rng.Complete.gLocal_honest calls hok t pub, fun m =>
      let h := ((Rng.Complete.gen_complete calls hok hrows busChacha busGen hne).2.2.2 t pub m)
      ⟨h.1, h.2.2.1⟩⟩

end ZkFormal.Chacha
