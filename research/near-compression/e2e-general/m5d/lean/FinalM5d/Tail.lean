import FinalM5d.FinRow

/-!
# FinalM5d.Tail — the template's outputs are the checker's `tailNew` outputs

Lane E's `FINAL` step is `finK` (post-state root, implicit transitions, outgoing reassignment)
followed by `tailNew` (the computed header outputs `o`) and the acceptance `headerOk I.H o`. The
M5d FINAL template starts after `finK`, at `t = (root, congestion, outgoing)`:

* `FinInOK fi I out t` — the `FinIn` cells are the projection of `(I, out, t)` the leaf spec §2
  defines (the upstream segment's obligation; the template hashes them to the public
  `finInDigest`);
* `ClassF1 I out` — the class pins (no transactions, proposals, bandwidth requests, split);
* `Computed ro rs rsh n I out t` — the roots the `FIN` row receives are the spec's: the outcome
  root, the outgoing-receipts root, and the Reed–Solomon `(encoded_merkle_root, encoded_length)`
  of the chunk body (what the `OUTL`/`SHD`/`RS`/`PART`/`MRK` tables compute; open as a whole-AIR
  theorem, see the README).

`tailNew_outputsOf`: then `tailNew afDriver I out t = .ok (outputsOf fi ro rs rsh n)`, and with
`fin_headerOk` (`final_template_sound`), the decoded public header `H` satisfies `headerOk H o`
for **the checker's own** `o`.
-/

namespace FinalM5d.Tail

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E FinalM5d FinalM5d.Link FinalM5d.FinRow
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound

/-- The chunk body `tailNew` encodes. -/
def body (I : Intake) (t : Bytes × Congestion × List Rcpt) : Bytes :=
  u32 I.w.newTxs.length ++ concatAll (I.w.newTxs.map TxD2.raw) ++ encodeRcpts t.2.2

/-- The `FinIn` cells carry the projection of `(I, out, t)` (leaf spec §2). -/
structure FinInOK (fi : Nat → Nat) (I : Intake) (out : MainOutD2)
    (t : Bytes × Congestion × List Rcpt) : Prop where
  root : slice fi 0 32 = t.1
  cong : (⟨leNat (slice fi 33 16), leNat (slice fi 49 16), leNat (slice fi 65 8),
    leNat (slice fi 73 2)⟩ : Congestion) = t.2.1
  gas : leNat (slice fi 75 8) = out.gasUsed
  bal : leNat (slice fi 83 16) = out.balanceBurnt
  gl : leNat (slice fi 99 8) = I.slotB2.gasLimit

/-- Class F1. -/
structure ClassF1 (I : Intake) (out : MainOutD2) : Prop where
  noTx : I.w.newTxs = []
  noProps : out.proposals = []
  noBw : out.bwRequests = []
  noSplit : I.proposed = none

/-- The received roots are the spec's. -/
structure Computed (ro rs rsh : Nat → Nat) (n : Nat) (I : Intake) (out : MainOutD2)
    (t : Bytes × Congestion × List Rcpt) : Prop where
  ro : slice ro 0 32 = outcomeRootD1 out.outcomes
  rsh : slice rsh 0 32 = afDriver.outgoingRoot I.L t.2.2
  emr : encodedMerkleRoot I.c.rsDataParts I.c.rsTotalParts (body I t) = some (slice rs 0 32, n)

theorem tailNew_outputsOf {fi ro rs rsh : Nat → Nat} {n : Nat} {I : Intake} {out : MainOutD2}
    {t : Bytes × Congestion × List Rcpt} (hf : FinInOK fi I out t) (hc : ClassF1 I out)
    (hr : Computed ro rs rsh n I out t) :
    tailNew afDriver I out t = .ok (outputsOf fi ro rs rsh n) := by
  obtain ⟨root, cong, outgoing⟩ := t
  have he := hr.emr
  simp only [body] at he
  simp only [tailNew, he]
  simp only [outputsOf, hf.root, hf.cong, hf.gas, hf.bal, hf.gl, hr.ro, hr.rsh, hc.noTx, hc.noProps,
    hc.noBw, hc.noSplit, List.map_nil]
  rfl

/-- **The FINAL template (class F1), at the `FIN` row.** If `FIN`'s constraints hold on a row with
`act = 1` and byte-valued statement cells, its `FinIn` cells are the projection of the
post-`finK` point `(I, out, t)`, the class pins hold and the received roots are the spec's, then
the chunk inner in the row's statement window decodes to `H`, the checker's own `tailNew`
computes `o`, and **`headerOk H o`** — lane E's `FinalOut`. -/
theorem final_template_sound {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hc : ∀ e ∈ Fin.constraints, e.eval tr t r pub = 0) (hact : ev tr t r pub Fin.act = 1)
    (hb : HbBytes tr t r pub) {I : Intake} {out : MainOutD2} {tf : Bytes × Congestion × List Rcpt}
    (hf : FinInOK (fiN tr t r pub) I out tf) (hcl : ClassF1 I out)
    (hr : Computed (colN "ro" tr t r pub) (colN "rs" tr t r pub) (colN "rsh" tr t r pub)
      (ev tr t r pub (.pub PV_N)) I out tf) :
    ∃ H o, decodeChunkInner (win (hbN tr t r pub)) = .ok H ∧ tailNew afDriver I out tf = .ok o ∧
      headerOk H o = true := by
  obtain ⟨h1, h2⟩ := fin_headerOk hc hact hb
  exact ⟨_, _, h1, tailNew_outputsOf hf hcl hr, h2⟩

end FinalM5d.Tail
