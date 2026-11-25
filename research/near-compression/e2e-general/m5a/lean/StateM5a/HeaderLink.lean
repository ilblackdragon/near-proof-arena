import NearSpecV3.E2E.Machine

/-!
# StateM5a.HeaderLink — B-T4: the FINAL header link as a chain invariant from INIT

Lane G's G-5 leaves the FINAL leaf the named premise **`decodeChunkInner window = .ok I.H`** (the
statement window its `FIN` row reads is the header of the intake `I` the input record `c9` carries):
a relative FINAL leaf sees only `B_in`, not the run that produced it.

The intake `I` is fixed once, by INIT's step (`c0 → c1`), and every later boundary of the run carries
it (`View.split`: `ctxRoot = ctxD (.intake I)` at every engine / call cut; lane I's chain copies
`ctxRoot` from `c1` to `c9`, every leaf in between copies it). So the link is a property of the
**intake** step, proved here once:

* **`init_header`**: if `CM.step (init cb wb) = .ok (eng I e)` on a non-genesis segment, then the
  claim decodes to `I.c` and **`decodeChunkInner I.c.chunkInner = .ok I.H`** (the machine's own
  `intakeK_post`), and `e` is the `start` position.
* `header_link`: hence, for any window `w` equal to the claim's chunk-inner bytes,
  `decodeChunkInner w = .ok I.H`.

What closes lane G's premise in the tree: (1) the context link — INIT and FINAL share `ctx =
claimDigest s`, INIT's `cb = assemble s.ci secB s.secC` (lane G's `InitDig`), so the claim's
`chunkInner` is `s.ci.chunkInner`, the window FINAL reads (`PublicStmt.decode_encode`, lane E / G);
(2) `ctxRoot` copied along `c1 … c9` (lane D's tree: equal digests on every edge; lane E's
`ctxD` binding), so FINAL's `I` is INIT's. Neither needs a state-lane row: lane B's halves (IF-INTAKE
at `c1`, IF-FINAL at `c9`) do not read the header.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.HeaderLink

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.Successor

/-- **The intake step fixes the header**: `I.H` is the decoded chunk-inner of the claim `I.c`. -/
theorem init_header {cb wb : Bytes} {I : Intake} {e : EConf} (hg : segmentHasGenesis cb = false)
    (h : CM.step (.init cb wb) = .ok (.eng I e)) :
    decodeClaimE cb = .ok I.c ∧ decodeChunkInner I.c.chunkInner = .ok I.H ∧
      e = ⟨.start, initRec afCfg.wasm I.env⟩ := by
  rw [step_init_nongen hg] at h
  rcases hI : intakeK afDriver true cb wb pure with x | J <;> rw [hI] at h <;>
    simp only [Except.map, reduceCtorEq, Except.ok.injEq, Conf.eng.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h1, h2, -⟩ := intakeK_post afDriver true cb wb J hI
  exact ⟨h1, h2, rfl⟩

/-- **The header link** for a window equal to the claim's chunk-inner bytes. -/
theorem header_link {cb wb w : Bytes} {I : Intake} {e : EConf} (hg : segmentHasGenesis cb = false)
    (h : CM.step (.init cb wb) = .ok (.eng I e)) (hw : w = I.c.chunkInner) :
    decodeChunkInner w = .ok I.H := by
  rw [hw]; exact (init_header hg h).2.1

end StateM5a.HeaderLink
