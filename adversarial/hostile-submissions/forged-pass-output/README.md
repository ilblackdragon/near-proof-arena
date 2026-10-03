# Hostile case: forged-pass-output

**Attack family:** forged-output

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** CERTIFICATE_MISSING

## What this proves about the judge

The build script and binaries print `PASS` and WRITE fake gate JSON files into the scratch dir claiming every obligation passed. The judge computes gates itself from measured outcomes and ignores candidate-written files and stdout; the real failure here (no certificate) still produces REJECTED.

## Notes

Primary point: judge-computed gates override forged output. Any real-failing gate (here CERTIFICATE_MISSING) yields REJECTED.
