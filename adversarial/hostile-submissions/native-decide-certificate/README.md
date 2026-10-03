# Hostile case: native-decide-certificate

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** NATIVE_EVAL_FOUND

## What this proves about the judge

The proof uses `native_decide`, trusting compiled code and `ofReduceBool` instead of the kernel. The policy forbids native evaluation; AXIOM_AUDIT must fail with NATIVE_EVAL_FOUND.
