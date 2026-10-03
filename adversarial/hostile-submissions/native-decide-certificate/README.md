# Hostile case: native-decide-certificate

**Attack family:** axiom-audit

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** NATIVE_EVAL_FOUND

## What this proves about the judge

The proof uses `native_decide`, which trusts compiled code and the `Lean.ofReduceBool` axiom instead of the kernel. The policy forbids native evaluation; AXIOM_AUDIT must fail.
