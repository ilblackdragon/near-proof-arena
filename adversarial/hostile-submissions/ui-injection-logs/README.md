# Hostile case: ui-injection-logs

**Attack family:** ui-log-injection

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The prover is honest but the verifier writes HTML/JS, ANSI escapes and an RTL override to stderr and accepts every proof. The submission is REJECTED at ADVERSARIAL_PROOFS, and the API must additionally return every captured string sanitized -- no raw control characters.

## Notes

attack_family 'ui-log-injection' tells the driver to assert the API response has no raw control chars.

<script>alert('readme-xss')</script>
