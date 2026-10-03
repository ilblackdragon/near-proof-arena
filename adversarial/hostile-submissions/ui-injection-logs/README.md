# Hostile case: ui-injection-logs

**Attack family:** ui-log-injection

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The candidate emits HTML/JS, ANSI escapes and RTL overrides in its name fields, README and especially stderr/error messages, trying to inject into the dashboard/logs. The proof is also bogus, so the submission is REJECTED; additionally the API must return every string escaped/sanitized with no raw control characters.

## Notes

attack_family 'ui-log-injection' tells the e2e driver to additionally assert the API response contains no raw control chars and escapes HTML.

<script>alert('readme-xss')</script>
‮latipsoh‬ ANSI [31mRED[0m
