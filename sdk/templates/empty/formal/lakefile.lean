import Lake
open Lake DSL

-- The certificate project. Only packages on the challenge's allowlist
-- (toolchain_policy.allowed_packages, at the pinned commits) may be required.
-- The arena's `formal-core` (admission theorem type, games, assumptions) and
-- the NEAR semantics slice are provided by the judge at the pinned commit;
-- uncomment and pin them as instructed by the challenge:
--
-- require formalCore from git "<formal-core repo>" @ "<pinned commit>"

package candidate

@[default_target]
lean_lib Candidate
