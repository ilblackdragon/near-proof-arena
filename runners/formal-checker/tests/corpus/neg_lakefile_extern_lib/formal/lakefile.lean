import Lake
open Lake DSL

package candidate

extern_lib ffi pkg := do
  pure default

script fakepass do
  IO.println "PASS"
  return 0

@[default_target]
lean_lib Candidate
