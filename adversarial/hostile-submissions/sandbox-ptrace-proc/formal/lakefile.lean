import Lake
open Lake DSL
package candidate
require ArenaCore from git "" @ "frozen"
require NearSpec from git "" @ "frozen"
@[default_target] lean_lib Candidate
