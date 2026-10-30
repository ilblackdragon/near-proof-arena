#!/bin/sh
# hand-over evidence runs
W=/data/illia/nearproof/.claude/worktrees/agent-a2e72e08b02b153e5
H=/data/illia/nearproof-deps/w12-o4b/ho
A=/data/illia/nearproof-deps/w12-o4b/check-after
B=/data/illia/nearproof-deps/w12-o4b/check-before
cd $W
rp() { python3 tools/d3/replay_successor.py --binary "$1" --tier "$2" --cases-file "$3" --out "$4" --jobs "$5" --timeout 7200 > "$4.log" 2>&1; echo "$4 exit $?" >> $H/status; }
rp $A signed /data/illia/nearproof-deps/gateb-prefreeze/corpus-cases.txt $H/corpus-signed-after 6 &
(
rp $A signed $H/rs.txt $H/rs-signed-after 4
rp $A runtimeLimits $H/rs.txt $H/rs-runtimeLimits-after 4
rp $A signed $H/shard13.txt $H/s13-signed-after 4
rp $B signed $H/shard13.txt $H/s13-signed-before 4
rp $A signed $H/census.txt $H/census-signed-after 4
rp $A runtimeLimits $H/census.txt $H/census-runtimeLimits-after 4
rp $A signed $H/fx.txt $H/fx-signed-after 4
rp $A runtimeLimits $H/fx.txt $H/fx-runtimeLimits-after 4
) &
wait
echo ALL >> $H/status
