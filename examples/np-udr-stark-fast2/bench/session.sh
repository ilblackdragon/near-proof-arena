#!/bin/bash
# session.sh <tag> <package-src-dir (with vendor)> <built-out-dir> [classes...]
# One live-equivalent BENCHMARK session (worker's real stage, Firecracker, CPUs 8-15).
set -e
tag=$1 pkg=$2 out=$3
R=/data/illia/nearproof-wt/zk-L8f
W=/data/illia/nearproof-wt/zk-L8f-bench/$tag
rm -rf $W; mkdir -p $W/bundle
( cd $pkg && git ls-files -z . | xargs -0 tar -cf - ) | tar -xf - -C $W/bundle
$R/target/debug/arena pack -o $W/package.tar $W/bundle >/dev/null
cp -a $out $W/bundle/out
F=$R/oracle/fixtures/public
$W/bundle/out/prepare --params $F/params.bin --out $W/public
CHAL=$R/challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json
HEAVY_MEM=40G /data/illia/nearproof-deps/bin/heavy $R/target/debug/examples/bench_session \
  --challenge $CHAL --package $W/package.tar --bundle-dir $W/bundle --public-dir $W/public \
  --native-verifier $W/bundle/out/verify --oracle /data/illia/nearproof-live/bin/near-arena-oracle \
  --generators $R/spec/workloads/near-transfer-receipt-v1 --fixtures $F \
  --cpus 8-15 --work $W/session --out $W/session.json > $W/session.log 2>&1
echo "exit $?"
