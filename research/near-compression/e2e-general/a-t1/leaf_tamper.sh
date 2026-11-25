#!/usr/bin/env bash
# A-T1 item 3: tampers of saved template leaves (segleafverify must refuse each).
#   leaf_tamper.sh <leaf_work_dir>       (the run_leaf.sh work dir; its leaf/ is copied, never changed)
set -uo pipefail
. "${LANEA_ENV:-/data/illia/nearproof-deps/e2e-laneA/at1/env.sh}"
BS=${WB_STACK:-/data/illia/nearproof-deps/e2e-laneA/at1/target-stack/release/nearproof-wasm-base}
WD=${1:?}; cd "$WD"
N=$(ls leaf/seg-*.proof | wc -l)
rej=0; acc=0
try() {  # name, mutation (python on dir X)
  rm -rf X; cp -r leaf X
  python3 -c "$2"
  if $BS segleafverify airSeg.json X "$N" > /dev/null 2>&1; then echo "ACCEPTED $1"; acc=$((acc+1)); else echo "REJECTED $1"; rej=$((rej+1)); fi
}
try "proof 0 byte flipped (middle)" "
b=bytearray(open('X/seg-0.proof','rb').read()); b[len(b)//2]^=1; open('X/seg-0.proof','wb').write(b)"
try "proof 1 truncated by one byte" "
b=open('X/seg-1.proof','rb').read(); open('X/seg-1.proof','wb').write(b[:-1])"
try "proofs swapped (seg-0 <-> seg-1, public files kept)" "
import os; os.rename('X/seg-0.proof','X/t'); os.rename('X/seg-1.proof','X/seg-0.proof'); os.rename('X/t','X/seg-1.proof')"
for idx in 11 12 13 31 67 85 8; do
try "seg-1 public value [$idx] + 1 (proof unchanged)" "
import json; p=json.load(open('X/seg-1.pubs.json')); p['pubs'][$idx]+=1; json.dump(p,open('X/seg-1.pubs.json','w'))"
done
try "vk: one WHIR query fewer in round 0" "
import json; v=json.load(open('X/SEG.vk.json'))
def walk(o):
    if isinstance(o,dict):
        for k,x in o.items():
            if k=='num_queries' and isinstance(x,int): o[k]=x-1; return True
            if walk(x): return True
    if isinstance(o,list):
        for x in o:
            if walk(x): return True
    return False
assert walk(v); json.dump(v,open('X/SEG.vk.json','w'))"
# A-T2 (pinned tight heights): a proof of the same segment under the same vk at the natural tight
# heights (the A-T1 leaf, OLD_LEAF=<its leaf dir>) and a template whose pinned heights differ
if [ -n "${OLD_LEAF:-}" ]; then
try "seg-0 = the same segment proved at its natural tight heights (same vk, A-T1 leaf)" "
import shutil; shutil.copy('$OLD_LEAF/seg-0.proof','X/seg-0.proof')"
try "seg-1 = the same segment proved at its natural tight heights (same vk, A-T1 leaf)" "
import shutil; shutil.copy('$OLD_LEAF/seg-1.proof','X/seg-1.proof')"
fi
try "manifest: template SHA512 height 8192 -> 4096 (pinned heights changed)" "
import json; m=json.load(open('X/manifest.json')); m['template']['heights']['SHA512']//=2; json.dump(m,open('X/manifest.json','w'))"
rm -rf X
echo "LEAF_TAMPER rejected $rej accepted $acc"
