#!/bin/bash
# judge-built NEAR verifier on honest / false / mutated proofs.
S=/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad
V=${V:-$S/m5/work/verify}; P=${P:-$S/pkgbuild/b1/pkg/out/prove}; PREP=${PREP:-$S/pkgbuild/b1/pkg/out/prepare}
W=$S/m5test; rm -rf $W; mkdir -p $W/pub
F=/data/illia/nearproof-wt/zk-L7/oracle/fixtures/public
$PREP --params $F/params.bin --out $W/pub || { echo prepare failed; exit 1; }
sha256sum $V | cut -c1-16
printf "case\tn\tprove_s\tproof_B\tclaim\tverify\tverify_ms\tfalse_claim\tmut_proof\ttrunc\n"
run() {
  local d=$1 c=$2
  local t0=$(date +%s%N)
  RAYON_NUM_THREADS=8 $P --public $W/pub --request $d/request.bin --witness $d/witness.bin --claim-out $W/c.bin --proof-out $W/p.bin 2>$W/err >/dev/null
  local rc=$? t1=$(date +%s%N)
  if [ $rc -ne 0 ]; then printf "%s\tPROVE_FAIL(%s)\n" "$c" "$(tail -1 $W/err)"; return; fi
  local cl=$(cmp -s $W/c.bin $d/expected_claim.bin && echo ok || echo DIFF)
  mkdir -p $W/keep; cp $W/c.bin $W/keep/$c.c; cp $W/p.bin $W/keep/$c.p; echo $c >> $W/keep/list
  local t2=$(date +%s%N); $V --public $W/pub --claim $W/c.bin --proof $W/p.bin >/dev/null 2>&1; local vr=$?; local t3=$(date +%s%N)
  # false claim: flip one byte in the last 32 bytes (outputs/commitments) of the claim
  python3 - $W/c.bin $W/cf.bin <<'PY'
import sys; b=bytearray(open(sys.argv[1],'rb').read()); b[len(b)-5]^=1; open(sys.argv[2],'wb').write(b)
PY
  $V --public $W/pub --claim $W/cf.bin --proof $W/p.bin >/dev/null 2>&1; local fr=$?
  python3 - $W/p.bin $W/pm.bin <<'PY'
import sys,random; b=bytearray(open(sys.argv[1],'rb').read()); random.seed(len(b)); i=random.randrange(len(b)); b[i]^=1<<random.randrange(8); open(sys.argv[2],'wb').write(b)
PY
  $V --public $W/pub --claim $W/c.bin --proof $W/pm.bin >/dev/null 2>&1; local mr=$?
  head -c $(( $(stat -c%s $W/p.bin) - 1 )) $W/p.bin > $W/pt.bin
  $V --public $W/pub --claim $W/c.bin --proof $W/pt.bin >/dev/null 2>&1; local tr=$?
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$c" "-" "$(( (t1-t0)/1000000 ))ms" "$(stat -c%s $W/p.bin)" "$cl" "$vr" "$(( (t3-t2)/1000000 ))" "$fr" "$mr" "$tr"
}
for d in $F/cases/*/; do run $d $(basename $d); done
for r in 1 16 256; do for d in $S/m5cases/batch-$r/cases/*/; do run $d "r$r-$(basename $d)"; done; done

# swapped pairs: claim of case i with the proof of case i+1 (valid canonical claims, wrong proof)
mapfile -t L < $W/keep/list; n=${#L[@]}; acc=0; rej=0
for ((i=0;i<n;i++)); do a=${L[$i]}; b=${L[$(( (i+1)%n ))]}
  $V --public $W/pub --claim $W/keep/$a.c --proof $W/keep/$b.p >/dev/null 2>&1 && acc=$((acc+1)) || rej=$((rej+1)); done
echo "swapped pairs: $n tested, $rej rejected, $acc accepted"
