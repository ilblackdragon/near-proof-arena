import re, sys
ROOT = sys.argv[1]
src = open(ROOT + '/WasmBase/Main/SegMemRoot.lean').read()

def chunk(start, end):
    a = src.index(start)
    b = src.index(end, a)
    return src[a:b]

parts = [
    chunk('theorem memb_act_of_p', '/-- **An active padding row\'s leaf message reaches'),
    chunk('/-- A read-only block\'s leaf message has new = old', 'end memb'),
    chunk('/-- A read-only block\'s out bytes are its in bytes', '/-- **Item 3'),
    chunk('/-- The bytes of a touched block `b`: the leaf', '/-- **Item 1'),
]
body = '\n'.join(parts)
body = body.replace('{chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)',
                    '{chip : List IfMsg} (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip)')
declared = re.findall(r'^theorem ([A-Za-z_][A-Za-z0-9_\']*)', body, re.M)
for q in ['memb_kDkP', 'memb_bi_lt', 'memb_ro_const', 'memb_leaf_in', 'memb_leaf_out']:
    body = body.replace('SegSha.' + q + ' ', 'SegSha.' + q + 'S ')
ext = ['memb_pos', 'memb_onehot', 'memb_C', 'memb_row', 'memb_blk_const', 'seg_r16_lt', 'seg_hsend_r16',
       'memb_p_bit']
names = set(declared) | set(ext)
def ren(m):
    n = m.group(0)
    if n.endswith("'") and n[:-1] in names:
        return n[:-1] + "S'"
    return n + 'S' if n in names else n
body = re.sub(r'(?<![A-Za-z0-9_.\'])([A-Za-z_][A-Za-z0-9_\']*)(?![A-Za-z0-9_])', ren, body)
hdr = '''import WasmBase.Main.SegMembS
import WasmBase.Main.SegMemRoot

/-!
# WasmBase.Main.SegMemMembS — MEMB-side lemmas of `SegMemRoot` from `HoldsXS` (E2E M4c, MEM)

Copies of `Main/SegMemRoot.lean`'s MEMB-only row lemmas (`memb_prod_form`, `memb_cons_mem`,
`memb_blk_lt`, `memb_ro_leaf`, `memb_ro_bytes`, `leaf_in_bytes`, …) with `HoldsX (wasmBaseSegAir …)`
replaced by `HoldsXS` and `ChipIf` by `ChipIfS` (`foo` ↦ `fooS`), so that they serve the multiproof
AIR (`HoldsX.toSMP`).  MEMB uses neither table 20 nor the buses 15/16/17.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.Wasm hiding P
open NearSpecV3.E2E.Bnd (Sha384Coll sha384 sha384_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace MemRoot

section membS
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

'''
out = hdr + body + '\nend membS\n\nend MemRoot\n\n'
for n in declared:
    out += f'#print axioms MemRoot.{n}S\n'
out += '\nend WasmBase\n'
open(ROOT + '/WasmBase/Main/SegMemMembS.lean', 'w').write(out)
print(declared)
