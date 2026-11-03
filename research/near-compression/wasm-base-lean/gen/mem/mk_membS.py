import re, sys
ROOT = sys.argv[1]
def rd(p): return open(ROOT + '/' + p).read()

bytes_src = rd('WasmBase/Main/SegShaBytes.lean')
a = bytes_src.index('/-- Every BYTE receive is a byte pair. -/')
b = bytes_src.index('end\nend SegSha', a)
bytes_part = bytes_src[a:b]

memb_src = rd('WasmBase/Main/SegShaMemb.lean')
a = memb_src.index('section rows')
b = memb_src.index('end rows') + len('end rows')
memb_part = memb_src[a:b]

memb_part = memb_part.replace('variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)\ninclude H\n', '')
body = bytes_part + '\n' + memb_part
# hypotheses
body = body.replace('(H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)', '(H : HoldsXS nloc ngl pub tr)')
body = body.replace('ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip', 'ChipIfS compressW nloc ngl pub tr chip')
# declared names in the copied text -> S
declared = re.findall(r'^theorem ([A-Za-z_][A-Za-z0-9_\']*)', body, re.M)
ext = ['memb_pos', 'memb_onehot', 'memb_C', 'memb_row', 'memb_kD_le', 'byte_bitsX', 'seg_hsend_byte',
       'memb_blk_const', 'table_constrX', 'lookup_soundX', 'comp_in_chip', 'memb_p_bit', 'seg_r16_lt', 'seg_hsend_r16']
names = set(declared) | set(ext)
def ren(m):
    n = m.group(0)
    return n + 'S' if n in names else n
body = re.sub(r'(?<![A-Za-z0-9_.\'])([A-Za-z_][A-Za-z0-9_\']*)(?![A-Za-z0-9_\'])', ren, body)
body = body.replace('comp_in_chipS H hC ht hr', 'comp_in_chipS H hC ht (by decide) hr')
hdr = '''import WasmBase.Main.SegS.SegShaBytes
import WasmBase.Main.SegS.SegSend
import WasmBase.Main.SegS.SegMemb
import WasmBase.Main.SegShaMemb
import WasmBase.Main.SegShaMpath

/-!
# WasmBase.Main.SegMembS — MEMB's leaf lemmas from `HoldsXS` (E2E M4c, sub-lane MEM, for the multiproof AIR)

Copies of `Main/SegShaMemb.lean`'s row lemmas (`memb_leaf_in`, `memb_leaf_out`, …) and of
`Main/SegShaBytes.lean`'s `seg_byte_lt`, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS`
(`Main/SegHoldsS.lean`) and `ChipIf` by `ChipIfS`, every name `foo` renamed `fooS`.  MEMB uses neither
table 20 nor the buses 15/16/17, so the proofs are the originals'; both segment AIRs give `HoldsXS`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local StateM5a.Sha512If
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-- `comp_in_chip` from `HoldsXS`/`ChipIfS` (tables `≠ 20`). -/
theorem comp_in_chipS {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (_H : HoldsXS nloc ngl pub tr) (hC : ChipIfS compress nloc ngl pub tr chip)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) (h20 : t ≠ 20) {r : Nat} (hr : r < tr.height t)
    {cidE cnt : Expr} {ws : List W3} (hsub : ∀ i ∈ comp cidE ws cnt, i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hcnt : (cnt.eval (tr.row pub t r)).toNat = 1) :
    ∀ m, m < 16 → (cidE.eval (tr.row pub t r) :: ((m : Nat) : F) ::
      ((ws.getD (2 * m) zeroW).map (·.eval (tr.row pub t r)) ++ (ws.getD (2 * m + 1) zeroW).map (·.eval (tr.row pub t r))))
        ∈ chip.map ifF := by
  intro m hm
  have hi := hsub _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)
  have := if_recv_memS hC ht h20 hr hi rfl hcnt
  simpa [comp, List.map_append] using this

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

'''
out = hdr + body.replace('section rows', '').replace('end rows', '') + '\nend\n\nend SegSha\n\n'
for n in declared:
    out += f'#print axioms SegSha.{n}S\n'
out += '\nend WasmBase\n'
open(ROOT + '/WasmBase/Main/SegMembS.lean', 'w').write(out)
print(declared)
