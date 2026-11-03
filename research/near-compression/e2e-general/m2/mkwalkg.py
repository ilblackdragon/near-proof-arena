import re
# E2E M2: generate WasmBase/Main/RegWalkG.lean (the REG group walk for any AIR carrying REG's
# constraints) from WasmBase/Main/RegWalk.lean.  Run from anywhere: python3 mkwalkg.py
import os
W = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../wasm-base-lean/WasmBase/Main/')
src = open(W + 'RegWalk.lean').read()

# split header (imports + docstring) from body
i = src.index('namespace WasmBase')
body = src[i:]

names = re.findall(r'^theorem (\w+)', body, re.M)
names = [n for n in names if n != 'reg_walk_26']

# drop reg_walk_constraints / reg_walk_26 definitions (replaced by regG_cons / RegAt)
def drop_thm(b, name):
    j = b.index('theorem ' + name)
    # start at preceding doc comment if any
    k = b.rfind('/--', 0, j)
    if k != -1 and b[k:j].count('-/') == 1 and b[b.index('-/', k) + 2:j].strip() == '':
        j0 = k
    else:
        j0 = j
    e = b.index('\ntheorem ', j + 1)
    e2 = b.rfind('/--', j, e)
    if e2 != -1:
        e = e2
    return b[:j0] + b[e:]

body = drop_thm(body, 'reg_walk_constraints')
body = drop_thm(body, 'reg_walk_26')
names = [n for n in names if n != 'reg_walk_constraints']

body = body.replace('''  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
''', '''  have hcon := regG_cons hA H hr
''')
body = body.replace('(H : Holds (wasmBaseRegAir nloc ngl) pub tr)', '(hA : RegAt A ti) (H : Holds A pub tr)')
body = body.replace('{nloc ngl : Nat}', '{A : Air} {ti : Nat}')
body = body.replace('occs (wasmBaseRegAir nloc ngl)', 'occs A')
body = body.replace('(wasmBaseRegAir nloc ngl).tables', 'A.tables')
body = body.replace('reg_recv_only_range16 nloc ngl', 'hA.r16only')
body = body.replace('(reg_walk_26 (nloc := nloc) (ngl := ngl)).1', 'hA.lt')
body = body.replace('reg_row_constraints H hr', 'regG_cons hA H hr')
body = body.replace('reg_r16_query_16bit H', 'lookup_r16G H')
# rename the file's theorems and pass hA on every `name H` call
for n in sorted(names, key=len, reverse=True):
    g = 'regG' + n[3:] if n.startswith('reg_') else n + 'G'
    body = re.sub(r'\b' + n + r'\b', g, body)
for n in names:
    g = 'regG' + n[3:] if n.startswith('reg_') else n + 'G'
    body = re.sub(r'\b' + g + r' H\b', g + ' hA H', body)
# table index 26 -> ti
body = re.sub(r'(tr\.height|rowNat tr|tr\.row pub|cell_cast tr|rowProd Reg\.table tr pub|rowCons Reg\.table tr pub|H\.heightLe) 26\b', r'\1 ti', body)
body = body.replace('⟨26, hA.lt', '⟨ti, hA.lt')
body = body.replace('H.heightLe ti ht\n', 'H.heightLe ti hA.lt\n')
body = re.sub(r'(rowNat_lt tr|tr\.cell) 26\b', r'\1 ti', body)
body = re.sub(r'have (\w+) := table_constr H ht (\w+)\n(\s*)rw \[hT\] at \1\n', r'have \1 := regG_cons hA H \2\n', body)
body = re.sub(r'\n\s*have hT := \(reg_walk_26 \(nloc := nloc\) \(ngl := ngl\)\)\.2', '', body)
body = body.replace('· rw [hT]; exact hmem', '· exact hA.inters _ hmem')
body = re.sub(r'(rowMsgs Reg\.table tr pub) 26\b', r'\1 ti', body)
for n in ['regG_byte_msg', 'regG_len_msg', 'regG_byte_row_msg', 'regG_len_row_msg']:
    body = body.replace('theorem %s {tr : Trace} {pub : List F} {r : Nat}' % n,
                        'theorem %s {ti : Nat} {tr : Trace} {pub : List F} {r : Nat}' % n)
for n in ['regG_byteslot_eval', 'regG_lenslot_eval']:
    body = body.replace('theorem %s (tr : Trace) (pub : List F) (r : Nat)' % n,
                        'theorem %s (ti : Nat) (tr : Trace) (pub : List F) (r : Nat)' % n)
    body = body.replace('%s tr pub r' % n, '%s ti tr pub r' % n)

header = '''import WasmBase.Main.RegWalk
import WasmBase.M2Air
/-!
# WasmBase.Main.RegWalkG — the REG group walk for **any** AIR carrying REG's constraints

`Main/RegWalk.lean` proves the walk for `wasmBaseRegAir`, whose REG is table 26.  The E2E AIRs
`wasmBaseIfRegAir` and `wasmBaseM2Air` carry REG' (`Chips.RegW`) at index 27: REG's constraints and
interactions as a prefix plus the memory-write link.  This file is `RegWalk.lean` generalised to an
arbitrary AIR `A` and table index `ti` with `RegAt A ti`:

* table `ti` contains every REG constraint and every REG interaction;
* every table but RANGE16 only *sends* on R16 (so an R16 receive is a RANGE16 answer).

The proofs are RegWalk's, with `table_constr … ; rw [reg_air_26]` replaced by `regG_cons`.  The
instances `regAt_ifreg` and `regAt_m2` put the walk, `Register.RegLenAgree` for a group and the
gap/`pos < len` bounds on `Holds (wasmBaseIfRegAir …)` and `Holds (wasmBaseM2Air …)` at index 27.
(Generated from `RegWalk.lean` mechanically; see `research/near-compression/e2e-general/m2/README.md`.)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- What the walk needs of table `ti` of `A`. -/
structure RegAt (A : Air) (ti : Nat) : Prop where
  lt : ti < A.tables.length
  cons : ∀ e ∈ Reg.table.constraints, e ∈ (A.tables[ti]'lt).constraints
  inters : ∀ i ∈ Reg.table.inters, i ∈ (A.tables[ti]'lt).inters
  r16only : ∀ T ∈ A.tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 → i.send = true

/-- REG's constraints vanish on every row of table `ti`. -/
theorem regG_cons {A : Air} {ti : Nat} {pub : List F} {tr : Trace} (hA : RegAt A ti)
    (H : Holds A pub tr) {r : Nat} (hr : r < tr.height ti) :
    ∀ e ∈ Reg.table.constraints, e.eval (natRow (rowNat tr ti r) (tr.row pub ti r)) = 0 :=
  fun e he => table_constr H hA.lt hr e (hA.cons e he)

/-- R16 lookup soundness, as RegWalk uses it. -/
theorem lookup_r16G {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr)
    (hsend : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    (hrecv : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_sound H busR16 (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) hrecv
    (fun o' ho' hb' hs' => hsend o' ho' hb' hs') ho hb hs hc

'''
body = body.replace('namespace WasmBase\nopen ZkFormal.Algebra Chips Local\nopen NearSpecV3.Wasm hiding P\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 4000\n', '', 1)
footer = '''
/-! ## The instances: REG' at index 27 of the E2E AIRs -/

namespace WasmBase
open ZkFormal.Algebra Chips

theorem hostR_table_r16 : HostR.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem ifc_table_r16 : IfC.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem regw_table_r16 : RegW.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem conv_table_r16 : Conv.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem regc_table_r16 : RegC.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem unreach_table_r16 : Unreach.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide

/-- Every table of `wasmBaseIfRegAir` except RANGE16 only sends on R16. -/
theorem ifreg_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseIfRegAir nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 →
      i.send = true := by
  intro T hT hne i hi hb
  have hsplit : (wasmBaseIfRegAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
        RegW.table] := rfl
  rw [hsplit, List.mem_append] at hT
  rcases hT with h | h
  · exact base_recv_only_r16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_r16_of_all hostR_table_r16 i hi hb
    · exact table_r16_of_all hostO_table_r16 i hi hb
    · exact table_r16_of_all hostTab_table_r16 i hi hb
    · exact table_r16_of_all hostB_table_r16 i hi hb
    · exact table_r16_of_all ifc_table_r16 i hi hb
    · exact table_r16_of_all regw_table_r16 i hi hb

/-- Every table of `wasmBaseM2Air` except RANGE16 only sends on R16. -/
theorem m2_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseM2Air nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 →
      i.send = true := by
  intro T hT hne i hi hb
  have hsplit : (wasmBaseM2Air nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
        RegC.table, Conv.table, Unreach.table] := rfl
  rw [hsplit, List.mem_append] at hT
  rcases hT with h | h
  · exact base_recv_only_r16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_r16_of_all hostR_table_r16 i hi hb
    · exact table_r16_of_all hostO_table_r16 i hi hb
    · exact table_r16_of_all hostTab_table_r16 i hi hb
    · exact table_r16_of_all hostB_table_r16 i hi hb
    · exact table_r16_of_all ifc_table_r16 i hi hb
    · exact table_r16_of_all regc_table_r16 i hi hb
    · exact table_r16_of_all conv_table_r16 i hi hb
    · exact table_r16_of_all unreach_table_r16 i hi hb

/-- **REG' at index 27 of `wasmBaseIfRegAir` satisfies the walk's interface.** -/
theorem regAt_ifreg (nloc ngl : Nat) : RegAt (wasmBaseIfRegAir nloc ngl) 27 where
  lt := by rw [ifreg_air_len]; decide
  cons := fun e he => by
    rw [ifreg_air_27]; exact List.mem_append_left _ he
  inters := fun i hi => by
    rw [ifreg_air_27]; exact List.mem_append_left _ hi
  r16only := ifreg_recv_only_range16 nloc ngl

/-- **REG' at index 27 of `wasmBaseM2Air` satisfies the walk's interface.** -/
theorem regAt_m2 (nloc ngl : Nat) : RegAt (wasmBaseM2Air nloc ngl) 27 where
  lt := by rw [m2_air_len]; decide
  cons := fun e he => by
    rw [m2_air_27]; exact List.mem_append_left _ (List.mem_append_left _ he)
  inters := fun i hi => by
    rw [m2_air_27]; exact List.mem_append_left _ (List.mem_append_left _ hi)
  r16only := m2_recv_only_range16 nloc ngl

end WasmBase
'''
open(W + 'RegWalkG.lean', 'w').write(header + body + footer)
print(len(names), 'theorems')
