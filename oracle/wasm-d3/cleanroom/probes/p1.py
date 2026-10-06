from probe import *
cases = []
def mk(imp_name="value_return", main=True):
    m = base_module()
    m.import_func("env", imp_name, [I64,I64], [])
    m.func([], [], [], b"")
    if main: m.exports.append(("main", 0, len(m.imports)))
    return m.encode().hex()
for g in [0, 1000, 10**8, 10**9]:
    cases.append((f"unknown-import gas={g}", f"{g} {mk('nope')}"))
    cases.append((f"no-main gas={g}", f"{g} {mk(main=False)}"))
    cases.append((f"unknown+no-main gas={g}", f"{g} {mk('nope', main=False)}"))
    cases.append((f"plain gas={g}", f"{g} {mk()}"))
show(cases)
print(len(bytes.fromhex(mk())), 1089295*len(bytes.fromhex(mk()))+35445963)
