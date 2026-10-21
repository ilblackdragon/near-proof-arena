"""Generate a standalone Cargo root against one verified dependency tree (no shared-tree edits)."""
from pathlib import Path
import json, sys
here = Path(__file__).resolve().parent
deps = Path(sys.argv[1]).resolve()
q = lambda p: json.dumps(str(p))
text = '''[package]
name = "nearproof-chunk-e2e"
version = "0.1.0"
edition = "2024"
[workspace]
[features]
default = ["chunk-recursion"]
chunk-recursion = []
[[bin]]
name = "nearproof-chunk-e2e"
path = ''' + q(here / 'src/main.rs') + '''
[dependencies]
p3-field = "=0.4.3"
p3-matrix = "=0.4.3"
p3-air = "=0.4.3"
sha2 = "0.10.9"
serde = { version = "1", features = ["derive"] }
serde_json = "1"
tempfile = "3"
'''
for name, directory, features in [
    ('openvm-recursion-circuit', 'openvm-sha384/crates/recursion', '["parallel"]'),
    ('openvm-stark-backend', 'stark-backend-unified/crates/stark-backend', '["parallel", "test-utils"]'),
    ('openvm-cpu-backend', 'stark-backend-unified/crates/cpu-backend', '["parallel"]'),
]:
    text += f'{name} = {{ path = {q(deps / directory)}, default-features = false, features = {features} }}\n'
text += '\n[patch."https://github.com/openvm-org/stark-backend.git"]\n'
for name in ['stark-backend','stark-sdk','cpu-backend','cuda-backend','cuda-builder','cuda-common']:
    text += f'openvm-{name} = {{ path = {q(deps / "stark-backend-unified/crates" / name)} }}\n'
text += '\n[patch.crates-io]\n'
for name in ['p3-baby-bear','p3-monty-31']:
    text += f'{name} = {{ path = {q(deps / "plonky3-ext12" / name)} }}\n'
text += '\n[profile.release]\ndebug = false\n'
root = deps / 'chunk-driver'
root.mkdir(exist_ok=True)
(root / 'Cargo.toml').write_text(text)
(root / 'Cargo.lock').write_bytes((here / 'Cargo.lock').read_bytes())
print(root / 'Cargo.toml')
