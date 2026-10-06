//! The D3 contracts (`contracts/*.wat`, compiled with `wasm-tools parse` into the committed
//! `contracts/*.wasm`; `ttn2` is oracle/d3-ttn's storage/promise contract, reused unchanged),
//! the code registry (code hash → bytes: every contract the D3 chains deploy, in genesis or at
//! run time, plus the D2 contracts), and the D3α contract predicate.

use near_primitives::hash::CryptoHash;
use std::collections::BTreeMap;
use std::sync::OnceLock;

pub const RICH: &[u8] = include_bytes!("../contracts/d3rich.wasm");
pub const TINY: &[u8] = include_bytes!("../contracts/d3tiny.wasm");
pub const FLOAT: &[u8] = include_bytes!("../contracts/d3float.wasm");
pub const CURVE: &[u8] = include_bytes!("../contracts/d3curve.wasm");
pub const ED: &[u8] = include_bytes!("../contracts/d3ed.wasm");
pub const TTN2: &[u8] = include_bytes!("../../d3-ttn/ttn2.wasm");

/// (name, code) of every contract a D3 chain can execute.
pub fn all() -> Vec<(&'static str, Vec<u8>)> {
    let mut v: Vec<(&'static str, Vec<u8>)> = vec![
        ("d3rich", RICH.to_vec()),
        ("d3tiny", TINY.to_vec()),
        ("d3float", FLOAT.to_vec()),
        ("d3curve", CURVE.to_vec()),
        ("d3ed", ED.to_vec()),
        ("ttn2", TTN2.to_vec()),
        ("d2program", crate::d2gen::program_wasm().to_vec()),
    ];
    for i in [0usize, 1, 3] {
        v.push((["d2small0", "d2small1", "", "d2small3"][i], crate::d2gen::small_wasm(i)));
    }
    v
}

pub struct Registry {
    pub by_hash: BTreeMap<CryptoHash, (&'static str, Vec<u8>)>,
}

pub fn registry() -> &'static Registry {
    static R: OnceLock<Registry> = OnceLock::new();
    R.get_or_init(|| Registry {
        by_hash: all().into_iter().map(|(n, c)| (CryptoHash::hash_bytes(&c), (n, c))).collect(),
    })
}

/// D3α facts of one contract (docs/requirements/D3_WASM_REQUIREMENTS.md §1.1,
/// spec/lean/v3/NearSpecV3/Wasm/DomainD3.lean `contractInD3α`).
#[derive(Clone, Debug, Default)]
pub struct CodeFacts {
    /// a float value type (function type, local, global, block / select type) or opcode
    pub float: bool,
    /// imports one of the Lean spec's `curveHosts` (Exec.lean)
    pub curve_imports: Vec<String>,
    /// imports `ed25519_verify` (modelled by the Lean spec; D3γ in the requirements table)
    pub ed25519_import: bool,
    pub chain_id_import: bool,
    /// wasmparser could not parse it (preparation fails in nearcore: an in-domain failure)
    pub parse_error: bool,
    pub imports: Vec<String>,
}

/// `curveHosts`, spec/lean/v3/NearSpecV3/Wasm/Exec.lean (ed25519_verify is not in it).
pub const CURVE_HOSTS: &[&str] = &[
    "alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check", "bls12381_p1_sum", "bls12381_p2_sum",
    "bls12381_g1_multiexp", "bls12381_g2_multiexp", "bls12381_map_fp_to_g1", "bls12381_map_fp2_to_g2",
    "bls12381_pairing_check", "bls12381_p1_decompress", "bls12381_p2_decompress", "ecrecover", "p256_verify",
];

pub fn code_facts(code: &[u8]) -> CodeFacts {
    let mut f = CodeFacts::default();
    if scan(code, &mut f).is_err() {
        f.parse_error = true;
    }
    f
}

fn scan(code: &[u8], f: &mut CodeFacts) -> Result<(), wasmparser::BinaryReaderError> {
    use wasmparser::{CompositeInnerType, Payload, TypeRef, ValType};
    let fl = |t: &ValType| matches!(t, ValType::F32 | ValType::F64);
    for p in wasmparser::Parser::new(0).parse_all(code) {
        match p? {
            Payload::TypeSection(r) => {
                for rg in r {
                    for st in rg?.into_types() {
                        if let CompositeInnerType::Func(ft) = &st.composite_type.inner {
                            if ft.params().iter().chain(ft.results()).any(fl) {
                                f.float = true;
                            }
                        }
                    }
                }
            }
            Payload::ImportSection(r) => {
                for i in r {
                    let i = i?;
                    if let TypeRef::Global(g) = i.ty {
                        if fl(&g.content_type) {
                            f.float = true;
                        }
                    }
                    if CURVE_HOSTS.contains(&i.name) {
                        f.curve_imports.push(i.name.to_string());
                    }
                    if i.name == "ed25519_verify" {
                        f.ed25519_import = true;
                    }
                    if i.name == "chain_id" {
                        f.chain_id_import = true;
                    }
                    f.imports.push(i.name.to_string());
                }
            }
            Payload::GlobalSection(r) => {
                for g in r {
                    if fl(&g?.ty.content_type) {
                        f.float = true;
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                for l in body.get_locals_reader()? {
                    if fl(&l?.1) {
                        f.float = true;
                    }
                }
                let mut ops = body.get_operators_reader()?;
                while !ops.eof() {
                    let op = format!("{:?}", ops.read()?);
                    // every float opcode's name, typed select / block types and conversions
                    // mention F32 or F64 (F32Add, I64TruncF64U, Block { blockty: Type(F64) }, …)
                    if op.contains("F32") || op.contains("F64") {
                        f.float = true;
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}
