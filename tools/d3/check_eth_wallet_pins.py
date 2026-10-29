#!/usr/bin/env python3
"""UQ-007: the ETH-wallet hashes the Lean resolution enumerates, recomputed from pinned nearcore.

`RuntimeContractIdentifier::resolve` (`runtime/runtime/src/contract_code.rs:56-76`) treats an
ETH-implicit account whose *local* code hash is one of the four `LegacyEthWallet` magic hashes
(`runtime/near-wallet-contract/src/lib.rs:37-52`) as a wallet. At PV86
`eth_implicit_global_contract = true` (`83.yaml:4`, checked by `check_pv86_param_pins.py`), so it
resolves to `Global { eth_wallet_global_contract_hash(chain_id) }` (`lib.rs:87-104`) and the
`LegacyEthWallet` variant is never constructed (Lean: `legacyWallet_unreachable_pv86`,
`ethWallet_kind_unreachable`).

This script recomputes, from the wasm blobs nearcore embeds:
* each magic hash `sha256("near" ‖ base58(sha256(wasm)))` (`lib.rs:143-155`) and checks it against
  `walletMagicHash` (`spec/lean/v3/NearSpecV3/D3/GlobalContract.lean`), and that the four are
  distinct (so `resolve`'s order is immaterial);
* the global wallet hash per chain (`lib.rs:87-104`: hard-coded for mainnet/mocknet and testnet,
  `sha256(localnet wasm)` otherwise) and checks it against `ethWalletHash`
  (`spec/lean/v3/NearSpecV3/D2/Actions.lean`).

`--break` flips one byte of one Lean value in memory; the check must then fail.
"""
import argparse
import hashlib
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
NEARCORE = Path("/data/illia/nearproof-deps/nearcore")
WALLET = "runtime/near-wallet-contract"
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
WASM = {"mainnet": "wallet_contract_mainnet.wasm", "testnet": "wallet_contract_testnet.wasm",
        "oldTestnet": "wallet_contract_testnet_pv70.wasm", "localnet": "wallet_contract_localnet.wasm"}


def b58(bs):
    n = int.from_bytes(bs, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    return "1" * (len(bs) - len(bs.lstrip(b"\0"))) + out


def byte_list(text):
    return bytes(int(x, 16) for x in re.findall(r"0x([0-9a-fA-F]{2})", text))


def lean_magic():
    src = (REPO / "spec/lean/v3/NearSpecV3/D3/GlobalContract.lean").read_text()
    body = src[src.index("def walletMagicHash : Wallet → Bytes"):src.index("def resolveWallet")]
    out = {}
    for name in WASM:
        m = re.search(rf"\| \.{name} =>\s*\[([^\]]*)\]", body)
        out[name] = byte_list(m.group(1))
    return out


def lean_global():
    src = (REPO / "spec/lean/v3/NearSpecV3/D2/Actions.lean").read_text()
    body = src[src.index("def ethWalletHash"):src.index("def initialNonce")]
    lists = re.findall(r"\[(0x[^\]]*)\]", body)
    assert len(lists) == 3, len(lists)
    return {"mainnet": byte_list(lists[0]), "testnet": byte_list(lists[1]),
            "localnet": byte_list(lists[2])}


def nearcore_global(lib):
    body = lib[lib.index("pub fn eth_wallet_global_contract_hash"):]
    body = body[:body.index("pub fn code_hash_matches_wallet_contract")]
    arrays = re.findall(r"CryptoHash\(\[([^\]]*)\]\)", body)
    assert len(arrays) == 2 and "chains::MAINNET | chains::MOCKNET" in body
    assert "_ => *LOCALNET.read_contract().hash()" in body
    return byte_list(arrays[0]), byte_list(arrays[1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nearcore", default=str(NEARCORE))
    ap.add_argument("--break", dest="brk", choices=["magic", "global"])
    a = ap.parse_args()
    nc = Path(a.nearcore) / WALLET
    lib = (nc / "src/lib.rs").read_text()
    for name, f in WASM.items():
        assert f in lib, f
    code = {k: (nc / "res" / f).read_bytes() for k, f in WASM.items()}
    magic = {k: hashlib.sha256(b"near" + b58(hashlib.sha256(c).digest()).encode()).digest()
             for k, c in code.items()}
    lm, lg = lean_magic(), lean_global()
    if a.brk == "magic":
        lm["oldTestnet"] = bytes([lm["oldTestnet"][0] ^ 1]) + lm["oldTestnet"][1:]
    if a.brk == "global":
        lg["localnet"] = bytes([lg["localnet"][0] ^ 1]) + lg["localnet"][1:]
    main_g, test_g = nearcore_global(lib)
    want_g = {"mainnet": main_g, "testnet": test_g,
              "localnet": hashlib.sha256(code["localnet"]).digest()}
    rows = [(f"magic {k}", magic[k], lm[k]) for k in WASM]
    rows += [(f"global {k}", want_g[k], lg[k]) for k in want_g]
    bad = 0
    for label, want, got in rows:
        ok = want == got
        bad += not ok
        print(f"{'ok ' if ok else 'BAD'} {label:18s} nearcore={want.hex()} lean={got.hex()}")
    distinct = len(set(magic.values())) == 4 and not set(magic.values()) & set(want_g.values())
    print(f"{'ok ' if distinct else 'BAD'} four magic hashes distinct and disjoint from the global hashes")
    print(f"{len(rows) - bad}/{len(rows)} wallet hashes agree")
    return 0 if bad == 0 and distinct else 1


if __name__ == "__main__":
    sys.exit(main())
