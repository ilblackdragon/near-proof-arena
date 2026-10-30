#!/usr/bin/env python3
"""Directed claim mutants for the d2-core claim-structure guards (L0 row validation).

Each mutant changes exactly one field of an honest, nearcore-accepted claim so that one named
`checkD2CoreGWith` guard is the first to fail. The verdict is the claim-v3 discipline, the same
judgement the corpus `c.*` / `t.*` mutants carry (`verdict_source: claim-v3`): the honest claim is
the one cold nearcore produced, so any other claim for that witness is false (`expected_rel:
false`). A mutant whose bytes do not parse as a claim-v3 body is not emitted.

Usage: l0_guard_mutants.py --bases FILE --out DIR [--per-kind N]
The witness and code files are copied unchanged; `meta.json` records the base and the mutation.
"""
import argparse
import json
import shutil
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import claim_schema as cs  # noqa: E402


def u32(n):
    return struct.pack("<I", n)


class Claim:
    """A claim body split into byte segments, so a field can be replaced and the rest re-joined."""

    def __init__(self, data):
        kind, _, _, _, off = cs.header(data)
        if kind != "claim":
            raise ValueError("not a claim")
        self.head = data[:off]
        r = cs.R(data[off:])
        b = r.b
        s = r.i
        r.bytes_("statement_id")
        self.pre = b[s:r.i]
        self.pv = r.u(4, "pv")
        s = r.i
        r.bytes_("chain_id")
        self.epoch_id = None
        self.chain = b[s:r.i]
        self.epoch_id = r.take(32, "epoch_id")
        s = r.i
        r.bytes_("chunk_inner")
        self.inner = b[s:r.i]
        self.blocks = []
        for _ in range(r.u(4, "n_blocks")):
            s = r.i
            r.u(1, "hv"); r.take(32, "prev"); r.bytes_("lite"); r.bytes_("rest")
            hdr = b[s:r.i]
            slots = []
            for _ in range(r.u(4, "slots")):
                s2 = r.i
                r.bytes_("slot inner")
                inner = b[s2:r.i]
                slots.append([inner, r.u(8, "hi")])
            self.blocks.append([hdr, slots])
        self.rs = r.take(4, "rs")
        self.epochs = []
        for _ in range(r.u(4, "epochs")):
            eid = r.take(32, "eid")
            epv = r.u(4, "epv")
            s = r.i
            r.u(8, "eh"); r.bytes_("layout")
            r.vec("v", lambda: (r.bytes_("a"), r.u(16, "s")))
            self.epochs.append([eid, epv, b[s:r.i]])
        self.flags = list(r.vec("esa", lambda: r.u(1, "f")))
        self.facts = []
        for _ in range(r.u(4, "facts")):
            s = r.i
            vu = r.option("vu", lambda: (r.vec("a", lambda: (r.bytes_("a"), r.u(16, "s"))),
                                          r.vec("b", lambda: (r.bytes_("a"), r.u(16, "s"))),
                                          r.option("t", lambda: r.bytes_("t"))))
            s_rest = r.i
            r.u(16, "ms")
            r.option("sg", lambda: (r.u(8, "a"), r.u(8, "b"), r.u(8, "c"),
                                    r.vec("f", lambda: r.u(8, "s")), r.vec("g", lambda: r.u(8, "s"))))
            self.facts.append([b[s:s_rest], b[s_rest:r.i], vu is not None])
        self.txv = list(r.vec("txv", lambda: r.u(1, "f")))
        s = r.i
        r.option("gce", lambda: r.bytes_("gce"))
        self.gce = b[s:r.i]
        r.done("claim")

    def encode(self):
        out = [self.head, self.pre, u32(self.pv), self.chain, self.epoch_id, self.inner,
               u32(len(self.blocks))]
        for hdr, slots in self.blocks:
            out += [hdr, u32(len(slots))]
            for inner, hi in slots:
                out += [inner, struct.pack("<Q", hi)]
        out += [self.rs, u32(len(self.epochs))]
        for eid, epv, rest in self.epochs:
            out += [eid, u32(epv), rest]
        out += [u32(len(self.flags)), bytes(self.flags), u32(len(self.facts))]
        for vu, rest, _ in self.facts:
            out += [vu, rest]
        out += [u32(len(self.txv)), bytes(self.txv), self.gce]
        return b"".join(out)


EMPTY_VU = b"\x01" + u32(0) + u32(0) + b"\x00"


def mutations(c):
    """(row, mutation name, mutate(claim) -> bool applied). Each targets one guard."""
    def pv85(x):
        x.pv = 85
        return True

    def empty(x):
        x.blocks, x.flags = [], []
        return True

    def dup_epoch(x):
        if not x.epochs:
            return False
        x.epochs = x.epochs + [list(x.epochs[-1])]
        return True

    def epoch_pv(x):
        for e in x.epochs:
            if e[0] == x.epoch_id:
                e[1] = 85
                return True
        return False

    def other_epoch_pv(x):
        for e in x.epochs:
            if e[0] != x.epoch_id:
                e[1] = 85
                return True
        return False

    def esa_len(x):
        x.flags = x.flags + [0]
        return True

    def esa_flag(x):
        if not x.flags:
            return False
        x.flags[-1] = 2
        return True

    def reverse(x):
        if len(x.blocks) < 2:
            return False
        x.blocks, x.flags = x.blocks[::-1], x.flags[::-1]
        return True

    def drop_middle(x):
        if len(x.blocks) < 3:
            return False
        del x.blocks[1]
        del x.flags[1]
        return True

    def drop_slot(x):
        if not x.blocks or not x.blocks[0][1]:
            return False
        x.blocks[0][1] = x.blocks[0][1][:-1]
        return True

    def facts_len(x):
        if not x.facts:
            return False
        x.facts = x.facts + [list(x.facts[-1])]
        return True

    def vu_toggle(x):
        if not x.facts:
            return False
        f = x.facts[0]
        if f[2]:
            f[0], f[2] = b"\x00", False
        else:
            f[0], f[2] = EMPTY_VU, True
        return True

    def txv_len(x):
        x.txv = x.txv + [1]
        return True

    def gce_some(x):
        if x.gce != b"\x00":
            return False
        x.gce = b"\x01" + u32(0)
        return True

    return [
        ("L0-D2-005", "l0.c.pv85", pv85),
        ("L0-D2-006", "l0.c.empty_segment", empty),
        ("L0-D2-007", "l0.c.epoch_dup", dup_epoch),
        ("L0-D2-010", "l0.c.epoch_record_pv", epoch_pv),
        ("L0-D2-011", "l0.c.other_epoch_pv85", other_epoch_pv),
        ("L0-D2-016", "l0.c.esa_extra_flag", esa_len),
        ("L0-D2-017", "l0.c.esa_flag2", esa_flag),
        ("L0-D2-021", "l0.c.blocks_reversed", reverse),
        ("L0-D2-022", "l0.c.drop_middle_block", drop_middle),
        ("L0-D2-023", "l0.c.drop_slot", drop_slot),
        ("L0-D2-030", "l0.c.apply_facts_extra", facts_len),
        ("L0-D2-031", "l0.c.validator_update_toggle", vu_toggle),
        ("L0-D2-037", "l0.c.tx_valid_extra", txv_len),
        ("L0-D2-028", "l0.c.genesis_extra_some", gce_some),
    ]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bases", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--per-kind", type=int, default=12)
    a = ap.parse_args()
    bases = [Path(l) for l in a.bases.read_text().splitlines() if l]
    made = {}
    index = []
    for base in bases:
        data = (base / "claim.bin").read_bytes()
        if Claim(data).encode() != data:
            raise SystemExit(f"claim round-trip failed: {base}")
        meta = json.loads((base / "meta.json").read_text())
        if meta.get("expected_rel") is not True:
            continue
        for row, name, f in mutations(None):
            if made.get(name, 0) >= a.per_kind:
                continue
            c = Claim(data)
            if not f(c):
                continue
            enc = c.encode()
            if enc == data:
                continue
            Claim(enc)  # must still parse as a claim body
            d = a.out / f"{base.parent.parent.name}-{base.name}-{name}"
            d.mkdir(parents=True, exist_ok=True)
            (d / "claim.bin").write_bytes(enc)
            for fn in base.iterdir():
                if fn.name not in ("claim.bin", "meta.json") and fn.is_file():
                    shutil.copy(fn, d / fn.name)
            m = dict(meta, kind="mutant", mutation=name, base=str(base), expected_rel=False,
                     expected_rel_d3=False, nearcore="claim-v3 discipline",
                     verdict_source="claim-v3", l0_row=row)
            (d / "meta.json").write_text(json.dumps(m, indent=2, sort_keys=True) + "\n")
            made[name] = made.get(name, 0) + 1
            index.append({"case": str(d), "row": row, "mutation": name, "base": str(base)})
    (a.out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    print(json.dumps(made, indent=1))


if __name__ == "__main__":
    main()
