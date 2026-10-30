#!/usr/bin/env python3
"""UQ-016: can the successor's action-log translation silently exclude a valid shape?

The Lean host functions (`spec/lean/v3/NearSpecV3/Wasm/Host.lean`) record every promise action as
an `MAct` entry (`pushAction { text := …, … }`). `D3.manager` (`D3/FunctionCall.lean`) and, on
every whole-state successor tier, `Successor.managerGlobal` (`Successor/PromiseActions.lean`) turn
that log into `ReceiptManager` receipts. An entry the translator cannot parse becomes
`out of domain (e.wasm-α): unmodeled action log entry …`, i.e. a *silent* exclusion of a shape
nearcore executes. This script closes the question statically, for every producer site:

* it enumerates every `pushAction { … }` in `Host.lean` (no site may be skipped: the count is
  printed and every site is classified, an unclassifiable site fails the check);
* it derives the translator's accepted tags and arities from `D3.manager`'s match arms
  (`| "TAG", [f1, …]`), plus its three structural branches (`yieldCreate`, `YR:`, `CR(`);
* each producer site must be consumed: a `TAG@{r}:…` template with exactly the arity the arm
  expects; a `YR:` template with two fields; a `CR(` entry with a `receiver`; an entry with
  `yieldCreate`; or an `"OTHER"` entry, which `managerGlobal` consumes iff it carries a
  `rawAction`. An `"OTHER"` entry without `rawAction` is allowed only in the `else` branch of
  `if (← get).globalActions then` (the signed tier, where that host is out of the signed domain
  by design) and is reported separately;
* every interpolated field must be one whose rendering cannot contain the separators `@ : / ( ) >`
  (hex strings, decimal numbers, account ids, `-`).

`--inject` adds a synthetic producer site with an unknown tag (deliberate-breakage control): the
check must then fail. Exit 0 iff every site is consumed on the successor path.
"""
import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
HOST = REPO / "spec/lean/v3/NearSpecV3/Wasm/Host.lean"
MANAGER = REPO / "spec/lean/v3/NearSpecV3/D3/FunctionCall.lean"
GLOBAL = REPO / "spec/lean/v3/NearSpecV3/Successor/PromiseActions.lean"

# Interpolated field expressions whose rendering is separator-free:
#   hexStr x            -> [0-9a-f]*
#   decimal Nat         -> r, amount, gas, weight, a[i], b-values that are Nat
#   account ids         -> NEAR account ids are [a-z0-9._-] (AccountId::validate), no separators
#   "/".intercalate (names.toList.map hexStr) -> hex joined by '/', split by the AC arm on '/'
#   ",".intercalate (deps.toList.map toString) -> decimals joined by ',' inside CR(...)
SAFE_FIELD = re.compile(
    r"^(hexStr [\w.\[\]]+|r|amount|gas|weight|a\[\d\]|al|recv|acct|b|s\.ctx\.currentAccount|"
    r"\"/\"\.intercalate \(names\.toList\.map hexStr\)|\",\"\.intercalate \(deps\.toList\.map toString\))$")


def sites(src):
    out = []
    for m in re.finditer(r"pushAction \{", src):
        i, depth = m.end(), 1
        while depth:
            depth += {"{": 1, "}": -1}.get(src[i], 0)
            i += 1
        body = src[m.end():i - 1]
        # Lean string interpolation braces are inside the text; the brace matcher above balances them.
        line = src.count("\n", 0, m.start()) + 1
        out.append((line, body))
    return out


def manager_arms(src):
    body = src[src.index("def manager (log : Array MAct)"):src.index("def distribute")]
    arms = {}
    for tag, fields in re.findall(r'\| "([A-Z]{2})", \[([^\]]*)\]', body):
        arms[tag] = 0 if not fields.strip() else len(fields.split(","))
    for needle in ('e.yieldCreate', 't.startsWith "YR:"', 't.startsWith "CR("'):
        assert needle in body, f"manager no longer has the {needle} branch"
    return arms


def in_signed_else(src, line):
    """True iff the site at `line` is in the `else` branch of the nearest enclosing
    `if (← get).globalActions then`."""
    lines = src.splitlines()
    indent = len(lines[line - 1]) - len(lines[line - 1].lstrip())
    seen_else = False
    for k in range(line - 2, -1, -1):
        l = lines[k]
        ind = len(l) - len(l.lstrip())
        if ind < indent and l.strip() == "else":
            seen_else = True
            indent = ind
        elif ind <= indent and "if (← get).globalActions then" in l:
            return seen_else
        elif ind < indent and l.strip() and not l.strip().startswith("--"):
            indent = ind
        if l.startswith("def ") or l.startswith("  | \""):
            return False
    return False


def raw_is_global_some(src, line, expr):
    """`rawAction := some …` or `rawAction := raw/enc` where the variable is bound in the same host as
    `if (← get).globalActions then some …` (so it is `some` on every successor tier)."""
    if expr.startswith("some"):
        return True
    lines = src.splitlines()
    for k in range(line - 1, max(0, line - 40), -1):
        m = re.match(rf"\s*let {re.escape(expr)} := if \(← get\)\.globalActions then", lines[k - 1])
        if m:
            nxt = lines[k - 1] + lines[k]
            return "then some" in nxt.replace("\n", " ") or "then\n" in nxt or "some (" in nxt
    return False


def classify(src, arms, line, body):
    fields = dict(re.findall(r"(\w+) := ((?:s!)?\"[^\"]*\"|[^,\n]+)", body))
    text = fields.get("text", "")
    if "yieldCreate" in fields:
        return "yieldCreate", None
    if text == '"OTHER"':
        raw = fields.get("rawAction")
        if raw and raw_is_global_some(src, line, raw.strip()):
            return "OTHER+rawAction", None
        if raw is None and in_signed_else(src, line):
            return "OTHER (signed-only else branch)", None
        return None, f"OTHER entry without a successor rawAction ({raw!r})"
    m = re.match(r'^s!"(.*)"$', text)
    if not m:
        return None, f"unrecognised text {text!r}"
    tmpl = m.group(1)
    interp = re.findall(r"\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", tmpl)
    for f in interp:
        if not SAFE_FIELD.match(f.strip()):
            return None, f"field {{{f}}} may render a separator"
    if tmpl.startswith("YR:"):
        return ("YR", None) if tmpl.count(":") == 2 else (None, "YR entry arity")
    if tmpl.startswith("CR("):
        return ("CR", None) if "receiver" in fields else (None, "CR entry without receiver")
    mt = re.match(r"^([A-Z]{2})@\{r\}((?::[^:]*)*)$", tmpl)
    if not mt:
        return None, f"template {tmpl!r} is not TAG@{{r}}:…"
    tag, rest = mt.group(1), mt.group(2)
    arity = rest.count(":")
    if tag not in arms:
        return None, f"tag {tag} has no manager arm"
    if arms[tag] != arity:
        return None, f"tag {tag}: producer arity {arity} != manager arity {arms[tag]}"
    return f"{tag}/{arity}", None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inject", action="store_true", help="add a synthetic unknown-tag site (control)")
    a = ap.parse_args()
    src = HOST.read_text()
    if a.inject:
        src += '\ndef injected : HM Unit := do\n  let _ ← pushAction { text := s!"ZZ@{r}:{amount}" }\n'
    arms = manager_arms(MANAGER.read_text())
    glob = GLOBAL.read_text()
    assert 'some (r, _) => { e with text := s!"CA@{r}", rawAction := none }' in glob, \
        "managerGlobal no longer stages rawAction entries as CA@r"
    assert "CA" in arms and arms["CA"] == 0
    found = sites(src)
    bad, kinds = [], {}
    for line, body in found:
        kind, err = classify(src, arms, line, body)
        if err:
            bad.append((line, err))
        else:
            kinds[kind] = kinds.get(kind, 0) + 1
    print(f"manager arms: {dict(sorted(arms.items()))}")
    print(f"pushAction sites in Host.lean: {len(found)}")
    for k, v in sorted(kinds.items()):
        print(f"  {v:3d}  {k}")
    for line, err in bad:
        print(f"BAD Host.lean:{line}: {err}")
    print("successor path: every producer site is consumed" if not bad else f"{len(bad)} unconsumed site(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
