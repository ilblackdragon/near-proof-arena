"""Canonical failure kinds for the W01 comparison (`full_observables.py`).

nearcore records an outcome's failure as the `Debug` text of its `TxExecutionError`, e.g.
`ActionError(ActionError { index: Some(0), kind: FunctionCallError(HostError(GuestPanic { panic_msg:
"x" })) })`. The Lean checker emits a dotted path with the VM error in nearcore's own `Debug`
syntax, e.g. `ActionError[0].FunctionCallError(HostError(GuestPanic { panic_msg: "x" }))`.

Both are reduced to one canonical form: the chain of variant names, with the action index for
`ActionError`, and without payloads (account ids, amounts, nonces, messages):
`ActionError[0].FunctionCallError.HostError.GuestPanic`, `InvalidTxError.InvalidNonce`,
`InvalidTxError.InvalidAccessKeyError.RequiresFullAccess`, `ActionError[None].LackBalanceForState`.

A tuple variant whose single argument is itself a variant (`HostError(GasExceeded)`) is followed
into; a string, number, `AccountId(..)`-style newtype in a struct field, or a struct body ends the
path. `NewReceiptValidationError` is truncated at its own name (the Lean checker does not classify
the receipt validation error inside it).
"""
import re

TRUNCATE = {'NewReceiptValidationError'}
_IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')


class _P:
    def __init__(self, s):
        self.s = s
        self.i = 0

    def ws(self):
        while self.i < len(self.s) and self.s[self.i] == ' ':
            self.i += 1

    def ident(self):
        self.ws()
        m = _IDENT.match(self.s, self.i)
        if not m:
            return None
        self.i = m.end()
        return m.group(0)

    def peek(self):
        self.ws()
        return self.s[self.i] if self.i < len(self.s) else ''

    def skip_balanced(self):
        """Skip one bracketed group starting at the current `(`, `{` or `[` (strings respected)."""
        close = {'(': ')', '{': '}', '[': ']'}
        stack = []
        while self.i < len(self.s):
            c = self.s[self.i]
            if c == '"':
                self.i += 1
                while self.i < len(self.s) and self.s[self.i] != '"':
                    self.i += 2 if self.s[self.i] == '\\' else 1
            elif c in close:
                stack.append(close[c])
            elif stack and c == stack[-1]:
                stack.pop()
                if not stack:
                    self.i += 1
                    return
            self.i += 1

    def struct_fields(self):
        """Parse `{ a: X, b: Y }` into {name: raw text}; the cursor is at `{`."""
        start = self.i
        self.skip_balanced()
        body = self.s[start + 1:self.i - 1]
        fields, depth, cur, ins = {}, 0, '', False
        parts = []
        for ch in body:
            if ch == '"':
                ins = not ins
            if not ins:
                if ch in '({[':
                    depth += 1
                elif ch in ')}]':
                    depth -= 1
                elif ch == ',' and depth == 0:
                    parts.append(cur)
                    cur = ''
                    continue
            cur += ch
        if cur.strip():
            parts.append(cur)
        for p in parts:
            if ':' in p:
                k, v = p.split(':', 1)
                fields[k.strip()] = v.strip()
        return fields


def _variant_path(text):
    """The variant-name chain of one `Debug` term."""
    p = _P(text)
    out = []
    while True:
        name = p.ident()
        if name is None:
            break
        if name == 'ActionError' and p.peek() == '{':
            f = p.struct_fields()
            idx = f.get('index', 'None')
            m = re.fullmatch(r'Some\((\d+)\)', idx)
            out.append(f'ActionError[{m.group(1) if m else "None"}]')
            out.extend(_variant_path(f.get('kind', '')))
            break
        out.append(name)
        if name in TRUNCATE:
            break
        c = p.peek()
        if c == '(':
            # descend only into a single variant argument
            start = p.i
            p.skip_balanced()
            inner = text[start + 1:p.i - 1].strip()
            if inner and _IDENT.fullmatch(inner.split('(')[0].split(' ')[0] or '') and inner[0].isupper():
                if name == 'ActionError':          # `ActionError(ActionError { .. })`
                    return out[:-1] + _variant_path(inner)
                return out + _variant_path(inner)
            break
        break
    return out


def canonical(kind):
    """Canonical dotted kind of a nearcore `Debug` error or a Lean-emitted kind; `None` passes."""
    if kind is None:
        return None
    kind = kind.strip()
    # Lean form: dotted prefix, then possibly a Debug term (`ActionError[0].FunctionCallError(...)`)
    m = re.match(r'((?:ActionError\[(?:\d+|None)\]|InvalidTxError)(?:\.[A-Za-z_][A-Za-z0-9_]*)*)(\(.*)?$', kind, re.S)
    if m and (kind.startswith('ActionError[') or kind.startswith('InvalidTxError.')):
        head = m.group(1).split('.')
        tail = m.group(2)
        if tail:
            # the last dotted segment is the variant whose Debug argument follows
            head = head[:-1] + _variant_path(head[-1] + tail)
        path = []
        for seg in head:
            path.append(seg)
            if seg in TRUNCATE:
                break
        return '.'.join(path)
    return '.'.join(_variant_path(kind))


# nearcore collapses VM execution errors into `FunctionCallError::ExecutionError(<Display>)`
# (`runtime/runtime/src/conversions.rs:74-90`). The Display text identifies the variant
# (`near-vm-runner/src/logic/errors.rs:458-636`); this table maps it back, so both sides compare at
# `FunctionCallError.HostError.<V>` / `FunctionCallError.WasmTrap.<V>` / `LinkError` / `LoadingError`.
_HOST_DISPLAY = [
    (r'String encoding is bad UTF-8 sequence\.$', 'BadUTF8'),
    (r'String encoding is bad UTF-16 sequence\.$', 'BadUTF16'),
    (r'Exceeded the prepaid gas\.$', 'GasExceeded'),
    (r'Exceeded the maximum amount of gas allowed to burn per contract\.$', 'GasLimitExceeded'),
    (r'Exceeded the account balance\.$', 'BalanceExceeded'),
    (r'Tried to call an empty method name\.$', 'EmptyMethodName'),
    (r'Smart contract panicked: ', 'GuestPanic'),
    (r'Integer overflow\.$', 'IntegerOverflow'),
    (r'Iterator index .* does not exist$', 'InvalidIteratorIndex'),
    (r'.* does not correspond to existing promises$', 'InvalidPromiseIndex'),
    (r'Actions can only be appended to non-joint promise\.$', 'CannotAppendActionToJointPromise'),
    (r'Returning joint promise is currently prohibited\.$', 'CannotReturnJointPromise'),
    (r'Setting refund_to on a joint promise is prohibited\.$', 'CannotSetRefundToOnJointPromise'),
    (r'Accessed invalid promise result index: ', 'InvalidPromiseResultIndex'),
    (r'Accessed invalid register id: ', 'InvalidRegisterId'),
    (r'Accessed memory outside the bounds\.$', 'MemoryAccessViolation'),
    (r'VM Logic returned an invalid receipt index: ', 'InvalidReceiptIndex'),
    (r'Action .* in receipt .* does not exist or has the wrong type of action\.$', 'InvalidActionIndex'),
    (r'VM Logic returned an invalid account id$', 'InvalidAccountId'),
    (r'VM Logic returned an invalid method name$', 'InvalidMethodName'),
    (r'VM Logic provided an invalid public key$', 'InvalidPublicKey'),
    (r'.* is not allowed in view calls$', 'ProhibitedInView'),
    (r'The number of logs will exceed the limit ', 'NumberOfLogsExceeded'),
    (r'The length of a storage key .* exceeds the limit ', 'KeyLengthExceeded'),
    (r'The length of a storage value .* exceeds the limit ', 'ValueLengthExceeded'),
    (r'The length of a log message .* exceeds the limit ', 'TotalLogLengthExceeded'),
    (r'The number of promises within a FunctionCall ', 'NumberPromisesExceeded'),
    (r'The number of input data dependencies ', 'NumberInputDataDependenciesExceeded'),
    (r'The length of a returned value ', 'ReturnedValueLengthExceeded'),
    (r'The size of a contract code in DeployContract action ', 'ContractSizeExceeded'),
    (r'Attempted to call deprecated host function ', 'Deprecated'),
    (r'AltBn128 invalid input: ', 'AltBn128InvalidInput'),
    (r'ECDSA recover error: ', 'ECRecoverError'),
    (r'ED25519 signature verification error: ', 'Ed25519VerifyInvalidInput'),
    (r'P256 signature verification error: ', 'P256VerifyInvalidInput'),
    (r'BLS12-381 invalid input: ', 'BLS12381InvalidInput'),
    (r'Yield resume payload is .* bytes which exceeds the .* byte limit$', 'YieldPayloadLength'),
    (r'yield resumption token is malformed$', 'DataIdMalformed'),
    (r'yield id is malformed$', 'YieldIdMalformed'),
    (r'Size of the recorded trie storage proof has exceeded the allowed limit ', 'RecordedStorageExceeded'),
    (r'contract code hash is malformed$', 'ContractCodeHashMalformed'),
    (r'Data entry for given key already exists$', 'DataEntryAlreadyExists'),
]
_TRAP_DISPLAY = [
    (r'An `unreachable` opcode was executed\.$', 'Unreachable'),
    (r'Call indirect incorrect signature trap\.$', 'IncorrectCallIndirectSignature'),
    (r'Memory out of bounds trap\.$', 'MemoryOutOfBounds'),
    (r'Call indirect out of bounds trap\.$', 'CallIndirectOOB'),
    (r'An arithmetic exception, e\.g\. divided by zero\.$', 'IllegalArithmetic'),
    (r'Misaligned atomic access trap\.$', 'MisalignedAtomicAccess'),
    (r'Generic trap\.$', 'GenericTrap'),
    (r'Stack overflow\.$', 'StackOverflow'),
    (r'Indirect call to null\.$', 'IndirectCallToNull'),
]


def execution_error_variant(msg):
    """`FunctionCallError::ExecutionError(msg)` → the collapsed variant path, or None."""
    if msg.startswith('WebAssembly trap: '):
        rest = msg[len('WebAssembly trap: '):]
        for rx, v in _TRAP_DISPLAY:
            if re.match(rx, rest, re.S):
                return 'WasmTrap.' + v
        return None
    if msg.startswith('Link Error: '):
        return 'LinkError'
    if msg.startswith('Loading Error: '):
        return 'LoadingError'
    for rx, v in _HOST_DISPLAY:
        if re.match(rx, msg, re.S):
            return 'HostError.' + v
    return None


_EXEC = re.compile(r'FunctionCallError\(ExecutionError\("((?:[^"\\]|\\.)*)"\)\)')


def canonical_expected(error):
    """nearcore's `Debug` error → canonical kind, resolving `ExecutionError(<Display>)` to the
    VM variant it was collapsed from. An unrecognised message stays `...ExecutionError`."""
    base = canonical(error)
    if base is None or not base.endswith('FunctionCallError.ExecutionError'):
        return base
    m = _EXEC.search(error)
    if not m:
        return base
    msg = m.group(1).encode('latin-1', 'backslashreplace').decode('unicode_escape')
    v = execution_error_variant(msg)
    return base[:-len('ExecutionError')] + v if v else base


_LEAN_VM = re.compile(r'^(.*FunctionCallError)\((HostError|WasmTrap)\((.*)\)\)$', re.S)


def canonical_lean(kind):
    """The Lean-emitted kind → canonical form. LinkError / LoadingError keep only their name.
    The Lean VM reports some host errors with nearcore's Display text inside the variant
    (`HostError(AltBn128 invalid input: …)`); those are resolved with the same Display table."""
    if kind is not None:
        m = _LEAN_VM.match(kind.strip())
        if m and not _IDENT.fullmatch(m.group(3).split(' {')[0].split('(')[0]):
            inner = m.group(3) if m.group(2) == 'HostError' else 'WebAssembly trap: ' + m.group(3)
            v = execution_error_variant(inner)
            if v is not None:
                return canonical(m.group(1)) + '.' + v
    c = canonical(kind)
    if c is None:
        return None
    for v in ('FunctionCallError.LinkError', 'FunctionCallError.LoadingError'):
        i = c.find(v)
        if i >= 0:
            return c[:i + len(v)]
    return c
