from hp import *
C = []
msg = "boom".encode("utf-16-le")
blob = len(msg).to_bytes(4, "little") + msg + b"x" * 16384
L = len(blob)
C.append(("abort<4 after 100 logs", (lambda p: [p.call("log_utf8", 1, 0) for _ in range(100)] and p.call("abort", 2, 4, 1, 1).done())(P(blob))))
for pre in [16340, 16350, 16355, 16356, 16357, 16380, 16384]:
    C.append((f"abort after {pre}", P(blob).call("log_utf8", pre, 12).call("abort", 4, 4, 1, 1).done()))
    C.append((f"panic16 after {pre}", P(blob).call("log_utf8", pre, 12).call("log_utf16", 8, 4).done()))
cmp(C, 300)
