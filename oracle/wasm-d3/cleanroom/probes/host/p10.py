from hp import *
C = []
for ms, fs in [("boom", "boom"), ("boomboom", "f"), ("", "")]:
    msg = ms.encode("utf-16-le"); fil = fs.encode("utf-16-le")
    blob = len(msg).to_bytes(4, "little") + msg + len(fil).to_bytes(4, "little") + fil
    L = len(blob)
    blob += b"x" * 16384
    for pre in range(16300, 16385, 3):
        C.append((f"{ms}/{fs} {pre}", P(blob).call("log_utf8", pre, L).call("abort", 4, 8 + len(msg), 1, 1).done()))
cmp(C, 150)
