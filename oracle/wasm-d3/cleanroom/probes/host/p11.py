from hp import *
C = []
s16 = ("€" * 100).encode("utf-16-le")   # 200 bytes utf16, 300 bytes utf8
blob = s16 + s16 + b"\0\0" + b"x" * 16384
for pre in [16000, 16084, 16085, 16100, 16184, 16185, 16200]:
    C.append((f"log16 euro {pre}", P(blob).call("log_utf8", pre, 402).call("log_utf16", 200, 0).done()))
    C.append((f"log16z euro {pre}", P(blob).call("log_utf8", pre, 402).call("log_utf16", U64MAX, 200).done()))
cmp(C, 250)
