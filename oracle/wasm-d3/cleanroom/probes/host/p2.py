from hp import *
C = []
D = b"keyvalue" + bytes(5000)
C.append(("w1", P(D).call("storage_write", 3, 0, 5000, 8, 0).done()))
C.append(("w1w2", P(D).call("storage_write", 3, 0, 5000, 8, 0).call("storage_write", 3, 0, 5, 3, 1).call("register_len", 1).done()))
C.append(("w1w2small", P(D).call("storage_write", 3, 0, 7, 8, 0).call("storage_write", 3, 0, 5, 3, 1).call("register_len", 1).done()))
C.append(("w1w1 same", P(D).call("storage_write", 3, 0, 7, 8, 0).call("storage_write", 3, 0, 7, 8, 1).call("register_len", 1).done()))
C.append(("w1 rm", P(D).call("storage_write", 3, 0, 5000, 8, 0).call("storage_remove", 3, 0, 1).call("register_len", 1).done()))
C.append(("w1 rd", P(D).call("storage_write", 3, 0, 5000, 8, 0).call("storage_read", 3, 0, 1).call("register_len", 1).done()))
C.append(("w1 rd small", P(D).call("storage_write", 3, 0, 50, 8, 0).call("storage_read", 3, 0, 1).call("register_len", 1).done()))
C.append(("w1 rm small", P(D).call("storage_write", 3, 0, 50, 8, 0).call("storage_remove", 3, 0, 1).call("register_len", 1).call("storage_usage").done()))
C.append(("w1 usage", P(D).call("storage_write", 3, 0, 50, 8, 0).call("storage_usage").call("storage_write", 3, 0, 10, 8, 0).call("storage_usage").done()))
cmp(C)
