from hp import *
C = []
D = b"bob.near" + bytes(16) + b"m"
for prepaid in [10**13, 3*10**14]:
    for g in [10**12, 10**14, 5*10**14, 10**15 - 10**12, 10**15, 10**15 + 1, 2**63, 2**64-10**13]:
        C.append((f"fc {prepaid} {g}", P(D, gas=prepaid).call("promise_batch_create", 8, 0).call("promise_batch_action_function_call", 0, 1, 24, 0, 0, 8, g).done(False)))
cmp(C, 200)
