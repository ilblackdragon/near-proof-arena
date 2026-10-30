"""Copy a case and zero its claim's epoch_start_after flags (claim-v3 encoding, ClaimV3.lean)."""
import os, shutil, struct, sys

src, dst = sys.argv[1], sys.argv[2]
cb = bytearray(open(os.path.join(src, "claim.bin"), "rb").read())
p = 0
def u32():
    global p
    v = struct.unpack_from("<I", cb, p)[0]; p += 4; return v
def borsh():
    global p
    n = u32(); s = p; p += n; return s, n
borsh(); borsh()          # claim tag, statement id
p += 4                    # protocol version
borsh()                   # chain id
p += 32                   # epoch id
borsh()                   # chunk inner
for _ in range(u32()):    # blocks
    p += 1 + 32; borsh(); borsh()
    for _ in range(u32()):
        borsh(); p += 8
p += 4                    # rs parts
for _ in range(u32()):    # epochs
    p += 32 + 4 + 8; borsh()
    for _ in range(u32()):
        borsh(); p += 16
s, n = borsh()
print("epoch_start_after", list(cb[s:s + n]))
for i in range(s, s + n):
    cb[i] = 0
os.makedirs(dst, exist_ok=True)
shutil.copy(os.path.join(src, "witness.bin"), dst)
open(os.path.join(dst, "claim.bin"), "wb").write(cb)
