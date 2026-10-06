import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Sched.Ids — buses and constants of the scheduler tables (lane `v3-sched`)

Buses `40 …` are lane-local (the assembly may renumber; every statement is parametric only in
the table definitions, which use these constants). External buses: `VBYTES` (21, trie),
`BYTES`/`DIGEST` (0/1, SHA). Public records are byte tuples (the public vector is the prepared
statement's bytes); `τ < 32`.

| # | bus | message | producers → consumers |
|---|---|---|---|
| 40 | `SCMP` | `(x, y, b)`: `b = [y ≤ x]` | memory, process, codec, distribute → comparator |
| 41 | `SOP` | `(addr, t, op, vin, v, inc, ok, c)` | codec / distribute (INIT, `op = 0`), scan (READ, 1), process (GRANT, 2) → memory |
| 42 | `SFIN` | `(addr, v, w)` | memory (segment end) → codec (links), distribute (budgets) |
| 43 | `SINC` | `(τ, e = cid·64 + j, inc, rem, s, r, link)` | scan → process |
| 44 | `SPUSH` | `(τ, key, z, ts, e)` | scan (initial), process (re-push) → process (bucket entry) |
| 45–50 | shuffle in / out / mem / gen / headers / chacha | lane v3-chacha formats | `shufV3`/`genV3`/`chachaV3` ↔ process |
| 51 | `SPUBB` | public `(τ, tag, x₀, x₁, x₂, x₃, x₄)` | public → codec (ash: tag 2 `(j, byte, 0, 0, 0)`; forwarding demand of link `l` in instance 0: tag 4 `(l_lo, l_hi, t₀, t₁, t₂)`), process (key limbs: tag 3 `(k, lo, hi, 0, 0)`) |
| 52 | `SPAR` | public `(τ, tag, n, p0 … p7)` | public → codec (tag 0), scan (tag 1) |
| 53 | `SRAW` | public `(τ, rid_lo, rid_hi, s, r, bm0 … bm4)` | public → scan |
| 54 | `SLINK` | public `(τ, l_lo, l_hi, allowed)` | public → distribute |
| 55 | `SSHD` | public `(τ, side, s, cnt, b0, b1, b2)` | public → distribute |
| 56 | `SDL` | `(τ, k_lo, k_hi, o, b)` | codec id byte `o < 16` of record `k`: instance τ → τ + 1 (public sends instance 0, receives `K + 1`) |
| 57 | `SDLX` | `(τ, a, b, x, links, left)` | distribute: sorted endpoints → grid, receiver delay line |
| 58 | `SDG` | `(τ, l, allowed, gb)` | distribute grid → codec |
| 59 | `S0F` | `(τ, present, vid)` | trie (`0x0f` read of instance τ) → codec |
| 60 | `SPOST` | `(τ, pos, b)` | codec → `upsV3` (new `0x0f` value bytes) |
-/

namespace ZkFormal.NearV3.Sched

def B_SCMP : Nat := 40
def B_SOP : Nat := 41
def B_SFIN : Nat := 42
def B_SINC : Nat := 43
def B_SPUSH : Nat := 44
def B_SSIN : Nat := 45
def B_SSOUT : Nat := 46
def B_SSMEM : Nat := 47
def B_SGEN : Nat := 48
def B_SSHUF : Nat := 49
def B_SCHACHA : Nat := 50
def B_SPUBB : Nat := 51
def B_SPAR : Nat := 52
def B_SRAW : Nat := 53
def B_SLINK : Nat := 54
def B_SSHD : Nat := 55
def B_SDL : Nat := 56
def B_SDLX : Nat := 57
def B_SDG : Nat := 58
def B_S0F : Nat := 59
def B_SPOST : Nat := 60

/-- Memory op codes. -/
def OP_INIT : Nat := 0
def OP_READ : Nat := 1
def OP_GRANT : Nat := 2

/-- Memory addresses: `τ·2^14 + kind·2^12 + idx` (kind 0 = link, 1 = sender, 2 = receiver). -/
def addrOf (τ kind idx : Nat) : Nat := τ * 16384 + kind * 4096 + idx

/-- Process times start at `2^20` (initial pushes use `ts = cid < 2^20`). -/
def T0 : Nat := 1048576

/-- Shuffle list id of a round: `τ·2^22 + T` (round start time `T`). -/
def lidOf (τ T : Nat) : Nat := τ * 4194304 + T

/-- Public byte-record tags. -/
def TAG_IDS : Nat := 0
def TAG_IDR : Nat := 1
def TAG_ASH : Nat := 2
def TAG_KEY : Nat := 3
def TAG_FWD : Nat := 4

end ZkFormal.NearV3.Sched
