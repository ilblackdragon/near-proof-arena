import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tests"))
import gen_d3a, mutate
n, seed, want = int(sys.argv[1]), int(sys.argv[2]), [int(x) for x in sys.argv[3:]]
r = random.Random(seed); g = gen_d3a.Gen(random.Random(seed + 1000))
for i in range(n):
    gas, w = g.case(); mw = mutate.mutate(r, w)
    if i in want:
        k = next((j for j in range(min(len(w), len(mw))) if w[j] != mw[j]), None)
        print(i, "orig len", len(w), "mut len", len(mw), "first diff at", k)
        print(" orig:", w[max(0,k-24):k+16].hex()); print(" mut :", mw[max(0,k-24):k+16].hex())
