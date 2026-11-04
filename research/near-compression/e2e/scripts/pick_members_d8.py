"""E2E-D D-8: the sample members of each class (assign.json from classes_d8.py): the class's largest
member by natural committed cells (the headroom-critical one) and its median member. Prints
`CLASS NAME CASE_DIR` lines, largest first."""
import json, sys

a = json.load(open(sys.argv[1]))
src = {}
for line in open(a['census'] + '/list.txt'):
    k, p = line.split()
    src[k + '_' + p.rstrip('/').split('/')[-1]] = p
nc = a['natural_cells']
for k in a['classes']:
    mem = sorted((c for c, kk in a['assign'].items() if kk == k), key=lambda c: (nc[c], c))
    if not mem:
        continue
    pick = [mem[-1]] + ([mem[len(mem) // 2]] if len(mem) > 1 else [])
    for c in pick:
        print(k, c, src[c])
