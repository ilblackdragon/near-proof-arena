"""Mirror of the A-T1 Lean change to `Seg.HostBK` on an exported segment-AIR JSON (temporary, until
the Lean change lands): column `ob` (16) and `writeInters` with count act*dir*(1-reg)."""
import json, sys
a = json.load(open(sys.argv[1]))
t = [t for t in a['tables'] if t['name'] == 'HOSTB'][0]
assert t['cols'][-2:] == ['hg0', 'hg1'], t['cols']
t['cols'].append('ob')
v = lambda i: ['v', i]
c = lambda n: ['c', n]
mul = lambda x, y: ['*', x, y]
sub = lambda x, y: ['-', x, y]
add = lambda x, y: ['+', x, y]
TS, DIR, POS, BV, ACT, REG, PLO, PHI, MTP, HP, OB = 0, 1, 2, 3, 7, 9, 10, 11, 12, 13, 16
wc = mul(mul(v(ACT), v(DIR)), sub(c(1), v(REG)))
addr = add(add(v(PLO), mul(c(65536), v(PHI))), v(POS))
t['inters'] += [
    {'bus': 2, 'send': False, 'count': wc, 'msg': [c(3), addr, c(0), v(OB), c(0), c(0), c(0), v(MTP)]},
    {'bus': 2, 'send': True, 'count': wc, 'msg': [c(3), addr, c(0), v(BV), c(0), c(0), c(0), v(TS)]},
    {'bus': 3, 'send': True, 'count': wc, 'msg': [sub(sub(sub(v(TS), v(MTP)), c(1)), mul(c(65536), v(HP)))]},
    {'bus': 3, 'send': True, 'count': wc, 'msg': [mul(c(4), v(HP))]},
]
json.dump(a, open(sys.argv[2], 'w'))
