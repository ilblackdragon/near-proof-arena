import sys
d = '/tmp/claude-1002/-data-illia-nearproof/e268603b-12da-4c61-ab1c-70f2a15e868f/scratchpad/'
arms = [l.strip() for l in open(d + 'arms.txt') if l.strip()]
carms = [l.strip() for l in open(d + 'carms.txt') if l.strip()]
out = []
out.append('/-! ## Per-arm (generated) -/\n')

def table(fn, names, tag):
    for i, n in enumerate(names, 1):
        out.append(f'set_option maxHeartbeats 0 in\n'
                   f'theorem HOR_{tag}_{i} (r : St) (h : HM Unit) (hh : {fn} "{n}" = some h) : HOR r h := by\n'
                   f'  rw [{fn}.eq_{i}] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr\n')
    out.append(f'theorem HOR_{fn} (r : St) (name : String) (h : HM Unit) (hh : {fn} name = some h) :\n'
               f'    HOR r h := by')
    hs = []
    for i, n in enumerate(names, 1):
        out.append(f'  by_cases h{i} : name = "{n}"')
        out.append(f'  · subst h{i}; exact HOR_{tag}_{i} r h hh')
        hs.append(f'h{i}')
    k = len(names) + 1
    out.append(f'  rw [{fn}.eq_{k} name {" ".join(hs)}] at hh; cases hh\n')

table('hostCall', arms, 'hc')
table('cryptoHostCall', carms, 'cc')
out.append('''theorem hostsOK : HostsOK := by
  intro s name h u s' hd hr
  have key : HOR s h := by
    unfold dispatchArm at hd
    split at hd
    · rename_i h' hh; cases hd; exact HOR_hostCall s name _ hh
    · split at hd
      · exact HOR_cryptoHostCall s name h hd
      · cases hd
  exact key s u s' (HostMono.refl s) hr

#print axioms hostsOK
''')
sys.stdout.write('\n'.join(out))
