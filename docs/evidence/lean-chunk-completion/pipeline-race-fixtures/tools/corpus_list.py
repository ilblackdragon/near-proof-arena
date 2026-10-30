import glob, random
random.seed(20261030)
ood = sorted(d for d in glob.glob('/data/illia/nearproof-deps/corpora/*/ood/*') if 'cold' not in d and 'warm-orig' not in d)
code = sorted(glob.glob('/data/illia/nearproof-deps/corpora/*/mutants/*-code.*'))
pick = ood + [c for c in code if random.random() < 0.10]
open('/data/illia/nearproof-deps/w12-runs/corpus.list', 'w').write('\n'.join(pick) + '\n')
print(len(ood), len(code), len(pick))
