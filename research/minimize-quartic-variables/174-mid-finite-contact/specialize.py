from verify import *
unmixed=collections.defaultdict(dict)
for (k,m),v in s.items():unmixed[m][k]=v
assert len(unmixed)==2495 and sum(len(d)>1 for d in unmixed.values())==2 and all(d=={0:-578,2:289} for d in unmixed.values() if len(d)>1);assert set(inv)=={j for m in unmixed for j in m}
print('PASS 174 active at every N >= 1, 2495 specialized monomials')
