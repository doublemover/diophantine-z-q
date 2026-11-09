#!/usr/bin/env python3
"""Source coverage, exact operation dependencies and finite nesting checks only."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent
expected={
 'ReciprocalChartWitness318':set(range(1,33))|set(range(58,74)),
 'CompressedAnchorWitness318':set(range(33,38))|set(range(74,78)),
 'RealGuardWitness318':set(range(78,90)),
 'PadeRatioWitness318':set(range(90,118)),
 'DetectorGateWitness318':set(range(118,146))}
seen=set()
for name,want in expected.items():
 s=(HERE/(name+'.lean')).read_text(); section=s.split('def fill ',1)[1].split('\n\n',1)[0]
 got=set(map(int,re.findall(r'(?:\|\s*(\d+)\s*=>)',section))) if 'match ' in section else set(map(int,re.findall(r'if i=(\d+)',section)))
 assert got==want,(name,got^want)
 assert not(seen&got)
 seen|=got
assert seen|({0}|set(range(38,58)))==set(range(146))
src=(HERE/'DetectorGateWitness318.lean').read_text()
new=(HERE/'DetectorLocalRegularity318.lean').read_text()
for n in range(118,146):
 expr=re.search(rf'def value{n} \(w : Assignment\) : ℚ := (.*)',src).group(1)
 deps=sorted(set(map(int,re.findall(r'value(\d+)',expr))))
 proof=new.split(f'lemma value{n}_regular',1)[1].split('\n\n',1)[0]
 assert f'unfold value{n}' in proof
 for d in deps:
  assert d<n
  assert f'value{d}_regular p h₀ w hw' in proof
 assert f'have h{n} := value{n}_regular p h₀ w hw' in new
for E in range(6):
 for N in range(E,8):
  for m in range(-10,11):
   for center in [-7,0,31]:
    assert center+4*6**N*m==center+4*6**E*(6**(N-E)*m)
for M in [1,2,5,64,119]:
 for E in range(5):
  L=M*4*6**E
  assert L>0 and L%M==0 and L%(4*6**E)==0
  for center in [0,1,64,100]:
   for h in [x for x in range(200) if (x-center)%L==0]:
    assert (h-center)%(4*6**E)==0
m=json.loads((HERE/'SOURCE-COPIES.json').read_text())
assert len(m['unchanged_sources'])==134 and not m['new_sources'] and set(m['repaired_sources'])=={'PrefixLocalRegularity318','DetectorLocalRegularity318'}
for name,binding in m['unchanged_sources'].items():
 assert hashlib.sha256((HERE/(name+'.lean')).read_bytes()).hexdigest()==binding['source_sha256']
print('PASS: exact5 fill supports/all146 coordinates,all28 original gate dependencies, signed nested-index and retained-modulus sanity,134 unchanged sources and two docstring/include-order repairs')
