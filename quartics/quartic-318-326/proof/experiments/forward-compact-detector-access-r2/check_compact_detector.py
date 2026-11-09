"""Exact source-map/support checks, not kernel validation."""
from pathlib import Path
import re
p=Path(__file__).parent
r=(p/'RealDetectorCoefficients318.lean').read_text();q=(p/'DetectorGateWitness318.lean').read_text()
for i in range(118,146):
 a=re.search(r'def value'+str(i)+r' .*? := (.*)',q).group(1)
 b=re.search(r'def value'+str(i)+r' .*? := (.*)',r).group(1)
 assert a==b,i
 assert all(n<118 for n in map(int,re.findall(r'w (\d+)',a))),i
# Each original pre-detector stored slot must occur once in the real raw extension.
expected=set()
for name in ['ReciprocalChartWitness318','RealGuardWitness318','PadeRatioWitness318']:
 s=(p/(name+'.lean')).read_text();s=s.split('@[expose] def fill',1)[1].split('lemma',1)[0].split('theorem',1)[0]
 expected.update(map(int,re.findall(r'\| (\d+) =>',s)))
expected.update([33,34,35,36,37,74,75,76,77])
raw=r.split('@[expose] def raw',1)[1].split('@[expose] def value118',1)[0]
actual=list(map(int,re.findall(r'\| (\d+) =>',raw)))
assert len(actual)==len(set(actual))
assert set(actual)==expected,(set(actual)-expected,expected-set(actual))
assert '| 62 => re (fun e => (u labels 2 e X)^2)/2' in raw
for j in range(4):
 for k,(f,proj) in enumerate([('primary','re'),('primary','im'),('alternate','re'),('alternate','im')]):
  assert f'| {102+4*j+k} => {proj} (fun e => {f} labels {j} e X)' in raw
 assert f'| {78+3*j} => (guard labels {j} X)⁻¹' in raw
 assert f'| {79+3*j} => re (fun e => root labels {j} e X)' in raw
 assert f'| {80+3*j} => im (fun e => root labels {j} e X)' in raw
assert '| _ => (q:ℝ)' in raw
print('PASS:28 exact detector polynomials, source support, all'+str(len(actual))+' stored pre-detector slots, half-scaled third square, primary/alternate/root slot order')
