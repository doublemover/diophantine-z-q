"""Static/algebraic correspondence only; no Lean command or topology proof check."""
from pathlib import Path
import re,json,hashlib
import sympy as S
p=Path(__file__).resolve().parent
s=(p/'PadicDetectorCoefficients318.lean').read_text()
old=(p/'DetectorWeightPreparation318.lean').read_text().split('@[expose] def coefficients')[1].split('@[expose] def weights')[0]
leaves=re.findall(r'\(\d,pair \((.*?)\) \((.*?)\)\)',old)
new=s.split('@[expose] def values')[1].split('lemma values_continuous')[0]
vs=re.findall(r'\(([^(),]*),([^(),]*)\)',new.split('![')[1])
assert len(vs)==len(leaves)==16,(len(vs),len(leaves))
def expr(t):return S.sympify(re.sub(r'w (\d+)',lambda m:'W'+m[1],t).replace('^','**'))
for (a,b),(x,y) in zip(leaves,vs):
    assert S.expand(expr(a)-expr(x))==0
    assert S.expand(expr(b)-expr(y))==0
    assert all(int(i)<146 for i in re.findall(r'w (\d+)',a+' '+b))
# Independent sanity of the explicit uniform arithmetic threshold, including
# negative coefficient/scale valuations. This is not the universal proof.
for B in range(-12,13):
 for C in range(-12,13):
  for E in [0,1]:
   for A in [0,1,2,3,8]:
    N=abs(B)+244*abs(C)+abs(E)+A+1
    assert C<N
    assert all(-B<6*N+k*C for k in [4,64,244])
    assert A<=2*N-12*C-2*E
m=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(m['unchanged_sources'])==122 and not m['new_sources'] and set(m['repaired_sources'])=={'NormalizedPointSigns318'}
for name,item in m['unchanged_sources'].items():
    assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==item['source_sha256']
assert '∀ (u d : ℚ)' in (p/'SourcePadicDetectorRegion318.lean').read_text()
assert '∀ h : ℤ' in (p/'SourcePadicDetectorRegion318.lean').read_text()
print('PASS:32 exact p-adic coefficient-map identities,original indices,uniform-threshold sanity,122 source-copy bindings and one syntax/map-one repair. No Lean/topological/CRT-access claim.')
