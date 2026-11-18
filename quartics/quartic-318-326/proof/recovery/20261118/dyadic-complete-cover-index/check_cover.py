"""Compute each original ordered class's dyadic terminal-proof selector. Standard library only."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib,json,sys
V=(1,-1,2,-2)
contacts=(0,32,76832,-343)
def rep(x):
    x=F(x); assert x
    a=x.numerator;b=x.denominator;n=0
    while a%2==0:a//=2;n+=1
    while b%2==0:b//=2;n-=1
    return (1 if a*pow(b,-1,4)%4==1 else -1)*(2**(n%2))
def working(q,switch):
    if not switch:return q,tuple(map(F,contacts))
    M=375*343
    return (tuple(rep(F(q[i],q[3])*F(343+contacts[i],M)) for i in range(3))+(rep(F(-1,M*q[3])),),
            (F(0),F(32),F(1120,3),F(375)))
def select(q):
    p=[abs(i)==2 for i in q];n=sum(p[:3]);jks=lambda g:[i for i in range(3) if g[i]]
    if len(set(q[:3]))==1:
        if n==3:return ('wild2222' if p[3] else 'wild222odd')
        if p[3]:return 'wild0002' if q==(1,1,1,2) else 'wilddd2'
        if q[3]==-1:return 'wildddminus'
        return 'residual' if q[0]==1 else 'wild1110'
    if n==0 and not p[3]:
        if q[3]==1:return 'terminal6'
        return 'terminal2' if q[1]==q[2] else 'terminal4'
    if n in (0,3) and p[3]:
        switch=n==3;t,e=working(q,switch);assert all(abs(t[i])==1 for i in range(3))
        if t[1]==t[2]:return 'even8'
        d=t[0];a=t[3]//2
        return 'evenclose' if d==(a if switch else -a) else 'evenunsplit'
    if p[3]:
        t,e=working(q,n==2);j,k=[i for i in range(3) if abs(t[i])==1];m=3-j-k
        if t[j]!=t[k]:return 'parityopposite'
        A=(t[m]//2*t[j]-(t[3]//2)*(e[j]-e[3]))/2;assert A.denominator%2
        if not A.numerator%2:return 'parityeven'
        return 'parity24' if j==1 else 'parity16'
    if q[3]==1:return 'gaussian54'
    if n==3:return 'unram6'
    assert n in (1,2);epsilon=(n==2)
    j,k=[i for i in range(3) if p[i]==epsilon]
    if q[j]==q[k]:return 'urmatch'
    return 'uroppfinal' if epsilon else 'uropp12'
EXPECTED=dict(residual=1,wild0002=1,wild1110=1,wilddd2=3,wildddminus=2,wild2222=4,wild222odd=4,
              terminal2=2,terminal4=4,terminal6=6,even8=8,evenclose=8,evenunsplit=8,parity24=8,parity16=16,parityeven=24,parityopposite=48,
              gaussian54=54,unram6=6,urmatch=24,uropp12=12,uroppfinal=12)
def rows():
    out=[{'mask':format(i,'02x'),'q':list(q),'terminal':select(q)} for i,q in enumerate(product(V,repeat=4))]
    assert len({r['mask'] for r in out})==len({tuple(r['q']) for r in out})==256
    assert Counter(r['terminal'] for r in out)==EXPECTED
    return out
def verify(root):
    rows1=rows(); tab=json.loads((root/'cover.json').read_text());src=json.loads((root/'proof-map.json').read_text())
    assert rows1==tab and set(EXPECTED)<=set(src['proofs'])
    assert all(len(v['sha256'])==64 for v in src['proofs'].values())
    if '--verify-sources' in sys.argv[1:]:
        for rec in src['proofs'].values():
            source=(root/rec['path']).read_bytes()
            assert hashlib.sha256(source).hexdigest()==rec['sha256'],rec['path']
    print('256 unique representative masks, 22 terminal proof selectors; no Lean checking performed')
if __name__=='__main__':
    verify(Path(__file__).resolve().parent)
