#!/usr/bin/env python3
"""Independent exact pilot local Selmer rows and Gaussian ray unit test."""
from hashlib import sha256
from itertools import product
from math import isqrt
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
def pin(path,h):
    b=(root/path).read_bytes()
    assert sha256(b).hexdigest()==h
    return json.loads(b)
J=pin('linked-detector-gaussian-order29-new-classes-r1/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json',
      '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
K=pin('linked-detector-three-class-local-after-selmer4-r1/EXACT-THIRD-PILOT-AND-ANCHOR.json',
      '8d4e41c9f6db7036cdb72284216b2502def7bbaa54074b793e517c542d8d8db2')
pilots=[(z['prime'],z['scales_mod_p2']) for z in J['rows']]
pilots.append((K['p_c'],K['scales_mod_p2']))
assert [p for p,_ in pilots]==[415721,9807649,6469193]
def bit(x,p):
    a=pow(x%p,(p-1)//2,p)
    assert a in (1,p-1)
    return int(a!=1)
def sx(*t):
    e=f=0
    for a,b in t:e^=a;f^=b
    return e,f
val=0
roots=[]
for p,(_,C1,C2) in pilots:
    sx0=-32*pow(407*C1*C1,-1,p)%p
    tx=pow(2399*C2*C2,-1,p)
    ux=pow(2399,-1,p)
    roots.append([sx0,tx,ux])
assert [[bit(x,p)for x in r]for (p,_),r in zip(pilots,roots)]==[[0,0,0],[1,0,0],[1,0,0]]
assert [[bit(r[i]-r[j],p)for i,j in ((0,1),(0,2),(1,2))]
        for (p,_),r in zip(pilots,roots)]==[[0,0,0],[0,1,1],[1,0,1]]
R=[((0,1),0),((0,2),0),((1,2),0),((0,1,2),1),((0,1,2),2)]
out=[]
for I,mod in R:
    n=len(I); mats=[]
    for i in I:
        p,_=pilots[i]; ss=roots[i]
        for unit0 in (0,1):
            # Keep either own stripped unit bit; this avoids assuming separately that it is +.
            scal={j:((1,unit0) if i==j else (0,bit(ss[i]-ss[j],p))) for j in I}
            D=sx(*scal.values())
            ER=[0,*[ss[j] for j in I]] if mod==0 else ([ss[j] for j in I] if mod==1
                 else [-ss[(j+1)%3]*ss[(j+2)%3] for j in range(3)])
            rr=[((0,0),)*3]
            for j in range(3):
                dd=[sx(D,(0,bit(ER[j]-ER[k],p))) if j!=k else None for k in range(3)]
                dd[j]=sx(dd[(j+1)%3],dd[(j+2)%3])
                rr.append(tuple(dd))
            assert len({tuple(a for a,b in z) for z in rr})==4
            mats.append((p,unit0,scal,set(rr)))
    kept=[]
    for pair in product(range(1<<n),repeat=2):
        tr=(pair[0],pair[1],pair[0]^pair[1])
        if all(tuple(sx(*(scal[j] for k,j in enumerate(I) if g>>k&1)) for g in tr) in im
               for p,unit0,scal,im in mats):
            kept.append(tr)
    if I==(1,2):assert set(kept)=={(0,0,0),(3,2,1),(0,3,3),(3,1,2)}
    out.append({'participating':I,'model':mod,'dimension':len(kept).bit_length()-1,'masks':kept})
assert [z['dimension'] for z in out]==[3,3,2,3,2]
T=2399
assert T%4==3 and all(T%d for d in range(2,isqrt(T)+1))
def mp(a,b):
    r,s=a;t,u=b
    return ((r*t-s*u)%T,(r*u+s*t)%T)
def gp(a,n):
    r=(1,0)
    while n:
        if n&1:r=mp(r,a)
        a=mp(a,a);n>>=1
    return r
norm=lambda a:(a[0]**2+a[1]**2)%T
g=mp((24,10),(pow(26,-1,T),0))
pi=(1387,2132); pi1=mp(pi,g)
assert g==(370,554) and norm(g)==1 and pi1==(1383,287)
assert norm(pi)==norm(pi1)==6469193%T==1489
assert [gp(r,(T*T-1)//4)for r in (pi,pi1)]==[(1,0),(T-1,0)]
assert pow(T,(6469193-1)//4,6469193)==1
gp0=[414772,416672,9813764,9801536]
assert [x%T for x in gp0]==[2144,1645,1854,1621]
assert int(K['new_h_modulus'])%T==1194
for g1,h1,e1 in product(range(4),range(4),range(2)):
    xor=(g1//2)^(h1//2)^(((g1+(-1)**e1*h1)%4)//2)
    assert xor==(((g1%2)^e1)&(h1%2))
print(json.dumps({'actual_roots':roots,'supported_selmer':out,'T':T,'old_count_residues': [x%T for x in gp0],
                  'old_and_new_gaussian_mod_T':[pi,pi1],'norm_one_g':g,'same_norm':norm(pi),
                  'opposite_tame_quartic_signs':[1,-1]},indent=2))
