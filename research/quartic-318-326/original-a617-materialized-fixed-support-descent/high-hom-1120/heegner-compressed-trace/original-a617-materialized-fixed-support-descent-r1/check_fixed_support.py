"""Literal a617: finite necessary Kummer space on fixed bad support and theta aggregate."""
from fractions import Fraction as F
from pathlib import Path
from math import prod,gcd,isqrt
import json, hashlib
here=Path(__file__).resolve().parent
at=here.parent/'original-a617-numeric-reconstruction-r2'/'EXACT-ROOT-SIGN.json'
assert hashlib.sha256(at.read_bytes()).hexdigest()=='c5093c42d1aace2def0059e75b46150540245fb86a3c6194e60d3b91b46aa36f'
root=json.loads(at.read_text())
rr={r['p']:r for r in root['finite_places']}
P=sorted(rr); S=[-1,2]+P
u,w=368900221027188880,362538667625927811
be=199477972060937362209233596181078921
z=F(u,w); M=z*z+2; Q2=z*z-40*z-32; C3=7*z**3+16*z*z+32*z+32
e=-8*z*z*(z+4)*M*C3/9
f=-2*z*z*(z-4)*(z+4)*M*Q2/9

def vp(q,p):
    q=F(q);a,b=q.numerator,q.denominator
    assert a
    d=0
    while a%p==0:d+=1;a//=p
    while b%p==0:d-=1;b//=p
    return d

def cls(q,p):
    v=vp(q,p); r=q/F(p)**v
    mod=8 if p==2 else p
    t=r.numerator*pow(r.denominator,-1,mod)%mod
    return ((v&1) ^ ({1:0,7:2,5:4,3:6}[t] if p==2 else (2 if pow(t,(p-1)//2,p)==p-1 else 0)))

def repspan(v):
    s={0}
    for x in v:s|={y^x for y in s}
    return s

def parity(x):return x.bit_count()&1

def tors(E,F,p):
    return [[E*F,-E,-F],[E,E*(E-F),E-F],[F,F-E,F*(F-E)]]

def vals(v,p,bits):
    ans=[cls(z,p) for z in v]
    assert ans[0]^ans[1]^ans[2]==0
    return ans[0] | (ans[1]<<bits)

def local(p):
    dim=3 if p==2 else 2
    moddepth=min(vp(e,p),vp(f,p),vp(e-f,p)); scale=F(p)**(2*(moddepth//2))
    tau=1 if p==2 else rr[p]['delta']
    E,F0=tau*e/scale,tau*f/scale
    rs=[F(0),E,F0]
    seen={0}; exact=[]
    def use(v,name):
        c=vals(v,p,dim)
        if c not in seen:
            seen.update({s^c for s in seen}); exact.append((name,c))
    for t,q in enumerate(tors(E,F0,p)):use(q,['T0','Te','Tf'][t])
    depth=max(vp(x-y,p) for i,x in enumerate(rs) for y in rs[:i]); assert depth>=0
    candidates=[]
    if len(seen)<(1<<dim):
        for a in range(1,66):candidates.append((F(a),f'x={a}'))
        for k in range(-4,depth+6):
            for j,R in enumerate(rs):
                for a in range(1,33):
                    if a%p:candidates.append((R+F(p)**k*a,f'x=root{j}+{a}*p^{k}'))
    for x,desc in candidates:
        if len(seen)==(1<<dim):break
        q=[x-R for R in rs]
        if 0 in q:continue
        if cls(prod(q),p):continue
        use(q,desc)
    assert len(seen)==(1<<dim),(p,exact,seen)
    return dim,sorted(seen),exact

def nullspace(rows,n):
    pp={}
    for x in rows:
        while x:
            j=x.bit_length()-1
            if j not in pp:pp[j]=x;break
            x^=pp[j]
    basis=[]
    for k in range(n):
        if k in pp:continue
        v=1<<k
        for j in sorted(pp):
            if parity(v&pp[j]):v|=1<<j
        assert all(not parity(v&x) for x in rows)
        basis.append(v)
    return basis

def decode(v):
    m=len(S);d=lambda q:prod(p for i,p in enumerate(S) if (q>>i)&1)
    a,b=v&((1<<m)-1), v>>m
    return [d(a),d(b),d(a^b)]

assert root['global_sign']==-1 and all(rr[p]['delta'] for p in P)
rows=[]; data={}
for p in [2]+P:
    dim,sub,wit=local(p)
    data[p]=[sub,wit]
    cols=[cls(q,p) for q in S]
    cols=cols+[t<<dim for t in cols]
    for c in range(1,1<<(2*dim)):
        if any(parity(t&c) for t in sub):continue
        rows.append(sum(1<<j for j,q in enumerate(cols) if parity(q&c)))
# e<f<0, beta,delta positive: sign pattern (+,+,+) or (-,+,-).
assert e<f<0
rows.append(1<<len(S))
before=nullspace(rows,2*len(S))
a=sum((1<<j) for j,p in enumerate(S) if p>2 and rr[p]['delta_character']==-1)
rows.extend([a,a<<len(S)])
after=nullspace(rows,2*len(S))
assert len(before)==len(after)==3 and before==after
a,b,c=map(decode,after)
assert c==[1,be,be] and a[0]<0 and b[0]>1
classes=lambda v:[q for q in S if (q==-1 and v<0) or (q>1 and v%q==0)]
pair=lambda u,v:u*v//gcd(u,v)**2
pairs=[a,b,[pair(x,y) for x,y in zip(a,b)]]
norms=[]
for B,l,wit in zip(pairs,(27953,8377,12457),(47,17,17)):
    x,y,xy=B
    assert l%8==1 and l not in S and all(l%q for q in range(2,isqrt(l)+1))
    leg=lambda t,p:pow(t%p,(p-1)//2,p)==1
    assert leg(x,l) and leg(y,l)
    assert all(leg(l,p)==(rr[p]['delta_character']>0) for p in P if x*y%p==0)
    i,j=cls(x,wit),cls(y,wit)
    assert i and j and i!=j
    norms.append(dict(triple=B,factor_support=list(map(classes,B)),q=l,full_local_v4_prime=wit,classes_at_v4=[i,j]))
efp=[p for p in P if vp(e*f,p)&1]
efrep=prod(efp); g=F(e*f)/efrep
assert g>0 and isqrt(g.numerator)**2==g.numerator and isqrt(g.denominator)**2==g.denominator
assert prod(rr[p]['delta_character'] for p in efp)==-1
assert rr[47]['delta_character']==-1 and vp(e,47)==0 and vp(f,47)==1
print(json.dumps(dict(fixed_support=S,local_witness=data,fixed_basis=list(map(decode,before)),aggregate_basis=list(map(decode,after)),
  fixed_dim=len(before),aggregate_dim=len(after),aggregate_rows=[sum((1<<j) for j,p in enumerate(S) if p>2 and rr[p]['delta_character']==-1)*2**k for k in (0,len(S))],
  norm_receivers=norms,pure_second_outside_theta_aggregate=dict(discriminant_repr=efrep,odd_factor_support=efp,
    nonsquare_theta=[p for p in efp if rr[p]['delta_character']==-1],jacobi=-1,local_rejection_p=47)),
    indent=2,sort_keys=True))
