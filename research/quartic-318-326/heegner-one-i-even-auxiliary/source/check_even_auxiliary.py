#!/usr/bin/env python3
"""Independent-input verification of the fixed arithmetic Cassels witness. No dependencies."""
from fractions import Fraction as Q
from itertools import product
from math import gcd,isqrt,prod
from pathlib import Path
import json

W=json.loads(Path(__file__).with_name("EXACT-EVEN-AUXILIARY.json").read_text())
d,m,beta=(W[k] for k in ("d","m","beta"))
old,mp=(W[k] for k in ("old_primes","m_primes"))
S=[-1,2,3,*sorted(old+mp)]
D=d*m
roots=(0,-D,3*D)
assert W["twist"]==-D and d==prod(old) and m==prod(mp)
assert beta==prod(old[:-2]) and old[-2:]==[114649,119851] and d%24==11
assert len(set(S))==len(S) and all(not any(p%l==0 for l in range(2,isqrt(p)+1)) for p in S[1:])

def leg(a,p):
    s=pow(a%p,(p-1)//2,p)
    return -1 if s==p-1 else s

assert m%24==23 and 53 not in S and leg(-m,53)==-1
assert all(leg(-m,p)==1 for p in old)

def va(x,p):
    assert x
    x=Q(x);u,v=x.numerator,x.denominator;r=0
    while u%p==0:u//=p;r+=1
    while v%p==0:v//=p;r-=1
    return r

def ut(x,p,k):
    y=Q(x)/Q(p)**va(x,p)
    return y.numerator*pow(y.denominator,-1,p**k)%p**k

def square_class(x,p):
    if p==-1:return int(x<0)
    v=va(x,p)%2
    if p==2:return v|({1:0,7:1,5:2,3:3}[ut(x,p,3)]<<1)
    return v|((leg(ut(x,p,1),p)==-1)<<1)

def width(p):
    return {-1:1,2:3}.get(p,2)

def local_restr(pair,p):
    return square_class(pair[0],p)|(square_class(pair[1],p)<<width(p))

def k3(x):
    return tuple(x-e if x!=e else prod(x-z for z in roots if z!=e) for e in roots)

def insert(B,j):
    while j:
        i=j.bit_length()-1
        if i in B:j^=B[i]
        else:B[i]=j;return True
    return False

def disc_set(x):
    xp=int(x)
    assert xp and xp==x
    t=0
    for j,p in enumerate(S):
        if p==-1:
            if xp<0:xp=-xp;t^=1
        else:
            while xp%p==0:xp//=p;t^=1<<j
    assert xp==1
    return t

def as_bits(x,y):
    return disc_set(x)|(disc_set(y)<<len(S))

assert [p["p"] for p in W["local_kummer_rows"]]==S
global_obstructions={}
for row in W["local_kummer_rows"]:
    p=row["p"];h=width(p)
    B={}
    for x_num,x_den,encoded in row["witnesses"]:
        x=Q(x_num,x_den)
        a,b,c=k3(x)
        if x not in roots:assert square_class(a*b*c,p)==0
        assert encoded==local_restr((a,b),p)
        assert insert(B,encoded)
    assert len(B)==h
    for functional in range(1,1<<(2*h)):
        if any((functional&b).bit_count()%2 for b in B.values()):continue
        r=sum(1<<(i*len(S)+j) for i,j in product(range(2),range(len(S)))
              if (functional&(square_class(S[j],p)<<(i*h))).bit_count()%2)
        insert(global_obstructions,r)
assert 2*len(S)-len(global_obstructions)==4
L,R=W['cassels_left'],W['cassels_right']
assert L==[L[0],1,L[0]] and R==[R[0],1,R[0]]
tors=[k3(x) for x in roots[:2]]
B={}
for x,y,z in [*tors,L,R]:
    v=as_bits(x,y)
    assert disc_set(x*y*z)==0
    assert all((v&r).bit_count()%2==0 for r in global_obstructions.values())
    assert insert(B,v)
assert len(B)==4

# Uniform dyadic / triadic first-coordinate lower bound for the actual isogeny.
# J_d has roots 0,d,9d. Order/even labels of its two first coordinates squareclasses.
for p,xs,expected in [(2,[d,-3],[6,4]),(3,[d,3],[2,1])]:
    got=[]
    for x in xs:
        fs=[x-y if x!=y else prod(x-z for z in [0,d,9*d] if z!=x) for y in [0,d,9*d]]
        if x not in [0,d,9*d]:assert square_class(prod(fs),p)==0
        got.append(square_class(fs[0],p))
    assert got==expected
    B={}
    assert all(insert(B,t) for t in got)

def local_sqrt(value,p,k):
    # Pick least nonnegative residue root and lift by a completely exact integer recurrence.
    v=va(value,p)
    assert v%2==0 and square_class(value,p)==0
    u=ut(value,p,k)
    if p==2:
        r=1
        for j in range(3,k):
            if ((r*r-u)>>j)&1:r+=1<<(j-1)
    else:
        r=next(i for i in range(p) if (i*i-u)%p==0)
        mod=p;iv=pow(2*r,-1,p)
        for j in range(1,k):
            r+=mod*((u-r*r)//mod*iv%p)
            mod*=p
    assert (r*r-u)%p**k==0
    q=r*Q(p)**(v//2)
    err=va(q*q-value,p) if q*q!=value else 10**9
    slope=va(2*q,p)
    assert err>2*slope
    return q,err-slope

def hilbert(x,y,p):
    a,b=va(x,p),va(y,p)
    if p==2:
        u,v=ut(x,p,3),ut(y,p,3)
        e=(u-1)*(v-1)//4+a*(v*v-1)//8+b*(u*u-1)//8
        return (-1)**(e%2)
    return (-1)**((a*b*((p-1)//2))%2)*leg(ut(x,p,1),p)**(b%2)*leg(ut(y,p,1),p)**(a%2)

a=L[0];g=R[0]
A,B,C=W["tangent_seed"]
assert a*A*A+D*C*C==B*B and gcd(A,gcd(B,C))==1
negative=[]
output_rows=[]
assert [r[0] for r in W["cassels_rows"]]==S
for word in W["cassels_rows"]:
    p,sg=word[:2]
    if len(word)==2:
        assert sg==1 and square_class(g,p)==0
        continue
    signs,read,coords=word[2:]
    x=Q(*coords)
    assert len(signs)==3 and set(signs)<={-1,1}
    zs,accuracy=zip(*(local_sqrt((x-e)/r,p,72 if p<=3 else 18) for e,r in zip(roots,L)))
    z1,z2,z3=(s*z for s,z in zip(signs,zs))
    f1=a*A*z3-B*z2+2*D*C
    f3=a*A*z1-B*z2+D*C
    acc1=min(va(a*A,p)+accuracy[2],va(B,p)+accuracy[1])
    acc3=min(va(a*A,p)+accuracy[0],va(B,p)+accuracy[1])
    k=3 if p==2 else 1
    assert min(acc1-va(f1,p),acc3-va(f3,p))>=k
    assert read==[va(f1,p),ut(f1,p,k),va(f3,p),ut(f3,p,k)]
    assert sg==hilbert(f1,g,p)*hilbert(f3,g,p)
    output_rows.append([p,*read,sg])
    if sg==-1:negative.append(p)
assert negative==[2,5,733] and prod(r[1] for r in W["cassels_rows"])==W["cassels_symbol"]==-1
print(json.dumps(dict(d=d,m=m,twist=-D,old_split_primes=old,ell53=-1,global_rows=len(global_obstructions),
                      selmer_dimension=4,cassels_basis=[L,R],tangent_seed=W["tangent_seed"],
                      cassels_rows=output_rows,cassels_symbol=-1,cassels_negative_places=negative),sort_keys=True,indent=2))
