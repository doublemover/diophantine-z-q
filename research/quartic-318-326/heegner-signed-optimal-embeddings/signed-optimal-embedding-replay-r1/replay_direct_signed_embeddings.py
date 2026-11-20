#!/usr/bin/env python3
"""Independent direct single-discriminant optimal-embedding read at m455,d323."""
from hashlib import sha256
from pathlib import Path
from collections import Counter
from itertools import product
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'paired-prime-surrogate-409-r1'/'eisenstein-replay-r1'))
from eisenstein_representations import order_reps,cross,dot
Q29='aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e'
REF='8d172729d64384eb192e718573a317e691f7f0862a291eacc4248aea22550a64'
def read(p,h):
    raw=Path(p).read_bytes()
    assert sha256(raw).hexdigest()==h
    return json.loads(raw)
book=read(sys.argv[1],Q29);ref=read(sys.argv[2],REF)
p=53;m=455;d=323
D=m*d*d
primes=(17,19)
I=(1,0,0,1)
def madd(A,B):return tuple(u+v for u,v in zip(A,B))
def smul(k,A):return tuple(k*u for u in A)
def mmul(A,B):return tuple(sum(A[2*i+k]*B[2*k+j] for k in range(2)) for i,j in product(range(2),repeat=2))
def mod(A,n):return tuple(a%n for a in A)
def inv(A,n):
    a,b,c,d=A
    return mod(smul(pow((a*d-b*c)%n,-1,n),(d,-b,-c,a)),n)
def leg(u,r):
    v=pow(u%r,(r-1)//2,r)
    return -1 if v==r-1 else v
def matrices(q):
    a,b=next((a,b) for a,b in product(range(q),repeat=2) if (a*a-a*b+b*b+p)%q==0)
    w=(0,-1,1,-1)
    F=(a,b-a,b,-a)
    wbar=mod(smul(-1,madd(I,w)),q)
    assert mod(madd(madd(mmul(w,w),w),I),q)==(0,)*4
    assert mod(mmul(F,F),q)==mod(smul(-p,I),q)
    assert mod(mmul(F,w),q)==mod(mmul(wbar,F),q)
    gamma=mod(mmul(madd(F,smul(-1,I)),inv(madd(I,smul(2,w)),q)),q)
    return (I,w,gamma,mmul(w,gamma))
MM={q:matrices(q) for q in primes}
for q in (16,3):
    MM[q]=[tuple(t for row in M for t in row) for M in book['exact_level_matrices'][str(q)]]
phase0=next(a for a in range(1,p) if (3*a*a-D)%p==0)
RX={}
for sign in (-1,1):RX[sign]=[Counter(),Counter()]
def mat(n,a,v,e):
    return mod(smul(pow(e,-1,n),tuple(sum(u*A[i] for u,A in zip((a,*v),MM[n])) for i in range(4))),n)
def on_line(A,v,n,scalar):
    a,b,c,d=A
    x,y=v
    return ((a-scalar)*x+b*y)%n==0 and (c*x+(d-scalar)*y)%n==0
def local_sign(A,p):
    a,b,c,d=A
    assert mod(mmul(A,A),p)==(0,)*4
    if c:return leg(c,p)
    assert b # A nonzero nilpotent with c=0 has a=d=0.
    return leg(-b,p)
def map_tab(c):
    return [(tuple(r['t16_and_after3']),r['inverse_transport_mark'],r['lambda13_phi0']) for r in c['exact_marks']]
marked_lambda={k:v for cls in book['marked_classes'] for k,_mark,v in map_tab(cls)}
assert len(marked_lambda)==416
nByClass=[]
for cls in book['marked_classes']:
    H=cls['max_order_basis_columns'];e=cls['basis_denominator']
    K=[tuple(H[j][i] for j in range(1,4)) for i in range(1,4)]
    C=(cross(K[1],K[2]),cross(K[2],K[0]),cross(K[0],K[1]))
    dt=dot(K[0],C[0])
    tab=map_tab(cls); seen=Counter(); counts=Counter()
    for v in order_reps(H,e,D):
        dots=[dot(v,r) for r in C]
        assert all(z%dt==0 for z in dots)
        a=sum(H[0][i]* (dots[i-1]//dt) for i in range(1,4))
        b,c,g=v
        ntr=2*a-b-g
        assert ntr%e==0
        tr=ntr//e
        assert tr%2==1
        phi=(3*b+2*c-g)*pow(3*e,-1,p)%p
        assert phi in (phase0,p-phase0)
        sign=1 if phi==phase0 else -1
        U={q:mod(madd(mat(q,a,v,e),smul((1-tr)//2,I)),q) for q in (16,3)}
        s=1 if e==1 else leg(-d,29)
        for q in primes:
            A=mod(madd(smul(2,mat(q,a,v,e)),smul(-tr,I)),q)
            if A==(0,0,0,0):
                break # not optimal
            s*=local_sign(A,q)
        else:
            # Exactly oriented generator Ω_d eigen=1 at level 16 and 3.
            el=[k for k,(c16,c3),l in tab if on_line(U[16],c16,16,1) and on_line(U[3],c3,3,1)]
            if not el and cls["j"]==[0,0]:continue  # one fixed mark rep per automorphism orbit
            assert len(el)==1,(cls["j"],v,U,el)
            k=el[0]
            seen[k]+=1
            RX[sign][(s+1)//2][k]+=1
            counts[sign]+=1
    nByClass.append(dict(j=cls['j'],each53sign=[counts[-1],counts[1]]))
assert all(sum(C.values())==2880 for K in RX.values() for C in K)
ref_halves=(Counter(),Counter())
for c in ref['cases']:
    for r in c['rows']:
        key=tuple(r['t16'][0]+r['t16'][1])
        ref_halves[(r['w']+1)//2][key]+=1

matches=[]
for sign,Z in RX.items():
    for perm in (False,True):
        if all(Z[j]==ref_halves[j^perm] for j in (0,1)):
            matches.append([sign,perm])
assert matches==[[1,False]]
periods=[sum((2*i-1)*n*marked_lambda[k] for i,C in enumerate(RX[s]) for k,n in C.items())%13 for s in (-1,1)]
assert periods==[11,11]
digest=lambda C:sha256(json.dumps(sorted(C.items()),separators=(',',':')).encode('ascii')).hexdigest()
print(json.dumps(dict(
    m=m,d=d,actual_direct_norm=D,phase0=phase0,
    each_class_counts=nByClass,
    marked_half_comparison_matches=matches,
    periods=periods,
    order_of_signs_in_digests=['genus_minus','genus_plus'],
    marked_genus_half_digests={str(s*phase0):[digest(C) for C in RX[s]] for s in (-1,1)},
    independent_full_isogeny_replay_digests=[digest(C) for C in ref_halves],
    total_embedded_each_p53_orientation=[sum(C.values())+sum(D.values()) for C,D in (RX[-1],RX[1])],
    no_classfield_polynomial_evaluated=True),sort_keys=True,indent=2))
