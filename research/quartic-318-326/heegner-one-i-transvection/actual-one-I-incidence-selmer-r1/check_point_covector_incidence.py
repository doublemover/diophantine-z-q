#!/usr/bin/env python3
"""Exact F13 incidence, local orbits, and original point-field covector resolvent canary."""
import itertools,json
p=13
V=[(a,b) for a in range(p) for b in range(p) if a or b]
L=[(1,t) for t in range(p)]+[(0,1)]
def pair(c,v):return (c[0]*v[0]+c[1]*v[1])%p
def rank(M):
    M=[[v%p for v in r] for r in M]
    if not M:return 0
    n=0
    for j in range(len(M[0])):
        k=next((i for i in range(n,len(M)) if M[i][j]),None)
        if k is None:continue
        M[k],M[n]=M[n],M[k]
        row=[z*pow(M[n][j],-1,p)%p for z in M[n]]
        for i in range(n+1,len(M)):
            z=M[i][j]
            if z:M[i]=[(a-z*b)%p for a,b in zip(M[i],row)]
        n+=1
        if n==len(M):return n
    return n
def mul(M,a):
    return [sum(v*w for v,w in zip(r,a))%p for r in M]
M=[[pow(pair(c,v),11,p) for v in L] for c in L]
linear=[[v[i] for v in L] for i in range(2)]
assert rank(M)==12 and rank(linear)==2
assert all(mul(M,z)==[0]*14 for z in linear)
MT=[list(a) for a in zip(*M)]
assert all(mul(MT,z)==[0]*14 for z in linear)
ranks={k:rank([[pow(pair(c,v),12-k,p) for v in L] for c in L]) for k in range(1,12)}
assert ranks=={k:13-k for k in range(1,12)}
# Test the literal affine-hyperplane sum with all 13 fibres; this
# confirms the power exponent is -1, not +1, on the actual action.
def scalar_basis(v,k):
    if v[0]:return (v[0],(v[1]*pow(v[0],-1,p))%p)
    return (v[1],13)
for c in L:
    row=[0]*14
    for v in V:
        if pair(c,v)==1:
            z,i=scalar_basis(v,1); row[i]=(row[i]+z)%p
    assert row==M[L.index(c)]
    assert sum(pair(c,v)==1 for v in V)==13

def point(g,v):
    a,b,d=g;x,y=v
    return (a*x+b*y)%p,d*y%p
def covector(g,v):
    a,b,d=g;x,y=v
    z=x*pow(a,-1,p)%p
    return z,(y-z*b)*pow(d,-1,p)%p
Inertia=[(a,b,1) for a in range(1,p) for b in range(p)]
Borel=[(a,b,d) for a in range(1,p) for b in range(p) for d in range(1,p)]
def orb_data(act):
    S=set(V);rows=[]
    while S:
        v=min(S)
        X={act(g,v) for g in Borel}
        e=len({act(g,v) for g in Inertia})
        assert S>=X and len(X)%e==0
        S-=X;rows.append([e,len(X)//e])
    return sorted(rows)
ev=orb_data(point);ec=orb_data(covector)
assert ev==[[12,1],[13,12]]
assert ec==[[1,12],[156,1]]
# 53 has nonscalar unipotent Frobenius. Check the point/covector
# coinvariant dimensions and rank of J on these exact unramified slots.
def word_matrix(f,k):
    A=[]
    for v in L:
        a,j=scalar_basis(f(v),1)
        r=[0]*14;r[j]=pow(a,k,p);A.append(r)
    return A
def mm(A,B):
    return [[sum(x*y for x,y in zip(a,b))%p for b in zip(*B)] for a in A]
gx=word_matrix(lambda v:((v[0]-v[1])%p,v[1]),1)
gy=word_matrix(lambda c:(c[0],(c[0]+c[1])%p),11)
assert mm(M,gx)==mm(gy,M)
def minus_id(A):
    return [[x-(i==j) for j,x in enumerate(row)] for i,row in enumerate(A)]
dx,dy=minus_id(gx),minus_id(gy)
assert rank(dx)==rank(dy)==12
ir=rank([a+b for a,b in zip(M,dy)])-rank(dy)
kr=rank([a+list(b) for a,b in zip(dx,L)])-rank(dx)
assert ir==kr==1
# The members of the original degree-one orbit give all distinct W.
q=53; d=2811626664334219040035976315; P=(36,22)
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u and (y+v)%q==0:return None
    a=(3*x*x+4*d*x-3*d*d)*pow(2*y,-1,q) if x==u else (v-y)*pow(u-x,-1,q)
    a%=q
    z=(a*a-2*d-x-u)%q
    return z,(a*(x-z)-y)%q
W=[];Q=None
for _ in range(12):
    Q=add(P,Q); assert Q is not None
    x,y=Q;assert (y*y-x*(x-d)*(x+3*d))%q==0
    W.append(169*y*pow(d,-1,q)%q)
assert add(P,Q) is None and len(set(W))==12
z=16
assert pow(z,13,q)==1 and z!=1
Z=[sum(Wa*pow(z,(i+1)*b,q) for i,Wa in enumerate(W))%q for b in range(1,13)]
assert len(set(Z))==11  # one reduction collision; no local monogenic claim
print(json.dumps(dict(d=d,actual_formal_ordinary_local_point_orbits=ev,
    actual_formal_ordinary_local_covector_orbits=ec,weight_k_hyperplane_ranks=ranks,
    linear_kernel_and_dual_cokernel_dimension=2,weight1_J=M,
    actual_53_unramified_point_covector_coinvariant_dimensions=[14-rank(dx),14-rank(dy)],
    actual_53_unramified_incidence_and_point_image_ranks=[ir,kr],
    original_W_scaling_values_mod53=W,primitive_root_mod53=z,gauss_resolvent_conjugates_mod53=Z,
    gauss_resolvent_distinct_reductions_mod53=len(set(Z))),sort_keys=True,indent=2))
