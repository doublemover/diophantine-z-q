#!/usr/bin/env python3
from math import prod, gcd, isqrt
from json import dumps
P=415721
T=(2,3,5,7,11,37,2399)
W=(-1,1,1,-1,1,-1,1)
H=-2207
R=prod(T[4:])
N=prod(T)

def leg(x,l):
    if l == 2:
        return 0 if x%2==0 else (1 if x%8 in (1,7) else -1)
    a=pow(x%l,(l-1)//2,l)
    return -1 if a==l-1 else a

def squarefree(n):
    return all(n%(j*j) for j in range(2,isqrt(n)+1))

fixed=tuple(leg(H,l) for l in T)
assert fixed==(1,1,-1,-1,1,-1,1) and leg(H,P)==1
assert all(fixed[i]==W[i] for i in range(4,7))
assert -prod(fixed)==1 and -prod(W)==1

def admissible_annex(m):
    if m%8!=1 or gcd(m,H*P)>1 or not squarefree(m):
        return
    dd=P*m
    delta=H*dd
    local=tuple(leg(delta,l) for l in T)
    if all(e==1 or (e==0 and l!=2 and c==w)
           for e,l,c,w in zip(local,T,fixed,W)):
        return dict(m=m,d=dd,Delta=delta,tame=list(local))

annex=[x for m in range(1,178,8) if (x:=admissible_annex(m)) is not None]
assert [x['m'] for x in annex]==[113,177]
q=(P,163199081,16990081,17238721)
D=prod(q)
assert D==19871020087852834114214638801 and all(leg(D,l)==1 for l in T)
d=R*D
delta=H*d
assert delta%P==0 and delta%(P*P)!=0 and delta%8==1
assert [leg(delta,l) for l in T]==[1,1,1,1,0,0,0]

def norm_representative(V):
    V%=P
    e=next(e for e in range(2,P) if leg(e,P)==-1)
    # First representative relative to u²=e, whole norm equation exact.
    for y in range(1,P):
        v=(V+e*y*y)%P
        if leg(v,P)==1:
            # Bounded exact lookup only once.
            x=next(x for x in range(1,P) if (x*x-v)%P==0)
            assert (x*x-e*y*y-V)%P==0
            return dict(non_square=e,x=x,y=y,norm=V)

ans=dict(p=P,N=N,level=N*P*P,ordered_tame=list(T),
    atkin=list(W),fixed_twist_char=list(fixed),fixed_twist_char_at_p=leg(H,P),
    new_type_sign_at_p=1,all_three_root_numbers=[1,1,1],
    least_small_positive_twists=annex,
    old_B_failing_candidate=dict(D=D,d=d,Delta=delta,
        residue_norm_only=norm_representative(-(delta//P))))
print(dumps(ans,indent=2))
