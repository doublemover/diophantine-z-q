"""Exact stdlib F2 local Kummer and Cassels-rank input for E_{-3N}."""
from math import prod

B=(17,409,2857,3673,6121,6529); H=(131,577,1367,9133)
beta,theta=prod(B),prod(H);N=beta*theta
S=(-1,2,3)+B+H
roots=(0,9*N,-3*N)
def cl(x,p):
    if p==0:return int(x<0)
    assert x
    v=0
    while x%p==0:x//=p;v^=1
    if p==2:return 4*v+2*(x%8 in (3,5))+(x%4==3)
    return 2*v+(pow(x%p,(p-1)//2,p)!=1)
def spans(vectors):
    V={0}
    for x in vectors:V|={a^x for a in V}
    return V
def pivots(rows):
    R={}
    for a in rows:
        while a:
            i=a.bit_length()-1
            if i not in R:R[i]=a;break
            a^=R[i]
    return R
def rep(v,j):return prod(t for i,t in enumerate(S) if v>>(i+j*len(S))&1)
def kernel(rows,n):
    R=pivots(rows);L=[]
    for i in range(n):
        if i in R:continue
        v=1<<i
        for j,a in sorted(R.items()):
            if (v&a).bit_count()%2:v^=1<<j
        assert all((a&v).bit_count()%2==0 for a in rows);L.append(v)
    return L
def run():
    rows=[];loc={}
    for p in [0]+list(S[1:]):
        k=1 if not p else (3 if p==2 else 2)
        pairs=[(-27*N*N,-9*N),(9*N,108*N*N)] if p else [(-27*N*N,-9*N)]
        if p==2:
            x=-12
            assert cl(prod(x-o for o in roots),p)==0
            pairs+=[(x,x-roots[1])]
        V=spans([cl(x,p)|(cl(y,p)<<k) for x,y in pairs])
        assert len(V)==2**k   # all from E(Qp); full local cardinal by [2] index
        def chi(t):return [(t&a).bit_count()%2 for a in V]
        ann=[t for t in range(1<<(2*k)) if not any(chi(t))]
        columns=[cl(x,p)<<(k*j) for j in range(2) for x in S]
        for t in ann:rows.append(sum((((t&x).bit_count()%2)<<i) for i,x in enumerate(columns)))
        loc[p]=sorted(V)
    n=2*len(S);L=kernel(rows,n)
    assert n==26 and len(pivots(rows))==22 and len(L)==4
    basis=[(rep(v,0),rep(v,1)) for v in L]
    assert basis==[(-3,-N),(17,3*(N//17)),(beta//17,N//17),(theta,1)]
    represented={(rep(v,0),rep(v,1)) for v in spans(L)}
    assert (beta,3) in represented and (-51,-51) in represented
    return dict(columns=n,constraint_rank=22,selmer_dimension=4,global_basis=basis)
if __name__=='__main__':print(run())
