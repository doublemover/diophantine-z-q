"""Exact dyadic idealizer for the rank-16 initial finite/reciprocal polynomial orders.
All base operations are polynomial over Z, with bit-packed F2[t] reductions.
Output bases are expressed in original monomial basis, with common denominator 256.
"""
import argparse,itertools,json,time
from functools import lru_cache
from sympy.polys.rings import ring
from sympy import ZZ
from pathlib import Path
A,t=ring("t",ZZ); ZERO=A.zero; ONE=A.one; n=16
def mul2(a,b):
    z=0
    while b:
        if b&1:z^=a
        a<<=1;b>>=1
    return z
def quo2(a,b):
    assert b;q=0
    while a.bit_length()>=b.bit_length():
        k=a.bit_length()-b.bit_length();a^=b<<k;q|=1<<k
    return q
def red(f):return sum(1<<k[0] for k,v in f.items() if v%2)
@lru_cache(None)
def lift(a):return A.from_dict({(i,):1 for i in range(a.bit_length()) if a>>i&1})
def half(f):
    assert all(not (v%2) for v in f.values())
    return A.from_dict({m:v//2 for m,v in f.items()}) if f else ZERO
def scale(f,k):return f*(2**k) if k>=0 else half(f) if k==-1 else half(scale(f,k+1))
def ker(rows):
    """Column Smith-style gcd elimination. Returns log & rank, final tail is saturated kernel."""
    M=[v[:] for v in rows if any(v)]; r=0; ops=[]
    while r<n and r<len(M):
        loc=min(((v.bit_length(),i,j) for i in range(r,len(M)) for j,v in enumerate(M[i]) if j>=r and v),default=None)
        if loc is None:break
        _,i,j=loc
        if i!=r:M[r],M[i]=M[i],M[r]
        def sw(a,b):
            if a!=b:
                for row in M:row[a],row[b]=row[b],row[a]
                ops.append(('s',a,b,0))
        sw(r,j)
        while True:
            restarted=False; piv=M[r][r]
            for i in range(r+1,len(M)):
                v=M[i][r]
                if v:
                    q=quo2(v,piv)
                    if q: M[i]=[a^mul2(q,b) for a,b in zip(M[i],M[r])]
                    if M[i][r]:
                        M[r],M[i]=M[i],M[r];restarted=True;break
            if restarted:continue
            for j in range(r+1,n):
                v=M[r][j]
                if v:
                    q=quo2(v,piv)
                    if q:
                        for row in M:row[j]^=mul2(q,row[r])
                        ops.append(('a',j,r,q))
                    if M[r][j]:
                        sw(r,j);restarted=True;break
            if not restarted:break
        r+=1
    return ops,r
def rec_poly(q):return 1 if not abs(q)%2 else 0
def table0(q,chart):
    b=[0,32,76832,-343]
    f=([v*(t-j) for v,j in zip(q,b)] if chart=='finite' else
       [q[0]*t]+[(q[0]*q[i]//(4**((rec_poly(q[0])+rec_poly(q[i]))//2)))*(1-b[i]*t) for i in range(1,4)])
    fs=[ONE]
    for z in f: fs=fs+[v*z for v in fs]
    return [[[fs[i&j] if k==i^j else ZERO for k in range(n)] for j in range(n)] for i in range(n)]
def transform(T,B,ops):
    for op,i,j,qq in ops:
        if op=='s':
            T[i],T[j]=T[j],T[i];B[i],B[j]=B[j],B[i]
            for row in T:row[i],row[j]=row[j],row[i]
            for row in T:
                for v in row:v[i],v[j]=v[j],v[i]
        else:
            q=lift(qq)
            B[i]=[a+q*b for a,b in zip(B[i],B[j])]
            new=[[a+q*b for a,b in zip(T[i][l],T[j][l])] for l in range(n)]
            new[i]=[a+q*b for a,b in zip(new[i],new[j])]
            for l in range(n):
                T[i][l]=new[l]
                if l!=i:T[l][i]=new[l][:] # no shared editable vector
            for row in T:
                for v in row:v[j]=v[j]-q*v[i]
def frob_rows(T):
    diag=[[red(p) for p in T[i][i]] for i in range(n)]
    rows=[[0]*n for j in range(16*n)]
    for i in range(n):
        v=[int(i==j) for j in range(n)]
        for _ in range(4):
            w=[0]*n
            for j,a in enumerate(v):
                if a:
                    aa=mul2(a,a)
                    for k,b in enumerate(diag[j]):
                        if b:w[k]^=mul2(aa,b)
            v=w
        for k,a in enumerate(v):
            for j in range(a.bit_length()):
                if a>>j&1:rows[16*k+j%16][i]|=1<<(j//16)
    return rows
def run(q,chart,with_table=False):
    assert len(q)==4 and all(isinstance(v,int) and v and v%4!=0 for v in q)
    T=table0(q,chart);B=[[256*ONE if i==j else ZERO for j in range(n)] for i in range(n)]
    record=[]
    while True:
        op,r=ker(frob_rows(T));transform(T,B,op)
        # J=span(2^d_i B_i). J/2J representation of B/2B.
        d=[int(i<r) for i in range(n)]
        rows=[[red(scale(T[i][j][k],d[j]-d[k])) for i in range(n)] for j in range(n) for k in range(n)]
        op2,r2=ker(rows);record.append([n-r,n-r2])
        if r2==n:break
        transform(T,B,op2);k=[-int(i>=r2) for i in range(n)]
        for i in range(n):
            for j in range(n):T[i][j]=[scale(a,k[i]+k[j]-k[l]) for l,a in enumerate(T[i][j])]
            B[i]=[scale(a,k[i]) for a in B[i]]
        assert len(record)<=128 # strict generic lattice growth; index exponent <=8*16
    encode=lambda f:[int(f.get((j,),0)) for j in range(f.degree()+1)] if f else []
    if with_table:return T,B,record
    return {'coefficients':list(q),'chart':chart,'rounds_nilradical_and_enlargement_ranks':record,'basis_numerators_ascending':[[encode(f) for f in v] for v in B], 'denominator':256}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',nargs=4,type=int,default=[1,-1,2,-2]);p.add_argument('--chart',choices=['finite','reciprocal'],default='finite');p.add_argument('--output',required=True)
    args=p.parse_args();a=time.monotonic();r=run(args.q,args.chart)
    Path(args.output).write_text(json.dumps(r,separators=(',',':'))+'\n')
    print(r['coefficients'],r['chart'],r['rounds_nilradical_and_enlargement_ranks'],round(time.monotonic()-a,2),flush=True)
