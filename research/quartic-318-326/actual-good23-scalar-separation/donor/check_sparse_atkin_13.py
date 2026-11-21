#!/usr/bin/env python3
"""Exact actual endomorphism circuit for quotient-invariant values at p=13."""
import argparse,json
from itertools import product,permutations
from math import isqrt,prod

P=13;PS=(2,3,5,7,11,37,2399); M=251895
W=(-1,1,1,-1,1,-1,1)
W1=(1,-1,-1,-1,1,-1,1)

def f(x):return (x%P,0)
def a(x,y):return ((x[0]+y[0])%P,(x[1]+y[1])%P)
def n(x):return (-x[0]%P,-x[1]%P)
def b(x,y):return a(x,n(y))
def m(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P)
def pw(x,i):
    t=f(1)
    while i:
        if i&1:t=m(t,x)
        x=m(x,x);i//=2
    return t
def d(x,y):
    assert y!=f(0)
    return m(x,pw(y,P*P-2))

def ecount(p,A,B):return p+1+sum(0 if (v:=(x**3+A*x+B)%p)==0 else (1 if pow(v,(p-1)//2,p)==1 else -1) for x in range(p))

def velu_setup(u,s):
    A=f(-35);B=f(-98)
    assert a(a(pw(u,3),m(A,u)),B)==f(0)
    aa=m(f(3),u);bb=a(m(f(3),pw(u,2)),A)
    aa1=m(f(-2),aa);bb1=b(pw(aa,2),m(f(4),bb))
    Aq=b(bb1,d(pw(aa1,2),f(3)))
    Bq=b(d(m(f(2),pw(aa1,3)),f(27)),d(m(aa1,bb1),f(3)))
    assert Aq==m(A,pw(s,4)) and Bq==m(B,pw(s,6))
    return [[Aq,Bq],a(s,d(f(2),s))]
DG=(7,2);DJ=(0,5);DH=m(DG,DJ)
DB=(f(1),DG,DJ,DH)

def Nq(q):
    r,s,t,u=q; return ((2*r+s+u)**2+7*s*s+2*(2*t+u)**2-2*s*(2*t+u)+13*u*u)//4

def dq(q):
    R=f(0)
    for z,v in zip(q,DB):R=a(R,m(f(z),v))
    assert m(R,pw(R,P))==f(Nq(q))
    return R

def nm(v,trzero=False):
    out=[]
    for u in range(-isqrt(8*v//26),isqrt(8*v//26)+1):
        A=8*v-26*u*u
        for s in range(-isqrt(A//13),isqrt(A//13)+1):
            B=A-13*s*s
            for g in ([0] if trzero else range(-isqrt(B//2),isqrt(B//2)+1)):
                if (g-s-u)%2:continue
                C=B-2*g*g
                k=isqrt(C)
                if k*k!=C:continue
                for k0 in ({k,-k} if k else {0}):
                    if (k0+s)%2:continue
                    vv=(k0+s)//2
                    if (vv-u)%2: continue
                    q=((g-s-u)//2,s,(vv-u)//2,u)
                    if q>tuple(-z for z in q):
                        assert Nq(q)==v
                        out.append(q)
    return sorted(out)

def mat(p):
    squares={}
    for x in range(p):squares.setdefault(x*x%p,x)
    for c in range(p):
        if p==2:
            sol=[a for a in range(2) if (a*(1-a)-c*(1+2*c)-2)%p==0]
            if not sol:continue
            A=sol[0]
        else:
            u=(-7-4*c-8*c*c)%p
            if u not in squares:continue
            A=(1+squares[u])*pow(2,-1,p)%p
        B=(1+2*c)%p;D=(1-A)%p
        assert (A*D-B*c)%p==2%p
        J=(0,-2%p,1,0);G=(A,B,c,D);GH=(B,-2*A%p,D,-2*c%p)
        return (1,0,0,1),G,J,GH
    raise AssertionError('no local frame')

def det4(R):
    return sum((-1)**sum(t[i]>t[j] for i in range(4) for j in range(i+1,4))*
               prod(R[i][t[i]] for i in range(4)) for t in permutations(range(4)))

MF={q:mat(q) for q in PS}
assert all(det4(MF[q])%q for q in PS)
def act(q,p):
    R=tuple(sum(v*B[j] for v,B in zip(q,MF[p]))%p for j in range(4))
    assert (R[0]*R[3]-R[1]*R[2])%p==Nq(q)%p
    return R

def lines(M,p,t,shift=0):
    aa,bb,cc,dd=M;aa=(aa-shift)%p;dd=(dd-shift)%p
    if t==p: return bb,dd
    return (aa+bb*t)%p,(cc+dd*t)%p

def kernel(M,p,shift=0):
    aa,bb,cc,dd=M;aa=(aa-shift)%p;dd=(dd-shift)%p
    if bb==0 and dd==0:
        assert aa or cc
        return p
    t=((-aa*pow(bb,-1,p)) if bb else (-cc*pow(dd,-1,p)))%p
    assert lines(M,p,t,shift)==(0,0)
    return t

def moved(M,p,t):
    a,b=lines(M,p,t)
    if a==0:
        assert b
        return p
    return b*pow(a,-1,p)%p

def initial():
    qs=nm(M,True)
    alpha=min(qs,key=lambda q:(sum(abs(v) for v in q),q))
    assert 2*alpha[0]+alpha[1]+alpha[3]==0
    A=tuple(act(alpha,p) for p in PS)
    frame=[]
    for p,op in zip(PS,A):
        if p==2:
            good=[v for v in range(p+1) if moved(op,p,v)==v]
            frame.append(min(good))
        elif M%p==0:frame.append(kernel(op,p))
        else:frame.append(kernel(op,p,4 if p==11 else 1))
    return alpha,tuple(frame),len(qs)

def build():
    T=[]
    for i,p in enumerate(PS):
        R={}
        for q in nm(p):
            K=kernel(act(q,p),p)
            assert K not in R
            R[K]=(dq(q),tuple(act(q,t) for t in PS))
        assert len(R)==p+1
        T.append(R)
    return T

def image(M,p):
    a,b,c,d=M
    t=(a,c) if a or c else (b,d)
    assert t!=(0,0)
    return p if t[0]==0 else t[1]*pow(t[0],-1,p)%p

def evaluate(frame,T):
    S=[(f(1),tuple(frame))]
    for i,p in enumerate(PS):
        R=[]
        for c,vals in S:
            di,A=T[i][vals[i]]
            V=tuple(image(A[j],ell) if j==i else moved(A[j],ell,vals[j]) for j,ell in enumerate(PS))
            R.append((m(c,di),V))
        S.extend(R)
    assert len(S)==128
    Ds=[pw(a,12) for a,_ in S]
    assert all(pw(u,14)==f(1) for u in Ds)
    return Ds,min(vals for _,vals in S),[a for a,_ in S]

def char(w,k):
    return prod(c for i,c in enumerate(w) if k>>i&1)

def invariants(Ds):
    # In k^×, 12th powers have order 14. Explicit normalized residual
    # logarithms, then all discriminant products.
    roots=[z for z in product(range(P),repeat=2) if pw(z,14)==f(1)]
    g=next(z for z in roots if pw(z,7)!=f(1) and pw(z,2)!=f(1))
    table={pw(g,j):j for j in range(14)}
    E=[table[u] for u in Ds]
    # Walsh spectrum; index-mask is the set of negative prime signs.
    for i in range(7):
        for j in range(128):
            if j>>i&1:continue
            x=E[j];y=E[j+(1<<i)]
            E[j]=(x+y)%14;E[j+(1<<i)]=(x-y)%14
    U=[pw(g,n) for n in E]
    assert all(pw(z,7)==f(1) for z in U)
    B=[a(pw(z,2),pw(z,12)) for z in U]
    assert all(t[1]==0 for t in B)
    return [t[0] for t in B], U, tuple(E)

def extra_weight4(ds):
    roots=[z for z in product(range(P),repeat=2) if pw(z,42)==f(1)]
    g=next(z for z in roots if all(pw(z,42//r)!=f(1) for r in (2,3,7)))
    L={pw(g,j):j for j in range(42)}
    E=[L[pw(u,4)] for u in ds]
    for i in range(7):
        for j in range(128):
            if j>>i&1:continue
            x=E[j];y=E[j+(1<<i)]
            E[j]=(x+y)%42;E[j+(1<<i)]=(x-y)%42
    # Normalize the singleton exactly: analytic lambda^(-4*32) times
    # E4 product equals lambda^(4*32) times our quotient differential product.
    U=[m(pw(g,e),pw(f(PS[i.bit_length()-1]),128)) if i.bit_count()==1 else pw(g,e)
       for i,e in enumerate(E)]
    assert all(pw(z,21)==f(1) for z in U)
    return [a(pw(z,2),pw(z,40)) for z in U]

def ib(w):return sum(1<<i for i,t in enumerate(w) if t==-1)

def main():
    pa=argparse.ArgumentParser()
    pa.add_argument('--full-last-slot',action='store_true')
    args=pa.parse_args()
    Id=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
    gram=tuple(tuple(Nq(tuple(a+b for a,b in zip(x,y)))-Nq(x)-Nq(y) for y in Id) for x in Id)
    assert det4(gram)==13**2
    assert ecount(13,-35,-98)==14
    vG=velu_setup((3,2),DG);vJ=velu_setup((7,0),DJ)
    assert vG[1]==f(1) and vJ[1]==f(0) and a(DH,d(f(4),DH))==f(1)
    alpha,frame,n_alpha=initial()
    T=build()
    rows=[]
    Wkeys={}
    Urows={}
    Drows={}
    top=2400 if args.full_last_slot else 16
    for i in [frame[-1]]+[j for j in range(top) if j!=frame[-1]]:
        fr=frame[:-1]+(i,)
        D,key,dd=evaluate(fr,T)
        Drows[i]=dd
        B,U,E=invariants(D)
        Urows[i]=(U,E)
        Wkeys[i]=key
        if fr==frame:
            # Independent consequence of W_m fixed and the character signs.
            assert all(U[j]==f(1) and B[j]==2 for j in range(1,128)
                if char(tuple(-1 if j>>k&1 else 1 for k in range(7)),
                        sum(1<<k for k,p in enumerate(PS) if M%p==0))==-1
                and j.bit_count()>=2)
        assert B[ib(W)]!=0 # actually any U with U^7=1 gives a nonzero B.
        t=(B[ib(W1)]*pow(B[ib(W)],-1,P)-1)*pow(96,-1,P)%P
        rows.append((i,t,B))
    use=list(range(1,128))
    if args.full_last_slot:
        bundles={}
        for i,t,B in rows:
            key=tuple(B[j] for j in use)
            bundles.setdefault(key,[]).append(i)
        alias=[[i for i in L] for L in bundles.values() if len({Wkeys[i] for i in L})>1]
        lookup={i:B for i,t,B in rows}
        Vpair={}
        iw=ib(W);iw2=iw^1
        for i in lookup:
            U=Urows[i][0]
            Vpair[i]=tuple(a(U[k],pw(U[k],13))[0] for k in (iw,iw2))
        full_pair_buckets={}
        for i,j in Vpair.items():full_pair_buckets.setdefault(j,[]).append(i)
        E4_controls=[[L,[[i,extra_weight4(Drows[i])] for i in L]] for L in alias]
        D4=[]
        for L,C in E4_controls:
            EQ=[j for j in range(1,128) if len({r[j] for i,r in C})==len(C)]
            D4.append((L,len(EQ),EQ[:8],[[i,[r[j] for j in EQ[:1]]] for i,r in C]))

        def gauge(i):
            E=Urows[i][1]
            return min(tuple((-x if (g&j).bit_count()%2 else x)%14 for j,x in enumerate(E)) for g in range(128))
        still_alias=[]
        triple_marks=[]
        for L in alias:
            gs=[gauge(i) for i in L]
            if len(set(gs))<len(gs):
                still_alias.append(L)
                continue
            assert len(L)==2
            i1,i2=L
            us=[Urows[i1][0],Urows[i2][0]]
            Ds=[[b(x,pw(x,13)) for x in u] for u in us]
            for i in range(1,128):
                for j in range(i+1,128):
                    k=i^j
                    data=[m(m(D[i],D[j]),D[k]) for D in Ds]
                    if data[0]!=data[1]:break
                else:continue
                break
            else:
                continue
            triple_marks.append([L,[i,j,k],data])

        chosen=[]
        role=list(lookup)
        while len({tuple(lookup[i][k] for k in chosen) for i in role})<len(bundles):
            k=max(use,key=lambda j:len({tuple(lookup[i][k] for k in (*chosen,j)) for i in role}))
            chosen.append(k);use.remove(k)
        # output only a SHA over ALL exact quotient rows, plus numerical controls
        import hashlib
        def role_rows(i):
            return [i,*Wkeys[i],*lookup[i]]
        h=hashlib.sha256(''.join(','.join(map(str,role_rows(i)))+'\n' for i in sorted(role)).encode()).hexdigest()
        print(json.dumps({'raw_slice_count':len(rows),'actual_W_orbits':len(set(Wkeys.values())),
          'all_character_tuples':len(bundles),'different_W_orbit_aliases':alias,
          'greedy_separating_full_slice_masks':chosen, 'true_U_gauge_aliases':still_alias,
           'first_distinguishing_invariant_triples':triple_marks,
          'exact_c4_invariant_tests_on_all_Delta_aliases':D4,
          'birational_V1_V2_value_bucket_counts':[[v,len(I)] for v,I in sorted(full_pair_buckets.items())],
          'birational_V1_V2_first_controls':[[i,Vpair[i],Wkeys[i]] for i in (0,1,2,37,521,1601)],
'exact_full_slice_sha256':h},indent=2,sort_keys=True))
        return
    chosen=[]
    while len({tuple(row[2][j] for j in chosen) for row in rows})<len(rows):
        sz=len({tuple(row[2][j] for j in chosen) for row in rows})
        j=max(use,key=lambda k:len({tuple(row[2][i] for i in (*chosen,k)) for row in rows}))
        k=len({tuple(row[2][i] for i in (*chosen,j)) for row in rows})
        if k==sz:break
        chosen.append(j);use.remove(j)
    assert rows[0][1]==0
    print(json.dumps({'actual_B_curve_coeffs':[-35%P,-98%P],'max_order_basis_reduced_discriminant':13,
       'velu_gamma':vG,'velu_J':vJ,'primitive_tracezero_alpha':alpha,'number_of_signed_tracezero_norms':n_alpha,
       'fixed_mark_frame_by_prime':dict(zip(PS,frame)),'endomorphism_tables':dict(zip(PS,map(len,T))),
       'cusp_coordinate_values':[[i,t] for i,t,B in rows],
       'separating_character_masks':chosen,'distinct_invariant_rows':len({tuple(B[j] for j in chosen) for _,_,B in rows}),
       'chosen_tuple_values':[[i,[B[j] for j in chosen]] for i,_,B in rows]},sort_keys=True,indent=2))
if __name__=='__main__':main()
