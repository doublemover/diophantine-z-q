#!/usr/bin/env python3
"""Complete chart/receiver controls, not a CM multiplicity issuer."""
from collections import Counter
import json

P = 29
# a+b*s is encoded by a+29*b, s^2=2.
Q = P*P
def f(a,b=0):return a%P+P*(b%P)
def add(a,b):return f(a%P+b%P,a//P+b//P)
def neg(a):return f(-(a%P),-(a//P))
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    x,y=a%P,a//P
    z,t=b%P,b//P
    return f(x*z+2*y*t,x*t+y*z)
def pw(a,n):
    r=1
    while n:
        if n&1:r=mul(r,a)
        a=mul(a,a);n//=2
    return r
def fr(a):return f(a%P,-(a//P))
def div(a,b):
    assert b
    return mul(a,pw(b,Q-2))
def p_add(A,B):
    if A is None:return B
    if B is None:return A
    x,y=A;u,v=B
    if x==u:
        if add(y,v)==0:return None
        assert y==v
        s=div(sub(sub(mul(3,pw(x,2)),mul(4,x)),3),mul(2,y))
    else:s=div(sub(v,y),sub(u,x))
    z=sub(add(pw(s,2),2),add(x,u))
    return z,sub(mul(s,sub(x,z)),y)
def p_neg(A):return A if A is None else (A[0],neg(A[1]))
def p_fr(A):return A if A is None else tuple(fr(x) for x in A)
def pm(n,A):
    T=None
    while n:
        if n&1:T=p_add(T,A)
        A=p_add(A,A);n//=2
    return T
def roots_table():
    out=[[] for _ in range(Q)]
    for a in range(Q):out[mul(a,a)].append(a)
    return out
def epoints(squares):
    yield None
    for a in range(Q):
        for b in squares[mul(mul(a,add(a,1)),sub(a,3))]:yield a,b
def curvepoints(squares):
    for a in range(Q):
        for b in squares[add(add(pw(a,8),mul(14,pw(a,4))),1)]:yield a,b
    yield None,1
    yield None,28
def phi(X,Y):
    if X in (None,0):
        assert Y in (1,28)
        return None if Y==1 else (0,0)
    x=div(add(add(Y,pw(X,4)),1),mul(2,pw(X,2)))
    return x,mul(x,sub(X,div(1,X)))
def w48(X,Y):
    if X is None:return 1,mul(4,Y)
    if X==1:return None,div(Y,4)
    return div(add(X,1),sub(X,1)),div(mul(4,Y),pw(sub(X,1),4))
def q_fr(X,Y):return (None if X is None else fr(X),fr(Y))
def j48(X,Y):
    if X in (None,0):return None
    y48=div(add(add(Y,pw(X,4)),1),2)
    assert y48
    t=add(sub(X,2),div(mul(3,X),y48))
    for off in (2,4,16):
        den=add(t,off)
        if not den:return None
        t=div(pw(t,2),den)
    if not t:return None
    return div(pw(add(t,f(256)),3),pw(t,2))
# Independent Hasse invariant classification over every j; for j !=0,1728
# use y^2=x^3+3k x+2k, k=j/(1728-j).
def supersingular(j):
    import math
    if j==0:a,b=0,1
    elif j==f(1728):a,b=1,0
    else:
        k=div(j,sub(f(1728),j));a,b=mul(3,k),mul(2,k)
    s=0
    for i in range(15):
        l=28-3*i;k=14-i-l
        if min(l,k)<0:continue
        c=math.comb(14,i)*math.comb(14-i,l)
        s=add(s,mul(f(c),mul(pw(a,l),pw(b,k))))
    return s==0
def coords(A):
    return None if A is None else [ [x%P,x//P] for x in A]
def run():
    assert pw(2,(P-1)//2)==28
    S=roots_table(); ep=list(epoints(S)); ec=set(ep)
    plus=[e for e in ep if p_fr(e)==e]
    minus=[e for e in ep if p_fr(e)==p_neg(e)]
    assert (len(ep),len(plus),len(minus))==(864,24,36)
    gen_plus=min(e for e in plus if e is not None and e!=pm(2,e) and pm(3,e) is None)
    gen_minus=min(e for e in minus if e is not None and pm(3,e) is not None and pm(9,e) is None)
    idx={pm(i,gen_minus):i for i in range(9)}
    assert len(set(pm(4,e) for e in plus))==3
    assert len(set(pm(2,e) for e in minus))==9
    ss=[j for j in range(Q) if supersingular(j)]
    assert ss==[0,2,25]
    all_c=list(curvepoints(S)); set_c=set(all_c)
    assert len(set_c)==908
    hist=Counter(); orbhist=Counter(); samples={}; active={}
    for X,Y in all_c:
        j=j48(X,Y)
        e=phi(X,Y); w=w48(X,Y); qe=q_fr(X,Y)
        assert e in ec and w in set_c and qe in set_c
        assert phi(*w)==p_add((3,0),p_neg(e)) and p_fr(e)==phi(*qe)
        if j not in ss:continue
        q=(X,Y); W=pm(2,p_add(e,p_neg(p_fr(e))))
        Wq=idx[W]
        assert idx[pm(2,p_add(phi(*w),p_neg(p_fr(phi(*w)))))]==(-Wq)%9
        g=q_fr(*w)
        assert j48(*g) in ss and q_fr(*w48(*g))==q
        assert pm(2,p_add(phi(*g),p_neg(p_fr(phi(*g)))))==W
        hist[j,Wq]+=1
        if g==q:orbhist[j,Wq,1]+=1
        elif q<g:orbhist[0,Wq,2]+=1
        if Wq and q<=g:active[q]=(j,Wq,1 if q==g else 2)
        # An explicit finite coordinate check per nonzero residue phase.
        if Wq not in samples:samples[Wq]=[j,coords(q),coords(W)]
    assert sum(hist.values())==224
    byj={str(j):[hist[j,i] for i in range(9)] for j in ss}
    both=[[i,sum(hist[j,i] for j in ss)] for i in range(9)]
    assert sum(v for _,v in both)==224
    paircounts={str(k):sum(v for (_,_,kk),v in orbhist.items() if kk==k) for k in (1,2)}
    assert paircounts['1']+2*paircounts['2']==224
    activehist=Counter(k for j,w,k in active.values())
    assert sum(k*n for k,n in activehist.items())==128
    # Conditional readout: a certified provider gives one count mod 9 per key.
    active_table=[dict(q=list(q),j=j,phase=w,orbit=k) for q,(j,w,k) in sorted(active.items())]
    return dict(active_label_encoding="a+29*b represents a+b*s",active_orbits=dict(activehist),active_table=active_table,base_field=P,field_parameter='s^2=2',ss_j=ss,ss_phase_histograms=byj,
        combined_phase_histogram=both,chart_Frob_Fr_orbit_counts=paircounts,phase_controls=samples,
        target_plus_order=24,target_minus_order=36,plus_generator_order3=coords(gen_plus),
        minus_generator_order9=coords(gen_minus),scope='Complete fixed marked chart only. Histograms do not count any CM discriminant.')
if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
