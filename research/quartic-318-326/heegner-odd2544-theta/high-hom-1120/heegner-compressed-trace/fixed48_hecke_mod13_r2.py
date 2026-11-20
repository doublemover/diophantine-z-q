#!/usr/bin/env python3
"""Real finite low-level graph; odd-13 same detector, not a char0 lift."""
import hashlib,json,sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
from random import Random
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'high-hom-1120/heegner-f53-descended'))
from actual_20_class_trace import *
from one_class_weighted_trace import *
from horizontal_fields import field
import marked_t16_invariants as direct

SRC=ROOT/'joined-work-20261120/rc-d1-f53-supersingular-low-map-r1/LOW-48-SUPERSINGULAR-F53.json'

def ktuple(a):return tuple(a.subfield())
def label(T,U):return ktuple(T)+ktuple(U)

def tkey(A,a,b):
    B,f=A.quotient(b,3)
    return label(direct.t16(A,a),direct.t16(B,f(a)))

def pointkey(r):return tuple(r['T']+r['U'])

def norm_count(d,q):
    return 1+sum((y*y-x*(x-d)*(x+3*d))%q==0 for x in range(q) for y in range(q))

def fresh_E(j):
    if j==[0,0]:return [[0,0],[1,0]]
    j=read(D16,j)
    c=j/(1728-j)
    A,B=3*c,2*c
    out=[]
    for s in [D16.one,1+D16.u]:
        C=D16.E(A*s*s,B*s**3)
        Ps=D16.coordinates(C,D16.one)
        check=next(P for P in Ps if C.mul(2,P))
        if C.mul(54,check) is None:
            assert 1450 < len(Ps) < 1470
            out.append(coeffs(C))
    assert len(out)==1
    return out[0]

def basis(M,ab,m,n,l,k,seed):
    # [m] is the identity-killing Frobenius scalar minus 1 (up to sign).
    rng=Random(seed);A=E(M,ab)
    gens=[]
    assert m % n==0
    for _ in range(200):
        x=M.F.trim([rng.randrange(p) for _ in range(k)])
        y=M.sqrt(x**3+A.A*x+A.B)
        if y is None:continue
        R=A.mul(m//n,(x,y))
        assert A.mul(n,R) is None
        t=A.mul(n//l,R)
        if t is None:continue
        if not gens:gens.append(R)
        elif t not in [A.mul((n//l)*u,gens[0]) for u in range(l)]:
            return gens[0],R
    raise AssertionError('no full independent torsion basis')

def lines(A,a,b,n,l):
    G=[A.add(a,A.mul(i,b)) for i in range(n)]
    G +=[A.add(A.mul(l*i,a),b) for i in range(n//l)]
    assert len(G)==n+n//l and len(set(G))==len(G)
    return G

def rank_mod(xs,n,r):
    basis={}
    for x in xs:
        x=[z%r for z in x]
        for i in range(n):
            a=x[i]
            if a:
                if i not in basis:
                    c=pow(a,-1,r);basis[i]=[c*z%r for z in x]
                    break
                y=basis[i]
                x=[(t-a*b)%r for t,b in zip(x,y)]
    return len(basis)

def main():
    data=SRC.read_bytes()
    assert hashlib.sha256(data).hexdigest().startswith('421d8068')
    book=json.loads(data)
    install()
    H=field(12,12);install_fast_inverse(H,H.modulus)
    Aout=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    es=[fresh_E(j) for j in book['hasse_j']]
    reps={}
    graphs={5:{},7:{},13:{},17:{},19:{}}
    for ab in es:
        A=E(D8,ab)
        a,b=basis(D8,ab,p**4-1,16,2,8,16)
        c,d=basis(D8,ab,p**4-1,3,3,8,3)
        G16,G3=lines(A,a,b,16,2),lines(A,c,d,3,3)
        this={}
        for U in G16:
            for V in G3:
                key=tkey(A,U,V)
                this[key]=(U,V)
        assert len(this)==(32 if ab==[[0,0],[1,0]] else 96)
        assert not (set(reps)&set(this))
        reps.update(this)
        for q,M,m,k in [(5,D8,p**4-1,8),(7,H,H.m,H.n),(13,D8,p**4-1,8),(17,D16,p**8-1,16),(19,D18,p**9+1,18)]:
            P,Q=basis(M,ab,m,q,q,k,q)
            maps=[faster_odd_edge(M,E(M,ab),R,q)
                    for R in lines(E(M,ab),P,Q,q,q)]
            for key in this:
                graphs[q][key]=Counter()
            for f in maps:
                R=E(D8,f.dst);ev=f.at(D8)
                for key,(U,V) in this.items():
                    graphs[q][key][tkey(R,ev(U),ev(V))]+=1
    # Only now identify all generated actual points with the complete
    # independently enumerated chart table, including the elliptic values.
    tab={pointkey(r):r['rows'][0]['phi'] for r in book['records']}
    assert len(tab)==len(reps)==416 and set(tab)==set(reps)
    G=short((D8.F.of(22),15*D8.u))
    assert Aout.mul(13,G) is None
    g13={Aout.mul(j,G):j for j in range(13)}
    value={k:g13[Aout.mul(224,short(tuple(parse(D8,v))))] if v else 0 for k,v in tab.items()}
    conj=lambda x:(x[0],-x[1]%53,x[2],-x[3]%53)
    assert all(value[conj(k)]==-value[k]%13 for k in tab)
    R=sorted(k for k in tab if k<conj(k))
    indices={k:(v,1) for v,k in enumerate(R)}
    indices.update({conj(k):(v,-1) for v,k in enumerate(R)})
    def clean(k,v):
        row=[0]*len(R)
        for key,w in v.items():
            if key in indices:
                i,a=indices[key];row[i]+=a*w
        return row
    Eqs=[];dim=[];atas={}
    for q,G in graphs.items():
        a=q+1-norm_count(-1,q);atas[str(q)]=a
        assert set(G)==set(tab)
        for k,v in G.items():
            assert all(x in tab for x in v) and sum(v.values())==q+1
            assert sum(w*value[x] for x,w in v.items())%13==(a*value[k])%13
            # Geometric Aut(E,C48) = ±1, so duality balances adjacency.
            assert all(G[x][k]==w for x,w in v.items())
        for k in R:
            vv=G[k].copy();vv[k]-=a
            Eqs.append(clean(k,vv))
        dim.append([q,len(R)-rank_mod(Eqs,len(R),13)])
    rowpoint={pointkey(r):r['rows'][0] for r in book['records']}
    w3 = {k:(k[2],k[3],k[0],k[1]) for k in tab}
    w48={}
    for k,dat in rowpoint.items():
        x,y=[read(D8,dat[a]) for a in ['x','y']]
        C=2*y-x**4-1
        X=(x+1)/(x-1)
        Z=4*C/(x-1)**4
        Y=(Z+X**4+1)/2
        assert Y*Y-Y*(X**4+1)==3*X**4
        w48[k]=label(X-2+3*X/Y,(Y-2*X-1)/X)
    for no,invol in [(3,w3),(48,w48)]:
        assert set(invol)==set(invol.values())==set(tab)
        assert all(invol[invol[k]]==k for k in tab)
        assert all(value[invol[k]]==-value[k]%13 for k in tab)
        for k in R:Eqs.append(clean(k,Counter([k,invol[k]])))
        dim.append(['W'+str(no),len(R)-rank_mod(Eqs,len(R),13)])
    print(json.dumps({
      'low_table_sha':hashlib.sha256(data).hexdigest(),
      'literal_low_vertices':len(tab), 'frobenius_antisymmetric_rank':len(R),
      'good_trace_eigenvalues':atas,'after_each_mod13_constraint_dimension':dim,
      'all_marked_edges_match_actual_detector_values':True,
      'sum_G13_coefficients_mod13':sum(value.values())%13,
    },indent=2,sort_keys=True))
if __name__=='__main__':main()
