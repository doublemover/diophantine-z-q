from collections import Counter
from functools import reduce
from operator import xor
import json

# All 20 variables are independent initially: for each support prime use
# coefficient T0=(0,1,1) and Ts=(1,0,1) at root ordered places (0,S,T).
p_a,p_b=415721,9807649
S=-32*407*2399**2
T=2399*407**2
delta=T-S
assert delta == 407*2399*(3**2*5**2*7**3)
basis=(-1,2,5,7,11,37,2399,'a1','a2','b1')
movers=('a1','a2','b1','b2')
edges={frozenset(('a1','b1')),frozenset(('a2','b1'))}
reps={'a1':p_a,'a2':p_a,'b1':p_b,'b2':p_b}
id_codes=(0,0b110,0b101,0b011)

def lp(x,p):
    assert x%p
    t=pow(x%p,(p-1)//2,p)
    assert t in [1,p-1]
    return int(t!=1)
def p_unit(x,p):
    k=0
    while x%p==0:
        x//=p; k+=1
    return k,x
def local_odd(x,p):
    v,u=p_unit(x,p)
    return v%2,lp(u,p)
def phase(g,p):
    if g==p:
        return 0
    if g in movers and p in movers:
        return int(frozenset((g,p)) in edges)
    return lp(reps.get(g,g),reps.get(p,p))
def point_torsion_odd(p):
    res={}
    for x in (None,0,S,T):
        if x==None:
            res[0]=0;continue
        diffs=[x,x-S,x-T]
        nz=[u for u in diffs if u]
        z=[u if u else nz[0]*nz[1] for u in diffs]
        l=list(zip(*[local_odd(u,p) for u in z]))
        out=lambda v:sum(e<<i for i,e in enumerate(v))
        v,u=map(out,l)
        assert v not in res
        res[v]=u
    return res
def point_torsion_move(p):
    res={0:0}
    q=reps[p]
    sign=reduce(xor,(phase(g,p) for g in movers if g!=p))
    powers={x:lp(x,q) for x in (S,T,delta)}
    a,b,c=[powers[x] for x in (S,T,delta)]
    for v,l in [(0b110,(a^b,sign^a,sign^b)),
                (0b101,(sign^a,a^c,sign^c)),
                (0b011,(sign^b,sign^c,b^c))]:
        res[v]=sum(e<<i for i,e in enumerate(l))
    return res

tables={p:point_torsion_odd(p) for p in (11,37,2399)}
tables.update({p:point_torsion_move(p) for p in movers})
assert all(tab[0]==0 and all(tab[x^y]==tab[x]^tab[y] for x in tab for y in tab) for tab in tables.values())
def codes(j):
    r=[0]*len(basis)
    if j!=None: r[j//2]=[0b110,0b101][j%2]
    return r
def bits(v):
    return [v>>i&1 for i in range(3)]
def checks(rs):
    cv=dict(zip(basis,rs))|{'b2':0}
    # Real second coordinate positive.
    ret=[cv[-1]>>1&1]
    # Dyadic third coordinate: valuation parity and odd unit coordinate
    # in U_2 / U_2^2 ~ < -1,5>.
    z=1
    for g,c in zip(basis,rs):
        if g!=2 and c>>2&1:
            z=z*reps.get(g,g)%8
    ret += [cv[2]>>2&1, int(z%4!=1), int(z in [3,5])]
    for p in (5,7,11,37,2399,*movers):
        v=cv[p]
        u=reduce(xor,(c for g,c in zip(basis,rs) if phase(g,p)),0)
        if p in tables:
            ret += bits(u^tables[p][v])
        else:
            a,b,c=bits(v)
            ret += [a, (u&1)^(b if p==7 else 0)]
    return ret

nvars=2*len(basis)
nrows=len(checks(codes(None)))
cols=[checks(codes(j)) for j in range(nvars)]
rows=[sum(cols[j][i]<<j for j in range(nvars)) for i in range(nrows)]
red={}
for r in rows:
    while r:
        h=r.bit_length()-1
        if h in red:
            r^=red[h]
        else:
            red[h]=r;break
def rhs(cs):
    return sum((id_codes.index(c)&1)<<(i*2) | (id_codes.index(c)>>1)<<(i*2+1) for i,c in enumerate(cs))
F=rhs([0,0,0,6,6,6,3,6,6,0])
A=rhs([0,0,0,0,0,0,3,5,5,3])
B=rhs([0,0,6,0,5,0,6,0,0,0])
want={reduce(xor,(v for i,v in enumerate([F,A,B]) if j>>i&1),0) for j in range(8)}
assert len(want)==8 and len(red)==nvars-3
assert all(not any((v&r).bit_count()%2 for r in rows) for v in want)

def inertia(v,p):
    return id_codes[(v>>(2*basis.index(p)))&3]
def form(c,d):
    assert c in id_codes and d in id_codes
    return int(c!=0 and d!=0 and c!=d)
gov={}
for p in ('a1',11,2399):
    us=[inertia(v,p) for v in (F,A,B)]
    gov[p]=[form(us[i],us[j]) for i,j in ((0,1),(0,2),(1,2))]
assert gov=={'a1':[1,0,0],11:[0,1,0],2399:[0,1,1]}
print(json.dumps({'S':S,'T':T,'delta':delta,'vars':nvars,'rows':nrows,'rank':len(red),'local_torsion_unit_by_valuation':{str(k):v for k,v in tables.items()},'basis':[list(inertia(v,p) for p in basis) for v in (F,A,B)],'inertia_square_rows':{str(k):v for k,v in gov.items()}},indent=2))
