#!/usr/bin/env python3
"""Exhaustive F_(53^2) low-level finite map; no high-level kernels required."""
from dataclasses import dataclass
from collections import defaultdict, Counter
from math import comb
from pathlib import Path
import json

p = 53
d = 22

@dataclass(frozen=True, order=True)
class K:
    a: int = 0
    b: int = 0
    def __post_init__(self):
        object.__setattr__(self,'a',self.a%p)
        object.__setattr__(self,'b',self.b%p)
    @staticmethod
    def of(t):
        return t if isinstance(t,K) else K(t)
    def __add__(self,t):
        t=K.of(t);return K(self.a+t.a,self.b+t.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self,t): return self+-K.of(t)
    def __rsub__(self,t): return K.of(t)+-self
    def __mul__(self,t):
        t=K.of(t);return K(self.a*t.a+d*self.b*t.b,self.a*t.b+self.b*t.a)
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0: return self.inv()**(-n)
        b,s=self,K(1)
        while n:
            if n&1:s=s*b
            b=b*b;n//=2
        return s
    def inv(self):
        t=pow((self.a*self.a-d*self.b*self.b)%p,-1,p)
        return K(t*self.a,-t*self.b)
    def __truediv__(self,t): return self*K.of(t).inv()
    def __rtruediv__(self,t): return K.of(t)*self.inv()
    def __bool__(self): return bool(self.a or self.b)
    def j(self): return [self.a,self.b]

zero,one=K(),K(1)
field=[K(a,b) for a in range(p) for b in range(p)]
pairs=defaultdict(list)
for f in field:pairs[f*f].append(f)

def hasse_j():
    assert pow(d,(p-1)//2,p)==p-1
    coeff=[comb(26,i)**2%p for i in range(27)]
    def f(x):
        s=zero
        for a in reversed(coeff):s=s*x+a
        return s
    vs=[l for l in field if not f(l)]
    assert len(vs)==26 and zero not in vs and one not in vs
    js=Counter(256*(1-l+l*l)**3/(l*l*(1-l)**2) for l in vs)
    return js

def children(s,c,b):
    if not (s+c):raise ValueError("pole at finite descendant")
    return s*s/(s+c),s*(s+b)

def chain(s,depth=3):
    row=(s,)
    for c,b in [(2,4),(4,8),(16,16)][:depth]:
        ee=[children(x,c,b) for x in row]
        assert all(x[1]==y[0] for x,y in zip(ee,ee[1:]))
        row=(ee[0][0],*(x[1] for x in ee))
    if not all(row): raise ValueError("zero at X0(2) descendant")
    return row

def source_j(t):
    t=chain(t)[0]
    return (t+256)**3/t**2

def project(x,y):
    return (x-2+3*x/y,(y-2*x-1)/x)

def t3_from_chart(x,y):
    X=(x*x+y)/(x*x)
    Y=(x*x*y+3*x*x+y*y-y)/(x*(y-1))
    X2,Y2=y+1,x*x*(y+3)
    def read(X,Y):
        t12=Y/(X-2)-3
        t6,t6b=t12*t12/(t12+2),t12*(t12+6)
        a=t6*t6*(t6+9)/(t6+8)**2
        b=t6b*t6b*(t6b+9)/(t6b+8)**2
        c=t6b*(t6b+9)**2/(t6b+8)
        assert t6*(t6+9)**2/(t6+8)==b
        return a,b,c
    a,b,c=read(X,Y)
    e,f,g=read(X2,Y2)
    assert (b,c)==(e,f)
    return a,b,c,g

def on_ell(P):
    if P is None:return True
    X,Y=P
    return Y*Y==X*(X+1)*(X-3)

def phi(x,y):
    r=(x-1/x)/2;s=(2*y-x**4-1)/(4*x*x)
    assert s*s==r**4+r*r+1
    if not r:
        assert s in (one,-one)
        return ((K(3),zero),"r=0,v=+1,raw=O") if s==one else ((K(-1),zero),"r=0,v=-1,raw=(0,0)")
    A=(s+1)/(r*r);B=(A*A-1)*r
    assert B*B==(A*A-1)*(2*A+1)
    X,Y=2*A+1,2*B
    assert on_ell((X,Y))
    if X==K(3):
        assert not Y
        return None,"raw=(3,0),based=O"
    m=Y/(X-3)
    V=m*m-1-X
    R=V,m*(3-V)
    assert on_ell(R)
    return R,None

def run():
    js=hasse_j()
    info={}; chart_bad=[]; project_bad=[]; allpairs=defaultdict(list)
    for x in field:
        H=x**4+1
        for z in pairs.get(H*H+12*x**4,[]):
            y=(H+z)/2
            assert y*y-y*H==3*x**4
            if not x or not y:
                chart_bad.append([x.j(),y.j()]); continue
            T,U=project(x,y)
            try:
                ch=chain(T);dh=chain(U)
            except ValueError:
                project_bad.append([x.j(),y.j(),T.j(),U.j()]);continue
            key=T,U
            allpairs[key].append((x,y))
            j=source_j(T)
            if j not in js:continue
            jj=source_j(U)
            assert jj in js
            value,flag=phi(x,y)
            k3=t3_from_chart(x,y)
            for z,a,b in zip(k3,ch,dh):
                assert (z+27)*(z+243)**3/z**3==(a+256)**3/a**2
                assert (z+27)*(z+3)**3/z==(b+256)**3/b**2
            info.setdefault(key,[]).append(dict(x=x.j(),y=y.j(),j=j.j(),j3=jj.j(),t3=[a.j() for a in k3],t4=[a.j() for a in chain(T,2)],t4_after3=[a.j() for a in chain(U,2)],t2=[t.j() for t in ch],t2_after3=[t.j() for t in dh],phi=None if value is None else [v.j() for v in value],branch=flag))
    order_j=Counter(tuple(row['j']) for rs in info.values() for row in rs)
    print('Hasse',[(x.j(),c) for x,c in sorted(js.items())])
    print('marked rows',sorted(order_j.items()),'keys',len(info),'total',sum(map(len,info.values())))
    print('chart bad',chart_bad,'project bad',len(project_bad))
    print('all chart finite keys',len(allpairs),'ambiguous',sum(len(v)>1 for v in allpairs.values()))
    print('supersingular ambiguous keys',[(x.j(),y.j(),rows) for (x,y),rows in info.items() if len(rows)>1])
    print('supersingular special branches',[(x.j(),y.j(),a['branch']) for (x,y),rows in info.items() for a in rows if a['branch']])
    def sig(A):
        return tuple(map(tuple,A))
    chKeys=defaultdict(list)
    for key,rs in sorted(info.items()):
        for row in rs:chKeys[sig(row['t2']),sig(row['t2_after3'])].append((key,row))
    collisions=[]
    for key,bucket in chKeys.items():
        if len(bucket)>1:
            coll=[dict(T=a.j(),U=b.j(),t3=row['t3'],phi=row['phi']) for (a,b),row in bucket]
            mask4=[(side,i) for side in ('t4','t4_after3') for i in range(3) if len({tuple(row[side][i]) for _,row in bucket})==len(bucket)]
            mask=[i for i in range(4) if len({tuple(row['t3'][i]) for _,row in bucket})==len(bucket)]
            print("collision",key,"mask4",mask4,"same phi",all(row['phi']==bucket[0][1]['phi'] for _,row in bucket))
            collisions.append(dict(t2=key[0],t2_after3=key[1],rows=coll,t3_resolving_stages=mask,t4_resolving_stages=mask4))
    print('supersingular combined 8 edge ambiguities',len(collisions))
    print('resolvable by marked t3',sum(bool(r['t3_resolving_stages']) for r in collisions))

    # Every actual geometric low-level marked point is covered; see the argument in the note.
    assert dict(order_j)=={tuple(j.j()):32 if j==zero else 96 for j in js}
    assert K(1728) not in js
    seed=info[K(6,40),K(44,18)]
    assert len(seed)==1 and seed[0]['phi']==[[43,47],[15,18]]
    assert on_ell((K(3),zero)) and phi(one,K(3))[0]==(K(3),zero)
    records=[]
    for key,rs in sorted(info.items()):
        assert all(r['t2']==rs[0]['t2'] and r['t2_after3']==rs[0]['t2_after3'] for r in rs)
        records.append(dict(T=key[0].j(),U=key[1].j(),rows=rs))
    report=dict(format="each field element [a,b] is a+b*u, u^2=22, over F53", count=sum(order_j.values()),hasse_j=[j.j() for j in sorted(js)], chart_bad=chart_bad,project_bad=project_bad,chain_collisions=collisions,records=records)
    Path(__file__).with_name('LOW-48-SUPERSINGULAR-F53.json').write_text(json.dumps(report,separators=(',',':'),sort_keys=True)+'\n')
if __name__=='__main__':run()
