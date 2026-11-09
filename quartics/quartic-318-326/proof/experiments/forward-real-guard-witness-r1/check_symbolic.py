#!/usr/bin/env python3
"""Exact raw-row coefficient check, independent of Lean elaboration; not global proof."""
from pathlib import Path
import hashlib,json,re
import sympy as s
HERE=Path(__file__).resolve().parent
RAW=HERE.parents[1]/'progress'/'Raw318FinalReplayData.lean'
def mul(x,y): return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def add(x,y): return tuple(x[i]+y[i] for i in range(2))
def sub(x,y): return tuple(x[i]-y[i] for i in range(2))
def run():
    text=RAW.read_text();checked=[]
    for j in range(4):
        a,b,c,d,e,f,g,h,z,r,t=s.symbols(f'a{j} b{j} c{j} d{j} e{j} f{j} g{j} h{j} z{j} r{j} t{j}')
        u=(a,b);v=(c,d);U=(e,f);V=(g,h)
        uf=mul(u,u);Uf=mul(U,U);den=sub(Uf,uf);num=add(mul(u,V),mul(U,v))
        eq=sub(mul(den,(r,t)),num)
        w={1+4*j:a,2+4*j:b,3+4*j:c,4+4*j:d,
           17+4*j:e,18+4*j:f,19+4*j:g,20+4*j:h,
           58+2*j:uf[0]/(2 if j==2 else 1),59+2*j:a*b,
           66+2*j:Uf[0],67+2*j:e*f,78+3*j:z,79+3*j:r,80+3*j:t}
        for k in range(3):
            n=39+3*j+k
            row=re.search(rf'^@\[expose\] def r{n} .* := (.*)$',text,re.M)
            assert row,n
            expr=re.sub(r'w (\d+)',lambda m:f'w{m[1]}',row[1])
            actual=s.sympify(expr,locals={f'w{i}':v for i,v in w.items()},rational=True)
            expected=den[0]*z-1 if k==0 else eq[k-1]
            assert s.expand(actual-expected)==0,n
            checked.append(n)
    prior=set(range(1,38))|set(range(58,78))
    assert not prior.intersection(range(78,90))
    return {'status':'PASS','scope':'12 literal coefficient identities and disjoint coordinate support only',
      'rows':checked,'sympy_version':s.__version__,
      'raw_data_sha256':hashlib.sha256(RAW.read_bytes()).hexdigest(),
      'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob('RealGuard*.lean')},
      'full_arithmetic_theorem_proved':False}
if __name__=='__main__': print(json.dumps(run(),indent=2))
