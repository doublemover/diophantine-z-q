#!/usr/bin/env python3
"""Exact symbolic cross-check; not a Lean compilation or arithmetic proof."""
from pathlib import Path
import hashlib
import json
import re
import sympy as sp

HERE = Path(__file__).resolve().parent
PROGRESS = HERE.parents[1] / 'progress'
RAW = PROGRESS / 'Raw318FinalReplayData.lean'

def add(x, y):
    return tuple(x[i]+y[i] for i in range(2))

def neg(x):
    return tuple(-a for a in x)

def mul(x, y):
    return x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0]

def scale(n, x):
    return n*x[0], n*x[1]

def equal(x, y):
    assert sp.expand(x-y) == 0, sp.factor(x-y)

def run():
    a,b,c,d=sp.symbols('a b c d')
    u=(a,b); s=(c,d); f=mul(u,u); t=mul(f,s); fv=mul(t,s)
    k=(-1,sp.Rational(7,4)); m=(sp.Rational(39,8),sp.Rational(-9,2)); D=(11,-6)
    rhs=add(add(mul(mul(k,k),add(f,fv)),scale(2,mul(m,t))),mul(D,mul(t,t)))
    residual=add((1,0),neg(rhs))
    w={33:f[0],34:f[1],35:c,36:d,37:a*a-2*b*b,
       74:t[0],75:t[1],76:fv[0],77:fv[1]}
    source=RAW.read_text()
    checks=[]
    for n in range(32,39):
        line=re.search(rf'^@\[expose\] def r{n} .* := (.*)$',source,re.M)
        assert line, f'Missing literal row {n}'
        expr=re.sub(r'w (\d+)',lambda m:f'w{m[1]}',line[1])
        val=sp.sympify(expr,locals={f'w{i}':v for i,v in w.items()},rational=True)
        want=residual[n-36] if n in (36,37) else 0
        equal(val,want)
        checks.append(f'literal r{n} '+('equals compression component' if n in (36,37) else 'vanishes'))
    for j in range(8):
        a,b,c,d=sp.symbols(f'a{j} b{j} c{j} d{j}')
        uj=(a,b); vj=(c,d); fj=mul(uj,uj)
        wj={4*j+1:a,4*j+2:b,4*j+3:c,4*j+4:d,
            58+2*j:fj[0]/(2 if j==2 else 1),59+2*j:a*b}
        curve=add(add(mul(vj,vj),(-1,0)),mul(D,mul(fj,fj)))
        for o in range(4):
            n=4*j+o
            line=re.search(rf'^@\[expose\] def r{n} .* := (.*)$',source,re.M)
            assert line, f'Missing literal row {n}'
            expr=re.sub(r'w (\d+)',lambda m:f'w{m[1]}',line[1])
            val=sp.sympify(expr,locals={f'w{i}':v for i,v in wj.items()},rational=True)
            equal(val,curve[o-2] if o>=2 else 0)
        checks.append(f'literal reciprocal chart {j}: all four rows')
    assert not set(w).intersection(set(range(1,33)) | set(range(58,74)))
    checks.append('disjoint coordinate supports permit compatible first-39-row assembly')
    for i in range(2):
        equal(mul(m,m)[i],add(mul(mul(k,k),mul(k,k)),neg(D))[i])
    U,V,K,M,E,T=sp.symbols('U V K M E T')
    F=1-K**2*(U**2+U**2*T**2)-2*M*U**2*T-E*(U**2*T)**2
    A=M+(K**2+E*U**2)*T
    equal((K**2+E*U**2)*F,U**2*(M**2-K**4+E)-(U**2*A**2-K**2*(1-E*U**4)))
    shift=(K*V/U-M)/(K**2+E*U**2)
    assert sp.cancel((M+(K**2+E*U**2)*shift)/(K*U**2)-V/U**3) == 0
    checks += ['actual fixed-point constant equation', 'generic compression polynomial certificate',
               'original ordinate reconstruction rational identity']
    return {'status':'PASS','scope':'Exact symbolic identities only; not Lean compilation or global arithmetic completeness',
            'sympy_version':sp.__version__,'checks':checks,
            'raw_data_sha256':hashlib.sha256(RAW.read_bytes()).hexdigest(),
            'lean_source_sha256':{n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in ['CompressedAnchorWitness318.lean','ReciprocalChartWitness318.lean']},
            'lean_compilation_status':'Not performed by this script; see VALIDATION.json'}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
