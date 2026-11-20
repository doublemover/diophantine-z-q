#!/usr/bin/env python3
"""Preserve reviewed weights, modular marks and lattice; replace only box scan."""
from math import isqrt
from pathlib import Path
from subprocess import run
from sys import argv
import json
from time import monotonic
import odd2544_two_source_controls as source
from odd2544_two_source_controls import src

EXE=Path(argv[1]).resolve()
OLD_REPS=source.exact_reps_at

def new_reps(order,den,M):
    assert tuple(r[0] for r in order)==(den,0,0,0)
    V=src.reduce_basis([tuple(order[i][j] for i in range(1,4)) for j in range(1,4)])
    a,b,c=[src.disc_(v) for v in V]
    p,q,r=[int(2*src.inner(V[i],V[j])) for i,j in ((0,1),(0,2),(1,2))]
    g=4*a*b*c+p*q*r-a*r*r-b*q*q-c*p*p
    assert g>0
    z0=9*den*den*M
    X=isqrt((z0*(4*b*c-r*r))//g)
    Y=isqrt((z0*(4*a*c-q*q))//g)
    raw=' '.join(map(str,(a,b,c,p,q,r,z0,X,Y,*[u for v in V for u in v])))
    res=run([EXE],input=raw,text=True,check=True,capture_output=True)
    for line in res.stdout.splitlines():
        row=tuple(map(int,line.split()))
        assert len(row)==3 and src.disc_(row)==z0
        yield row

def read(D, reps, book):
    source.exact_reps_at=reps
    now=monotonic()
    data=source.coefficient(book,D)
    secs=monotonic()-now
    return data, secs

def main():
    assert src.hashlib.sha256(src.SOURCE.read_bytes()).hexdigest().startswith('aa650e28')
    book=json.loads(src.SOURCE.read_text())
    if argv[2]=="bench":
        out=[]
        for D in [-83,-419]:
            slow,py=read(D,OLD_REPS,book)
            quick,cpp=read(D,new_reps,book)
            assert slow==quick
            out.append(dict(checked=quick,python_seconds=round(py,3),
                            cpp_seconds=round(cpp,3),ratio=round(py/cpp,2)))
        print(json.dumps(out,indent=2,sort_keys=True))
    else:
        out=[]
        for t in argv[2:]:
            D=int(t)
            c,_=read(D,new_reps,book)
            out.append(c)
        print(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__":main()
