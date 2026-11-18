"""Exact support, original class markings existence, and fixed-factor rank obstruction."""
import json,sys
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'analytic'))
from marked_pair import screen
b=F(204,439715)**2
theta=457
assert 17*12**2+theta*20569**2==439715**2
assert 1-b/17==theta*F(20569,439715)**2
assert 0<b<17
data=[]
for ps in [[103,17],[103,17,457]]:
    bit=lambda a,p:int(pow(a%p,(p-1)//2,p)==p-1)
    L=[[0 if i==j else bit(q,p) for j,q in enumerate(ps)] for i,p in enumerate(ps)]
    for i,row in enumerate(L):row[i]=sum(row)%2
    beta=[0,1]+([0] if len(ps)==3 else []);sel=[1,1]+([0] if len(ps)==3 else [])
    C=[[(L[i][j]+bit(3,ps[i])*sel[j])%2 for j in range(1,len(ps))] for i in range(1,len(ps))]
    assert C==[[int(i==j) for j in range(len(ps)-1)] for i in range(len(ps)-1)]
    d=17*103*(457 if len(ps)==3 else 1)
    pairs=screen(d,[2,3]+sorted(ps))
    assert len(pairs)==8 and (17,1) in pairs
    data.append(dict(d=d,deleted_sharp_core=C,selmer=pairs))
x=F(-43200,169);y=F(16750440,2197);d=-409
assert y and y*y==x*(x-d)*(x+3*d)
def count(p):return 1+sum(sum(int(y*y%p==x*(x-d)*(x+3*d)%p) for y in range(p)) for x in range(p))
assert [count(5),count(7)]==[8,8]
print(json.dumps(dict(b=str(b),pole_marking_scale='204/439715',complement_scale='20569/439715',curves=data,fixed_409_nontorsion=[str(x),str(y)],fixed_good_counts=[count(5),count(7)]),indent=2))
