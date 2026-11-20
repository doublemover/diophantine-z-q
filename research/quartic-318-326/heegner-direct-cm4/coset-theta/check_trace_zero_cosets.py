#!/usr/bin/env python3
"""Exact fixed trace-zero lattices and local coset control reads."""
from fractions import Fraction as F
from math import lcm
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse,json

here=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--book',type=Path,default=here.parent/'odd2544-weight-primefree-r1'/'ACTUAL-ODD2544-MARKED-ORDERS-Q29.json')
p.add_argument('--calibration',type=Path,default=here.parent/'direct-cm4-f53-calibration-r1'/'EXACT-CM4-D323.json')
a=p.parse_args()
book=a.book.read_bytes()
assert sha256(book).hexdigest()=='aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e'
cal=a.calibration.read_bytes()
assert sha256(cal).hexdigest()=='2550e6d05947071c31983bd886c86c0744d4c338cacb6a18f56df186cacc8c6a'

N=lcm(64,3,53)
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sc(n,x):return tuple(n*a for a in x)
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def cross(x,y):return tuple(x[(i+1)%3]*y[(i+2)%3]-x[(i+2)%3]*y[(i+1)%3] for i in range(3))
def determinant(g):return dot(g[0],cross(g[1],g[2]))
def normQ(v,e):
    _,b,c,g=v
    return F((3*b+2*c-g)**2+212*(c*c-c*g+g*g),12*e*e)
def tr(v,e):
    q,r=divmod(2*v[0]-v[1]-v[3],e)
    assert r==0
    return q
def integral(x):
    assert x.denominator==1
    return x.numerator
records=[]
for cl in json.loads(book)['marked_classes']:
    h=list(zip(*cl['max_order_basis_columns']));e=cl['basis_denominator']
    ts=[tr(v,e) for v in h]
    assert ts[0]==2 and ts[1]%2
    k=add(sc((1-ts[1])//2,h[0]),h[1])
    assert tr(k,e)==1
    B=[add(h[i],sc(-ts[i],k)) for i in (0,2,3)]
    assert all(tr(v,e)==0 for v in B)
    G=[[integral(normQ(add(x,y),e)-normQ(x,e)-normQ(y,e)) for y in B] for x in B]
    det=determinant(G)
    assert det==2*53**2 and all(G[i][i]%2==0 for i in range(3))
    adj=[cross(G[1],G[2]),cross(G[2],G[0]),cross(G[0],G[1])]
    level=lcm(*(F(adj[i][j],det*(2 if i==j else 1)).denominator for i,j in product(range(3),repeat=2)))
    assert level==212
    records.append(dict(j=cl['j'],denominator=e,trace_zero_basis_columns=B,
                        polar_gram=G,det=det,level=level))

def q16(r):
    return {12:4,44:12}.get(r%64)
for d in (323,1139,132107,465851):
    uv=[(u,v) for u,v in product(range(4),(1,3))
        if (2*u-v)%4==1 and (u*u-u*v+v*v)%4==(d+1)//4%4]
    assert q16(4*d)==4*((uv[0][0]-uv[0][1])%4)
data=json.loads(cal)
for row in data['all_exact_marks_of_chosen_trace']:
    a,b,c,g,e=row['endomorphism_coordinates']
    t=row['tr_before_shift']
    xi=(a-t*e//2,b,c,g)
    assert tr(xi,e)==0 and normQ(xi,e)==4*323
    assert any(x%2 for x in row['alpha_matrix_16'])
    ph=(3*b+2*c-g)*pow(3*e,-1,53)%53
    assert 1<=ph<=26
    for n,tag,u,l in [(16,'alpha_matrix_16',row['marks'][0],q16(4*323)),
                      (3,'alpha_matrix_3',row['marks'][1],1)]:
        A,B,C,D=row[tag]
        assert ((A-l)*u[0]+B*u[1])%n==0 and (C*u[0]+(D-l)*u[1])%n==0
assert len(data['all_exact_marks_of_chosen_trace'])==24 and data['chosen_ring_trace_mod13']==9
print(json.dumps(dict(universal_coset_modulus=N,unscaled_common_level=212,
                     scaled_common_level=212*N*N,
                     primitive_q16_by_norm_mod64={12:4,44:12},
                     marked_orientation_filter_on_2xi=[1,26],
                     exact_d323_rows_checked=24,
                     trace_zero_book=records),indent=2))
