#!/usr/bin/env python3
"""Explicit rational surplus-root norm, retaining the 19 actual W cells."""
from pathlib import Path
from fractions import Fraction as F
from math import prod
from hashlib import sha256
import json,sys
sys.set_int_max_str_digits(0)
P=Path(__file__).resolve().parents[1] / 'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py'
raw=P.read_bytes()
assert sha256(raw).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(raw.decode().split('\nqs=(')[0],globals())
f=P.parent.parent/'linked-detector-numeric-anchor-phase-repair-r1/EXACT-PRIMARY-REPAIRED-COVER.json'
data=json.loads(f.read_bytes())
cells=[(p,w) for p,w,_,_ in data['old_cells_W_a_unit_b_unit']] + [
 (r['p'],r['W_mod_p2']) for r in data['actual_new_contacts']]
assert len(set(p for p,_ in cells))==len(cells)==19
assert all(p%8==1 and chi(2,p)==1 for p,_ in cells)
u=prod(p for p,_ in cells)
k=F(u**4,2)+F(3*u*u,4)+F(1,32)
assert k>0
targets={2:600,3:8,5:4,7:4,11:4,13:4,17:1,19:4,23:4,37:4,2399:4}
den=prod(p**(m-(p==2)) for p,m in targets.items())
assert all(u%p for p in targets)
N,L=0,1
roots=[]
for p,w in cells:
 m=p**3
 s=rootsmod(mod(k+u*u*w*w,m),p,3)[0]
 alpha=(s+u*w)%m
 assert alpha%p and (s*s-mod(k+u*u*w*w,m))%m==0
 N,L=crt(N,L,den*alpha%m,m)
 roots.append([p,w,s,alpha])
for p in targets:N,L=crt(N,L,1,p)
# A>>K/A and W>2 with one simple exact step, no interval search.
mult=max(1,(den*(4*u+mod(k,1)+k.numerator//k.denominator+2))//L+1)
A=F(N+mult*L,den)
W=(A-k/A)/(2*u)
S=(A+k/A)/2
R=W*W+F(3,4)+u*u
assert W>2 and R*R-2*S*S==(W*W+F(1,2))*(W*W+1)
assert S*S-u*u*W*W==k
assert all(vp(W,p)==-m for p,m in targets.items())
assert all(mod(W,p*p)==w for p,w in cells)
# Programmatic budget and exact sample no factorization of actual numbers.
dump=lambda q:[F(q).numerator,F(q).denominator]
print(json.dumps(dict(u=u,k=dump(k),coeff_A=dump(A),W=dump(W),R=dump(R),S=dump(S),
    exact_split_cells=roots,small_W_required_depth={p:-m for p,m in targets.items()},
    W_height=[W.numerator.bit_length(),W.denominator.bit_length()],
    preserves_actual_h=data['final_h'],enlarged_crt_modulus=L),indent=2))
