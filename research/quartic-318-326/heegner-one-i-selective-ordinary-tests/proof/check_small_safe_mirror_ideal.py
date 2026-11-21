#!/usr/bin/env python3
"""Least good point-count-zero-forced mirror prime, and its exact chart."""
from pathlib import Path
import runpy,contextlib,io,hashlib,json
from math import isqrt
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
H=Path(__file__).resolve().parent.parent
def get(path,pin):
    a=(H/path).read_bytes()
    assert hashlib.sha256(a).hexdigest()==pin
    return H/path
f=get("actual-one-I-affine-enumeration-r1/check_affine_frobenius_filters.py",
 "4684be7a8adbc66295090b31775db4f965fdae1e991c5e789e4f53aedc32038c")
with contextlib.redirect_stdout(io.StringIO()):
    m=runpy.run_path(str(f))
d=m["d"]; row=m["row"]
E=get("actual-one-I-mirror-even-tower-r1/EXACT-MIRROR-EVEN-TOWER-AND-CHARTS.json",
 "962cc16a0b4a09cb9469dfd286bec9976b51aeca6ac7ecf6c77a255aafc505d0")
j=json.loads(E.read_text()); assert j["d"]==d
q=1951; P=[]
for p in range(5,q+1):
    if d%p==0 or p==13 or any(p%k==0 for k in range(2,isqrt(p)+1)):
        continue
    r=row(p); t=r["trace"]
    if (p+1-t)%13==0 or r.get("skipped_repeated_eigenvalue"):continue
    for h in r["rows"]:
        n=h["line_residue_degree"]
        if h["covector_return_order"]==1:
            assert n>=3
            if p**n<=q**3:P.append((p,n,t))
assert P==[(1951,3,-40)]*4
D=j["relative_normalization_divides_Z_squared_by"];assert D==13**4*d
f0=[c%q for c in j["absolute_even_degree84_polynomial_desc"]]
h=g.gf_factor(f0,q,ZZ)[1]
assert len(h)==28 and all(len(a)==4 and e==1 for a,e in h)
hh=min(a for a,e in h);assert hh==[1,66,1847,82]
W=[D%q,0]
zz=g.gf_pow_mod(W,(q**3+1)//4,hh,q,ZZ)
assert zz and g.gf_rem(g.gf_sqr(zz,q,ZZ),hh,q,ZZ)==W
print(json.dumps(dict(d=d,rational_prime=q,least_norm=q**3,Frobenius_trace=-40,
  order=1992,norm_exceeds_GRH_cap=q**3>148614287,
  marked_degree3_Y_factor_desc=hh,marked_Z_mod_Y_desc=zz,
  relative_split_line_orbit_count=4,
  no_lower_good_split_norm_with_E_mod13_fixed_zero=True),
  sort_keys=True,indent=2))
