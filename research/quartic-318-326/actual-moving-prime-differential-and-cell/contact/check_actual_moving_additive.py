#!/usr/bin/env python3
"""Cross-check the true 2-torsion translation and actual pilot residue phases."""
import sys, hashlib,json
from fractions import Fraction as F
from pathlib import Path
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha256(raw).hexdigest()=='6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1'
ix={r['prime']:r for r in json.loads(raw)['rows']}
def residue(x,p):
    x=F(x); return x.numerator*pow(x.denominator,-1,p)%p
def vp(x,p):
    x=F(x)
    if not x:return None
    a,b=x.numerator,x.denominator;e=0
    while a%p==0:a//=p;e+=1
    while b%p==0:b//=p;e-=1
    return e
def sqrt(x,p):
    return next(t for t in range(1,p) if t*t%p==x%p)
count=0
for p in [7,11,29,101,415721]:
 for A0 in [1,2,3]:
  for B in [1,2,3]:
   for w in [2,3,4]:
    for v in [1,2]:
     for e,z0 in [(0,1),(0,2),(1,1),(2,1)]:
      A=F(p)*A0;D=A*B
      z=p**e*z0
      r=w*w-A*z*z;r2=w*w-B*v*v
      if vp(r,p)!=0 or vp(r2,p)!=0 or vp(r-r2,p)!=0:continue
      assert vp(D,p)==1
      x,y=D*w*w,D*D*w*z*v
      E=D*r; sec=D*r2;k=E*(E-sec)
      # Standard actual group-law formula, not the proposed simplified ratio.
      X=E+k/(x-E);Y=-k*y/(x-E)**2
      assert Y*Y==X*(X-E)*(X-sec)
      l=-X/Y
      assert l==F(z*v)/(w*(r-r2))
      K=(D/p)*r*(r-r2)
      assert residue((w*w-r)/p,p)==residue(K*l*l,p)
      assert (residue(l,p)==0)==(e>0)
      assert vp(w*w-r,p)==1+2*e
      count+=1
# All twelve rational nonzero root classes are already distinct:
# one exact XVI prime suffices to witness it.
row=ix[415721]
scale=row['scales_mod_p2']
rho=[-F(1,2),F(-1),F(1,2399),-F(32,407)]
classes=[residue(r/c**2,415721) for c in scale for r in rho]
assert len(set(classes))==12 and all(classes)
out=[]
for p,is_old_a in [(415721,True),(9807649,False)]:
    m=p*p;c=ix[p]['scales_mod_p2'][1]
    s=-32*pow(407*c*c,-1,m)%m
    t=pow(2399*c*c,-1,m)
    if is_old_a:
        # Actual OLD p_a w^2 cell; local representative a/p=1, b=s−t mod p.
        w=ix[p]['r_over_d_mod_p2']
        r,r2=s,t
        B=(s-t)%p
        kap=((w*w-r)%m)//p
        assert (w*w-r)%p==0 and pow(B,(p-1)//2,p)==p-1
    else:
        # Pilot-only same-scale b phase, not the old different-scale cell.
        r,r2=t,s;B=1
        w0=sqrt(r,p)
        w=w0+p*(((r+p-w0*w0)//p)*pow(2*w0,-1,p)%p)
        kap=1
    V=sqrt((r-r2)*pow(B,-1,p),p)
    Z=sqrt(kap,p)
    lam=Z*V*pow(w*(r-r2),-1,p)%p
    K=B*r*(r-r2)%p
    assert K*lam*lam%p==kap
    out.append({'prime':p,'actual_old_pa_cell':is_old_a,
                'unit_model_other_factor':B,
                'w_mod_p2':w,'r_mod_p2':r,'r_other_mod_p2':r2,
                'stripped_contact':kap,'K_and_one_additive_test': [K,lam]})
print(json.dumps({'exact_rational_grouplaw_controls':count,'distinct_12_root_residues_at_pa':classes,
                  'actual_pa_and_pilot_only_pb_unit_tests':out},indent=2))
